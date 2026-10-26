import V185TrunkScan23Chunk0919

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5444970 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 6]
def baseStart_5444970 : Nat := 118140960795 + 5444970 * 2 ^ 59
def prefixEnd_5444970 : Nat := 4983230072969 + 3 ^ 40 * 5444970 * 2
def baseEnd_5444970 : Nat := 310654084367962973726005

theorem tailTrace_5444970 : CollatzResearch.WordTrace tailWord_5444970 prefixEnd_5444970 310654084367962973726005 := by
  unfold tailWord_5444970
  simp only [CollatzResearch.WordTrace]
  refine ⟨49648592770952772921463091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132396247389207394457234909 49648592770952772921463091)
  ·
    refine ⟨74472889156429159382194637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49648592770952772921463091 74472889156429159382194637)
    ·
      refine ⟨27927333433660934768322989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74472889156429159382194637 27927333433660934768322989)
      ·
        refine ⟨10472750037622850538121121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27927333433660934768322989 10472750037622850538121121)
        ·
          refine ⟨7854562528217137903590841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10472750037622850538121121 7854562528217137903590841)
          ·
            refine ⟨5890921896162853427693131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7854562528217137903590841 5890921896162853427693131)
            ·
              refine ⟨8836382844244280141539697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890921896162853427693131 8836382844244280141539697)
              ·
                refine ⟨6627287133183210106154773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8836382844244280141539697 6627287133183210106154773)
                ·
                  refine ⟨310654084367962973726005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6627287133183210106154773 310654084367962973726005)
                  ·
                    rfl

theorem cell23_5444970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_5444970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5444970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5444970 prefixEnd_5444970 := by exact prefixLift 5444970
  have htrace : WordTrace (prefixWord ++ tailWord_5444970) baseStart_5444970 baseEnd_5444970 := by
    simpa [prefixWord, tailWord_5444970, baseEnd_5444970] using wordTrace_append hprefix tailTrace_5444970
  have hstable : (prefixWord ++ tailWord_5444970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5444970).length < 2 ^ (prefixWord ++ tailWord_5444970).sum := by decide
  have hdescent : baseEnd_5444970 < baseStart_5444970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5444970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445003 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 4]
def baseStart_5445003 : Nat := 118140960795 + 5445003 * 2 ^ 59
def prefixEnd_5445003 : Nat := 4983230072969 + 3 ^ 40 * 5445003 * 2
def baseEnd_5445003 : Nat := 2795903704173265134421393

theorem tailTrace_5445003 : CollatzResearch.WordTrace tailWord_5445003 prefixEnd_5445003 2795903704173265134421393 := by
  unfold tailWord_5445003
  simp only [CollatzResearch.WordTrace]
  refine ⟨198595574692691538321803663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132397049795127692214535775 198595574692691538321803663)
  ·
    refine ⟨297893362039037307482705495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198595574692691538321803663 297893362039037307482705495)
    ·
      refine ⟨446840043058555961224058243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297893362039037307482705495 446840043058555961224058243)
      ·
        refine ⟨670260064587833941836087365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446840043058555961224058243 670260064587833941836087365)
        ·
          refine ⟨125673762110218864094266381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 670260064587833941836087365 125673762110218864094266381)
          ·
            refine ⟨47127660791332074035349893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125673762110218864094266381 47127660791332074035349893)
            ·
              refine ⟨8836436398374763881628105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47127660791332074035349893 8836436398374763881628105)
              ·
                refine ⟨6627327298781072911221079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8836436398374763881628105 6627327298781072911221079)
                ·
                  refine ⟨9940990948171609366831619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6627327298781072911221079 9940990948171609366831619)
                  ·
                    refine ⟨14911486422257414050247429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9940990948171609366831619 14911486422257414050247429)
                    ·
                      refine ⟨2795903704173265134421393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14911486422257414050247429 2795903704173265134421393)
                      ·
                        rfl

theorem cell23_5445003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 4].length) (baseStart_5445003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445003 prefixEnd_5445003 := by exact prefixLift 5445003
  have htrace : WordTrace (prefixWord ++ tailWord_5445003) baseStart_5445003 baseEnd_5445003 := by
    simpa [prefixWord, tailWord_5445003, baseEnd_5445003] using wordTrace_append hprefix tailTrace_5445003
  have hstable : (prefixWord ++ tailWord_5445003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445003).length < 2 ^ (prefixWord ++ tailWord_5445003).sum := by decide
  have hdescent : baseEnd_5445003 < baseStart_5445003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445009 : List Nat := [1, 2, 2, 1, 1, 1, 2, 13]
def baseStart_5445009 : Nat := 118140960795 + 5445009 * 2 ^ 59
def prefixEnd_5445009 : Nat := 4983230072969 + 3 ^ 40 * 5445009 * 2
def baseEnd_5445009 : Nat := 103552103150266374479495

theorem tailTrace_5445009 : CollatzResearch.WordTrace tailWord_5445009 prefixEnd_5445009 103552103150266374479495 := by
  unfold tailWord_5445009
  simp only [CollatzResearch.WordTrace]
  refine ⟨198595793530669801346522081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132397195687113200897681387 198595793530669801346522081)
  ·
    refine ⟨148946845148002351009891561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198595793530669801346522081 148946845148002351009891561)
    ·
      refine ⟨111710133861001763257418671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148946845148002351009891561 111710133861001763257418671)
      ·
        refine ⟨167565200791502644886128007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111710133861001763257418671 167565200791502644886128007)
        ·
          refine ⟨251347801187253967329192011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167565200791502644886128007 251347801187253967329192011)
          ·
            refine ⟨377021701780880950993788017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251347801187253967329192011 377021701780880950993788017)
            ·
              refine ⟨282766276335660713245341013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377021701780880950993788017 282766276335660713245341013)
              ·
                refine ⟨103552103150266374479495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 282766276335660713245341013 103552103150266374479495)
                ·
                  rfl

theorem cell23_5445009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 13].length) (baseStart_5445009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445009 prefixEnd_5445009 := by exact prefixLift 5445009
  have htrace : WordTrace (prefixWord ++ tailWord_5445009) baseStart_5445009 baseEnd_5445009 := by
    simpa [prefixWord, tailWord_5445009, baseEnd_5445009] using wordTrace_append hprefix tailTrace_5445009
  have hstable : (prefixWord ++ tailWord_5445009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445009).length < 2 ^ (prefixWord ++ tailWord_5445009).sum := by decide
  have hdescent : baseEnd_5445009 < baseStart_5445009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445019 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 7]
def baseStart_5445019 : Nat := 118140960795 + 5445019 * 2 ^ 59
def prefixEnd_5445019 : Nat := 4983230072969 + 3 ^ 40 * 5445019 * 2
def baseEnd_5445019 : Nat := 2795911919863737071821319

theorem tailTrace_5445019 : CollatzResearch.WordTrace tailWord_5445019 prefixEnd_5445019 2795911919863737071821319 := by
  unfold tailWord_5445019
  simp only [CollatzResearch.WordTrace]
  refine ⟨198596158260633573054386111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132397438840422382036257407 198596158260633573054386111)
  ·
    refine ⟨297894237390950359581579167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198596158260633573054386111 297894237390950359581579167)
    ·
      refine ⟨446841356086425539372368751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297894237390950359581579167 446841356086425539372368751)
      ·
        refine ⟨670262034129638309058553127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446841356086425539372368751 670262034129638309058553127)
        ·
          refine ⟨1005393051194457463587829691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670262034129638309058553127 1005393051194457463587829691)
          ·
            refine ⟨1508089576791686195381744537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005393051194457463587829691 1508089576791686195381744537)
            ·
              refine ⟨1131067182593764646536308403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508089576791686195381744537 1131067182593764646536308403)
              ·
                refine ⟨1696600773890646969804462605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131067182593764646536308403 1696600773890646969804462605)
                ·
                  refine ⟨636225290208992613676673477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1696600773890646969804462605 636225290208992613676673477)
                  ·
                    refine ⟨119292241914186115064376277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 636225290208992613676673477 119292241914186115064376277)
                    ·
                      refine ⟨2795911919863737071821319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119292241914186115064376277 2795911919863737071821319)
                      ·
                        rfl

theorem cell23_5445019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_5445019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445019 prefixEnd_5445019 := by exact prefixLift 5445019
  have htrace : WordTrace (prefixWord ++ tailWord_5445019) baseStart_5445019 baseEnd_5445019 := by
    simpa [prefixWord, tailWord_5445019, baseEnd_5445019] using wordTrace_append hprefix tailTrace_5445019
  have hstable : (prefixWord ++ tailWord_5445019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445019).length < 2 ^ (prefixWord ++ tailWord_5445019).sum := by decide
  have hdescent : baseEnd_5445019 < baseStart_5445019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445023 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 5]
def baseStart_5445023 : Nat := 118140960795 + 5445023 * 2 ^ 59
def prefixEnd_5445023 : Nat := 4983230072969 + 3 ^ 40 * 5445023 * 2
def baseEnd_5445023 : Nat := 2795913973786355056171301

theorem tailTrace_5445023 : CollatzResearch.WordTrace tailWord_5445023 prefixEnd_5445023 2795913973786355056171301 := by
  unfold tailWord_5445023
  simp only [CollatzResearch.WordTrace]
  refine ⟨198596304152619081737531723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132397536101746054491687815 198596304152619081737531723)
  ·
    refine ⟨297894456228928622606297585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198596304152619081737531723 297894456228928622606297585)
    ·
      refine ⟨223420842171696466954723189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297894456228928622606297585 223420842171696466954723189)
      ·
        refine ⟨20945703953596543777005299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223420842171696466954723189 20945703953596543777005299)
        ·
          refine ⟨31418555930394815665507949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20945703953596543777005299 31418555930394815665507949)
          ·
            refine ⟨11781958473898055874565481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31418555930394815665507949 11781958473898055874565481)
            ·
              refine ⟨8836468855423541905924111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11781958473898055874565481 8836468855423541905924111)
              ·
                refine ⟨13254703283135312858886167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8836468855423541905924111 13254703283135312858886167)
                ·
                  refine ⟨19882054924702969288329251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13254703283135312858886167 19882054924702969288329251)
                  ·
                    refine ⟨29823082387054453932493877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19882054924702969288329251 29823082387054453932493877)
                    ·
                      refine ⟨2795913973786355056171301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29823082387054453932493877 2795913973786355056171301)
                      ·
                        rfl

theorem cell23_5445023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_5445023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445023 prefixEnd_5445023 := by exact prefixLift 5445023
  have htrace : WordTrace (prefixWord ++ tailWord_5445023) baseStart_5445023 baseEnd_5445023 := by
    simpa [prefixWord, tailWord_5445023, baseEnd_5445023] using wordTrace_append hprefix tailTrace_5445023
  have hstable : (prefixWord ++ tailWord_5445023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445023).length < 2 ^ (prefixWord ++ tailWord_5445023).sum := by decide
  have hdescent : baseEnd_5445023 < baseStart_5445023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445026 : List Nat := [3, 3, 1, 2, 1, 2, 11]
def baseStart_5445026 : Nat := 118140960795 + 5445026 * 2 ^ 59
def prefixEnd_5445026 : Nat := 4983230072969 + 3 ^ 40 * 5445026 * 2
def baseEnd_5445026 : Nat := 34517475484300228943627

theorem tailTrace_5445026 : CollatzResearch.WordTrace tailWord_5445026 prefixEnd_5445026 34517475484300228943627 := by
  unfold tailWord_5445026
  simp only [CollatzResearch.WordTrace]
  refine ⟨49649103392902053312472733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132397609047738808833260621 49649103392902053312472733)
  ·
    refine ⟨18618413772338269992177275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49649103392902053312472733 18618413772338269992177275)
    ·
      refine ⟨27927620658507404988265913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18618413772338269992177275 27927620658507404988265913)
      ·
        refine ⟨20945715493880553741199435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27927620658507404988265913 20945715493880553741199435)
        ·
          refine ⟨31418573240820830611799153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20945715493880553741199435 31418573240820830611799153)
          ·
            refine ⟨23563929930615622958849365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31418573240820830611799153 23563929930615622958849365)
            ·
              refine ⟨34517475484300228943627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23563929930615622958849365 34517475484300228943627)
              ·
                rfl

theorem cell23_5445026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 11].length) (baseStart_5445026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445026 prefixEnd_5445026 := by exact prefixLift 5445026
  have htrace : WordTrace (prefixWord ++ tailWord_5445026) baseStart_5445026 baseEnd_5445026 := by
    simpa [prefixWord, tailWord_5445026, baseEnd_5445026] using wordTrace_append hprefix tailTrace_5445026
  have hstable : (prefixWord ++ tailWord_5445026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445026).length < 2 ^ (prefixWord ++ tailWord_5445026).sum := by decide
  have hdescent : baseEnd_5445026 < baseStart_5445026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445053 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_5445053 : Nat := 118140960795 + 5445053 * 2 ^ 59
def prefixEnd_5445053 : Nat := 4983230072969 + 3 ^ 40 * 5445053 * 2
def baseEnd_5445053 : Nat := 2795929378205989938796163

theorem tailTrace_5445053 : CollatzResearch.WordTrace tailWord_5445053 prefixEnd_5445053 2795929378205989938796163 := by
  unfold tailWord_5445053
  simp only [CollatzResearch.WordTrace]
  refine ⟨198597398342510396861123813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132398265561673597907415875 198597398342510396861123813)
  ·
    refine ⟨37237012189220699411460715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198597398342510396861123813 37237012189220699411460715)
    ·
      refine ⟨55855518283831049117191073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37237012189220699411460715 55855518283831049117191073)
      ·
        refine ⟨41891638712873286837893305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55855518283831049117191073 41891638712873286837893305)
        ·
          refine ⟨31418729034654965128419979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41891638712873286837893305 31418729034654965128419979)
          ·
            refine ⟨47128093551982447692629969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31418729034654965128419979 47128093551982447692629969)
            ·
              refine ⟨35346070163986835769472477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47128093551982447692629969 35346070163986835769472477)
              ·
                refine ⟨13254776311495063413552179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35346070163986835769472477 13254776311495063413552179)
                ·
                  refine ⟨19882164467242595120328269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13254776311495063413552179 19882164467242595120328269)
                  ·
                    refine ⟨7455811675215973170123101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19882164467242595120328269 7455811675215973170123101)
                    ·
                      refine ⟨2795929378205989938796163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7455811675215973170123101 2795929378205989938796163)
                      ·
                        rfl

theorem cell23_5445053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_5445053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445053 prefixEnd_5445053 := by exact prefixLift 5445053
  have htrace : WordTrace (prefixWord ++ tailWord_5445053) baseStart_5445053 baseEnd_5445053 := by
    simpa [prefixWord, tailWord_5445053, baseEnd_5445053] using wordTrace_append hprefix tailTrace_5445053
  have hstable : (prefixWord ++ tailWord_5445053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445053).length < 2 ^ (prefixWord ++ tailWord_5445053).sum := by decide
  have hdescent : baseEnd_5445053 < baseStart_5445053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445058 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5445058 : Nat := 118140960795 + 5445058 * 2 ^ 59
def prefixEnd_5445058 : Nat := 4983230072969 + 3 ^ 40 * 5445058 * 2
def baseEnd_5445058 : Nat := 2795931945609262419233641

theorem tailTrace_5445058 : CollatzResearch.WordTrace tailWord_5445058 prefixEnd_5445058 2795931945609262419233641 := by
  unfold tailWord_5445058
  simp only [CollatzResearch.WordTrace]
  refine ⟨49649395176873070678763957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132398387138328188476703885 49649395176873070678763957)
  ·
    refine ⟨4654630797831850376134121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49649395176873070678763957 4654630797831850376134121)
    ·
      refine ⟨3490973098373887782100591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4654630797831850376134121 3490973098373887782100591)
      ·
        refine ⟨5236459647560831673150887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3490973098373887782100591 5236459647560831673150887)
        ·
          refine ⟨7854689471341247509726331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5236459647560831673150887 7854689471341247509726331)
          ·
            refine ⟨11782034207011871264589497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7854689471341247509726331 11782034207011871264589497)
            ·
              refine ⟨8836525655258903448442123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11782034207011871264589497 8836525655258903448442123)
              ·
                refine ⟨13254788482888355172663185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8836525655258903448442123 13254788482888355172663185)
                ·
                  refine ⟨9941091362166266379497389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13254788482888355172663185 9941091362166266379497389)
                  ·
                    refine ⟨3727909260812349892311521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9941091362166266379497389 3727909260812349892311521)
                    ·
                      refine ⟨2795931945609262419233641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727909260812349892311521 2795931945609262419233641)
                      ·
                        rfl

theorem cell23_5445058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5445058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445058 prefixEnd_5445058 := by exact prefixLift 5445058
  have htrace : WordTrace (prefixWord ++ tailWord_5445058) baseStart_5445058 baseEnd_5445058 := by
    simpa [prefixWord, tailWord_5445058, baseEnd_5445058] using wordTrace_append hprefix tailTrace_5445058
  have hstable : (prefixWord ++ tailWord_5445058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445058).length < 2 ^ (prefixWord ++ tailWord_5445058).sum := by decide
  have hdescent : baseEnd_5445058 < baseStart_5445058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445080 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 1, 3, 2]
def baseStart_5445080 : Nat := 118140960795 + 5445080 * 2 ^ 59
def prefixEnd_5445080 : Nat := 4983230072969 + 3 ^ 40 * 5445080 * 2
def baseEnd_5445080 : Nat := 2795943242183661333158539

theorem tailTrace_5445080 : CollatzResearch.WordTrace tailWord_5445080 prefixEnd_5445080 2795943242183661333158539 := by
  unfold tailWord_5445080
  simp only [CollatzResearch.WordTrace]
  refine ⟨99299191556706290236178347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132398922075608386981571129 99299191556706290236178347)
  ·
    refine ⟨148948787335059435354267521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99299191556706290236178347 148948787335059435354267521)
    ·
      refine ⟨111711590501294576515700641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148948787335059435354267521 111711590501294576515700641)
      ·
        refine ⟨83783692875970932386775481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111711590501294576515700641 83783692875970932386775481)
        ·
          refine ⟨62837769656978199290081611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83783692875970932386775481 62837769656978199290081611)
          ·
            refine ⟨94256654485467298935122417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62837769656978199290081611 94256654485467298935122417)
            ·
              refine ⟨70692490864100474201341813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94256654485467298935122417 70692490864100474201341813)
              ·
                refine ⟨6627421018509419456375795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70692490864100474201341813 6627421018509419456375795)
                ·
                  refine ⟨9941131527764129184563693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6627421018509419456375795 9941131527764129184563693)
                  ·
                    refine ⟨3727924322911548444211385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9941131527764129184563693 3727924322911548444211385)
                    ·
                      refine ⟨2795943242183661333158539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727924322911548444211385 2795943242183661333158539)
                      ·
                        rfl

theorem cell23_5445080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_5445080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445080 prefixEnd_5445080 := by exact prefixLift 5445080
  have htrace : WordTrace (prefixWord ++ tailWord_5445080) baseStart_5445080 baseEnd_5445080 := by
    simpa [prefixWord, tailWord_5445080, baseEnd_5445080] using wordTrace_append hprefix tailTrace_5445080
  have hstable : (prefixWord ++ tailWord_5445080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445080).length < 2 ^ (prefixWord ++ tailWord_5445080).sum := by decide
  have hdescent : baseEnd_5445080 < baseStart_5445080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445093 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_5445093 : Nat := 118140960795 + 5445093 * 2 ^ 59
def prefixEnd_5445093 : Nat := 4983230072969 + 3 ^ 40 * 5445093 * 2
def baseEnd_5445093 : Nat := 2795949917432169782295979

theorem tailTrace_5445093 : CollatzResearch.WordTrace tailWord_5445093 prefixEnd_5445093 2795949917432169782295979 := by
  unfold tailWord_5445093
  simp only [CollatzResearch.WordTrace]
  refine ⟨198598857262365483692579933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132399238174910322461719955 198598857262365483692579933)
  ·
    refine ⟨74474571473387056384717475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198598857262365483692579933 74474571473387056384717475)
    ·
      refine ⟨111711857210080584577076213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74474571473387056384717475 111711857210080584577076213)
      ·
        refine ⟨10472986613445054804100895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111711857210080584577076213 10472986613445054804100895)
        ·
          refine ⟨15709479920167582206151343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10472986613445054804100895 15709479920167582206151343)
          ·
            refine ⟨23564219880251373309227015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15709479920167582206151343 23564219880251373309227015)
            ·
              refine ⟨35346329820377059963840523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23564219880251373309227015 35346329820377059963840523)
              ·
                refine ⟨53019494730565589945760785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35346329820377059963840523 53019494730565589945760785)
                ·
                  refine ⟨39764621047924192459320589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53019494730565589945760785 39764621047924192459320589)
                  ·
                    refine ⟨14911732892971572172245221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39764621047924192459320589 14911732892971572172245221)
                    ·
                      refine ⟨2795949917432169782295979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14911732892971572172245221 2795949917432169782295979)
                      ·
                        rfl

theorem cell23_5445093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_5445093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445093 prefixEnd_5445093 := by exact prefixLift 5445093
  have htrace : WordTrace (prefixWord ++ tailWord_5445093) baseStart_5445093 baseEnd_5445093 := by
    simpa [prefixWord, tailWord_5445093, baseEnd_5445093] using wordTrace_append hprefix tailTrace_5445093
  have hstable : (prefixWord ++ tailWord_5445093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445093).length < 2 ^ (prefixWord ++ tailWord_5445093).sum := by decide
  have hdescent : baseEnd_5445093 < baseStart_5445093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445116 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 9]
def baseStart_5445116 : Nat := 118140960795 + 5445116 * 2 ^ 59
def prefixEnd_5445116 : Nat := 4983230072969 + 3 ^ 40 * 5445116 * 2
def baseEnd_5445116 : Nat := 310662414165247021367597

theorem tailTrace_5445116 : CollatzResearch.WordTrace tailWord_5445116 prefixEnd_5445116 310662414165247021367597 := by
  unfold tailWord_5445116
  simp only [CollatzResearch.WordTrace]
  refine ⟨99299848070641079310333601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132399797427521439080444801 99299848070641079310333601)
  ·
    refine ⟨74474886052980809482750201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99299848070641079310333601 74474886052980809482750201)
    ·
      refine ⟨55856164539735607112062651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74474886052980809482750201 55856164539735607112062651)
      ·
        refine ⟨83784246809603410668093977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55856164539735607112062651 83784246809603410668093977)
        ·
          refine ⟨62838185107202558001070483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83784246809603410668093977 62838185107202558001070483)
          ·
            refine ⟨94257277660803837001605725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62838185107202558001070483 94257277660803837001605725)
            ·
              refine ⟨35346479122801438875602147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94257277660803837001605725 35346479122801438875602147)
              ·
                refine ⟨53019718684202158313403221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35346479122801438875602147 53019718684202158313403221)
                ·
                  refine ⟨310662414165247021367597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53019718684202158313403221 310662414165247021367597)
                  ·
                    rfl

theorem cell23_5445116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_5445116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445116 prefixEnd_5445116 := by exact prefixLift 5445116
  have htrace : WordTrace (prefixWord ++ tailWord_5445116) baseStart_5445116 baseEnd_5445116 := by
    simpa [prefixWord, tailWord_5445116, baseEnd_5445116] using wordTrace_append hprefix tailTrace_5445116
  have hstable : (prefixWord ++ tailWord_5445116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445116).length < 2 ^ (prefixWord ++ tailWord_5445116).sum := by decide
  have hdescent : baseEnd_5445116 < baseStart_5445116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445131 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 1, 3, 2]
def baseStart_5445131 : Nat := 118140960795 + 5445131 * 2 ^ 59
def prefixEnd_5445131 : Nat := 4983230072969 + 3 ^ 40 * 5445131 * 2
def baseEnd_5445131 : Nat := 2795969429697040633620805

theorem tailTrace_5445131 : CollatzResearch.WordTrace tailWord_5445131 prefixEnd_5445131 2795969429697040633620805 := by
  unfold tailWord_5445131
  simp only [CollatzResearch.WordTrace]
  refine ⟨198600243236227816182463247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132400162157485210788308831 198600243236227816182463247)
  ·
    refine ⟨297900364854341724273694871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198600243236227816182463247 297900364854341724273694871)
    ·
      refine ⟨446850547281512586410542307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297900364854341724273694871 446850547281512586410542307)
      ·
        refine ⟨670275820922268879615813461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446850547281512586410542307 670275820922268879615813461)
        ·
          refine ⟨3927397388216419216498907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 670275820922268879615813461 3927397388216419216498907)
          ·
            refine ⟨5891096082324628824748361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927397388216419216498907 5891096082324628824748361)
            ·
              refine ⟨4418322061743471618561271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5891096082324628824748361 4418322061743471618561271)
              ·
                refine ⟨6627483092615207427841907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418322061743471618561271 6627483092615207427841907)
                ·
                  refine ⟨9941224638922811141762861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6627483092615207427841907 9941224638922811141762861)
                  ·
                    refine ⟨3727959239596054178161073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9941224638922811141762861 3727959239596054178161073)
                    ·
                      refine ⟨2795969429697040633620805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3727959239596054178161073 2795969429697040633620805)
                      ·
                        rfl

theorem cell23_5445131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 1, 3, 2].length) (baseStart_5445131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445131 prefixEnd_5445131 := by exact prefixLift 5445131
  have htrace : WordTrace (prefixWord ++ tailWord_5445131) baseStart_5445131 baseEnd_5445131 := by
    simpa [prefixWord, tailWord_5445131, baseEnd_5445131] using wordTrace_append hprefix tailTrace_5445131
  have hstable : (prefixWord ++ tailWord_5445131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445131).length < 2 ^ (prefixWord ++ tailWord_5445131).sum := by decide
  have hdescent : baseEnd_5445131 < baseStart_5445131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445183 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_5445183 : Nat := 118140960795 + 5445183 * 2 ^ 59
def prefixEnd_5445183 : Nat := 4983230072969 + 3 ^ 40 * 5445183 * 2
def baseEnd_5445183 : Nat := 2795996130691074430170565

theorem tailTrace_5445183 : CollatzResearch.WordTrace tailWord_5445183 prefixEnd_5445183 2795996130691074430170565 := by
  unfold tailWord_5445183
  simp only [CollatzResearch.WordTrace]
  refine ⟨198602139832039429063356203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132401426554692952708904135 198602139832039429063356203)
  ·
    refine ⟨297903209748059143595034305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198602139832039429063356203 297903209748059143595034305)
    ·
      refine ⟨223427407311044357696275729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297903209748059143595034305 223427407311044357696275729)
      ·
        refine ⟨167570555483283268272206797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223427407311044357696275729 167570555483283268272206797)
        ·
          refine ⟨62838958306231225602077549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167570555483283268272206797 62838958306231225602077549)
          ·
            refine ⟨23564609364836709600779081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62838958306231225602077549 23564609364836709600779081)
            ·
              refine ⟨17673457023627532200584311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23564609364836709600779081 17673457023627532200584311)
              ·
                refine ⟨26510185535441298300876467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17673457023627532200584311 26510185535441298300876467)
                ·
                  refine ⟨39765278303161947451314701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26510185535441298300876467 39765278303161947451314701)
                  ·
                    refine ⟨14911979363685730294243013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39765278303161947451314701 14911979363685730294243013)
                    ·
                      refine ⟨2795996130691074430170565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14911979363685730294243013 2795996130691074430170565)
                      ·
                        rfl

theorem cell23_5445183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_5445183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445183 prefixEnd_5445183 := by exact prefixLift 5445183
  have htrace : WordTrace (prefixWord ++ tailWord_5445183) baseStart_5445183 baseEnd_5445183 := by
    simpa [prefixWord, tailWord_5445183, baseEnd_5445183] using wordTrace_append hprefix tailTrace_5445183
  have hstable : (prefixWord ++ tailWord_5445183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445183).length < 2 ^ (prefixWord ++ tailWord_5445183).sum := by decide
  have hdescent : baseEnd_5445183 < baseStart_5445183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445193 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 5, 4]
def baseStart_5445193 : Nat := 118140960795 + 5445193 * 2 ^ 59
def prefixEnd_5445193 : Nat := 4983230072969 + 3 ^ 40 * 5445193 * 2
def baseEnd_5445193 : Nat := 932000421832539797015173

theorem tailTrace_5445193 : CollatzResearch.WordTrace tailWord_5445193 prefixEnd_5445193 932000421832539797015173 := by
  unfold tailWord_5445193
  simp only [CollatzResearch.WordTrace]
  refine ⟨198602504562003200771220233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132401669708002133847480155 198602504562003200771220233)
  ·
    refine ⟨148951878421502400578415175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198602504562003200771220233 148951878421502400578415175)
    ·
      refine ⟨223427817632253600867622763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148951878421502400578415175 223427817632253600867622763)
      ·
        refine ⟨335141726448380401301434145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223427817632253600867622763 335141726448380401301434145)
        ·
          refine ⟨251356294836285300976075609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335141726448380401301434145 251356294836285300976075609)
          ·
            refine ⟨188517221127213975732056707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251356294836285300976075609 188517221127213975732056707)
            ·
              refine ⟨282775831690820963598085061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188517221127213975732056707 282775831690820963598085061)
              ·
                refine ⟨53020468442028930674640949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282775831690820963598085061 53020468442028930674640949)
                ·
                  refine ⟨4970668916440212250747589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53020468442028930674640949 4970668916440212250747589)
                  ·
                    refine ⟨932000421832539797015173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4970668916440212250747589 932000421832539797015173)
                    ·
                      rfl

theorem cell23_5445193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 5, 4].length) (baseStart_5445193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445193 prefixEnd_5445193 := by exact prefixLift 5445193
  have htrace : WordTrace (prefixWord ++ tailWord_5445193) baseStart_5445193 baseEnd_5445193 := by
    simpa [prefixWord, tailWord_5445193, baseEnd_5445193] using wordTrace_append hprefix tailTrace_5445193
  have hstable : (prefixWord ++ tailWord_5445193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445193).length < 2 ^ (prefixWord ++ tailWord_5445193).sum := by decide
  have hdescent : baseEnd_5445193 < baseStart_5445193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445197 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_5445197 : Nat := 118140960795 + 5445197 * 2 ^ 59
def prefixEnd_5445197 : Nat := 4983230072969 + 3 ^ 40 * 5445197 * 2
def baseEnd_5445197 : Nat := 932001106473412458465167

theorem tailTrace_5445197 : CollatzResearch.WordTrace tailWord_5445197 prefixEnd_5445197 932001106473412458465167 := by
  unfold tailWord_5445197
  simp only [CollatzResearch.WordTrace]
  refine ⟨198602650453988709454365845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132401766969325806302910563 198602650453988709454365845)
  ·
    refine ⟨9309499240030720755673399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198602650453988709454365845 9309499240030720755673399)
    ·
      refine ⟨13964248860046081133510099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9309499240030720755673399 13964248860046081133510099)
      ·
        refine ⟨20946373290069121700265149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13964248860046081133510099 20946373290069121700265149)
        ·
          refine ⟨7854889983775920637599431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20946373290069121700265149 7854889983775920637599431)
          ·
            refine ⟨11782334975663880956399147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7854889983775920637599431 11782334975663880956399147)
            ·
              refine ⟨17673502463495821434598721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11782334975663880956399147 17673502463495821434598721)
              ·
                refine ⟨13255126847621866075949041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17673502463495821434598721 13255126847621866075949041)
                ·
                  refine ⟨9941345135716399556961781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13255126847621866075949041 9941345135716399556961781)
                  ·
                    refine ⟨932001106473412458465167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9941345135716399556961781 932001106473412458465167)
                    ·
                      rfl

theorem cell23_5445197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_5445197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445197 prefixEnd_5445197 := by exact prefixLift 5445197
  have htrace : WordTrace (prefixWord ++ tailWord_5445197) baseStart_5445197 baseEnd_5445197 := by
    simpa [prefixWord, tailWord_5445197, baseEnd_5445197] using wordTrace_append hprefix tailTrace_5445197
  have hstable : (prefixWord ++ tailWord_5445197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445197).length < 2 ^ (prefixWord ++ tailWord_5445197).sum := by decide
  have hdescent : baseEnd_5445197 < baseStart_5445197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445233 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_5445233 : Nat := 118140960795 + 5445233 * 2 ^ 59
def prefixEnd_5445233 : Nat := 4983230072969 + 3 ^ 40 * 5445233 * 2
def baseEnd_5445233 : Nat := 2796021804723799234545335

theorem tailTrace_5445233 : CollatzResearch.WordTrace tailWord_5445233 prefixEnd_5445233 2796021804723799234545335 := by
  unfold tailWord_5445233
  simp only [CollatzResearch.WordTrace]
  refine ⟨198603963481858287602676353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132402642321238858401784235 198603963481858287602676353)
  ·
    refine ⟨148952972611393715702007265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198603963481858287602676353 148952972611393715702007265)
    ·
      refine ⟨111714729458545286776505449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148952972611393715702007265 111714729458545286776505449)
      ·
        refine ⟨83786047093908965082379087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111714729458545286776505449 83786047093908965082379087)
        ·
          refine ⟨125679070640863447623568631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83786047093908965082379087 125679070640863447623568631)
          ·
            refine ⟨188518605961295171435352947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125679070640863447623568631 188518605961295171435352947)
            ·
              refine ⟨282777908941942757153029421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188518605961295171435352947 282777908941942757153029421)
              ·
                refine ⟨106041715853228533932386033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282777908941942757153029421 106041715853228533932386033)
                ·
                  refine ⟨79531286889921400449289525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106041715853228533932386033 79531286889921400449289525)
                  ·
                    refine ⟨7456058145930131292120893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79531286889921400449289525 7456058145930131292120893)
                    ·
                      refine ⟨2796021804723799234545335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7456058145930131292120893 2796021804723799234545335)
                      ·
                        rfl

theorem cell23_5445233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_5445233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445233 prefixEnd_5445233 := by exact prefixLift 5445233
  have htrace : WordTrace (prefixWord ++ tailWord_5445233) baseStart_5445233 baseEnd_5445233 := by
    simpa [prefixWord, tailWord_5445233, baseEnd_5445233] using wordTrace_append hprefix tailTrace_5445233
  have hstable : (prefixWord ++ tailWord_5445233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445233).length < 2 ^ (prefixWord ++ tailWord_5445233).sum := by decide
  have hdescent : baseEnd_5445233 < baseStart_5445233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445237 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5445237 : Nat := 118140960795 + 5445237 * 2 ^ 59
def prefixEnd_5445237 : Nat := 4983230072969 + 3 ^ 40 * 5445237 * 2
def baseEnd_5445237 : Nat := 2796023858646417218895317

theorem tailTrace_5445237 : CollatzResearch.WordTrace tailWord_5445237 prefixEnd_5445237 2796023858646417218895317 := by
  unfold tailWord_5445237
  simp only [CollatzResearch.WordTrace]
  refine ⟨198604109373843796285821965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132402739582562530857214643 198604109373843796285821965)
  ·
    refine ⟨74476541015191423607183237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198604109373843796285821965 74476541015191423607183237)
    ·
      refine ⟨13964351440348391926346857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74476541015191423607183237 13964351440348391926346857)
      ·
        refine ⟨10473263580261293944760143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13964351440348391926346857 10473263580261293944760143)
        ·
          refine ⟨15709895370391940917140215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10473263580261293944760143 15709895370391940917140215)
          ·
            refine ⟨23564843055587911375710323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15709895370391940917140215 23564843055587911375710323)
            ·
              refine ⟨35347264583381867063565485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23564843055587911375710323 35347264583381867063565485)
              ·
                refine ⟨13255224218768200148837057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35347264583381867063565485 13255224218768200148837057)
                ·
                  refine ⟨9941418164076150111627793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13255224218768200148837057 9941418164076150111627793)
                  ·
                    refine ⟨7456063623057112583720845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9941418164076150111627793 7456063623057112583720845)
                    ·
                      refine ⟨2796023858646417218895317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7456063623057112583720845 2796023858646417218895317)
                      ·
                        rfl

theorem cell23_5445237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5445237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445237 prefixEnd_5445237 := by exact prefixLift 5445237
  have htrace : WordTrace (prefixWord ++ tailWord_5445237) baseStart_5445237 baseEnd_5445237 := by
    simpa [prefixWord, tailWord_5445237, baseEnd_5445237] using wordTrace_append hprefix tailTrace_5445237
  have hstable : (prefixWord ++ tailWord_5445237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445237).length < 2 ^ (prefixWord ++ tailWord_5445237).sum := by decide
  have hdescent : baseEnd_5445237 < baseStart_5445237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445288 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5445288 : Nat := 118140960795 + 5445288 * 2 ^ 59
def prefixEnd_5445288 : Nat := 4983230072969 + 3 ^ 40 * 5445288 * 2
def baseEnd_5445288 : Nat := 2796050046159796519357583

theorem tailTrace_5445288 : CollatzResearch.WordTrace tailWord_5445288 prefixEnd_5445288 2796050046159796519357583 := by
  unfold tailWord_5445288
  simp only [CollatzResearch.WordTrace]
  refine ⟨99302984748329515997964259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132403979664439354663952345 99302984748329515997964259)
  ·
    refine ⟨148954477122494273996946389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99302984748329515997964259 148954477122494273996946389)
    ·
      refine ⟨3491120557558459546803431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 148954477122494273996946389 3491120557558459546803431)
      ·
        refine ⟨5236680836337689320205147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3491120557558459546803431 5236680836337689320205147)
        ·
          refine ⟨7855021254506533980307721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5236680836337689320205147 7855021254506533980307721)
          ·
            refine ⟨5891265940879900485230791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7855021254506533980307721 5891265940879900485230791)
            ·
              refine ⟨8836898911319850727846187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891265940879900485230791 8836898911319850727846187)
              ·
                refine ⟨13255348366979776091769281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8836898911319850727846187 13255348366979776091769281)
                ·
                  refine ⟨9941511275234832068826961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13255348366979776091769281 9941511275234832068826961)
                  ·
                    refine ⟨7456133456426124051620221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9941511275234832068826961 7456133456426124051620221)
                    ·
                      refine ⟨2796050046159796519357583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7456133456426124051620221 2796050046159796519357583)
                      ·
                        rfl

theorem cell23_5445288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5445288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445288 prefixEnd_5445288 := by exact prefixLift 5445288
  have htrace : WordTrace (prefixWord ++ tailWord_5445288) baseStart_5445288 baseEnd_5445288 := by
    simpa [prefixWord, tailWord_5445288, baseEnd_5445288] using wordTrace_append hprefix tailTrace_5445288
  have hstable : (prefixWord ++ tailWord_5445288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445288).length < 2 ^ (prefixWord ++ tailWord_5445288).sum := by decide
  have hdescent : baseEnd_5445288 < baseStart_5445288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445318 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_5445318 : Nat := 118140960795 + 5445318 * 2 ^ 59
def prefixEnd_5445318 : Nat := 4983230072969 + 3 ^ 40 * 5445318 * 2
def baseEnd_5445318 : Nat := 2796065450579431401982445

theorem tailTrace_5445318 : CollatzResearch.WordTrace tailWord_5445318 prefixEnd_5445318 2796065450579431401982445 := by
  unfold tailWord_5445318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6206470740204698347485019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132404709124366898079680405 6206470740204698347485019)
  ·
    refine ⟨9309706110307047521227529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6206470740204698347485019 9309706110307047521227529)
    ·
      refine ⟨6982279582730285640920647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9309706110307047521227529 6982279582730285640920647)
      ·
        refine ⟨10473419374095428461380971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982279582730285640920647 10473419374095428461380971)
        ·
          refine ⟨15710129061143142692071457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10473419374095428461380971 15710129061143142692071457)
          ·
            refine ⟨11782596795857357019053593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15710129061143142692071457 11782596795857357019053593)
            ·
              refine ⟨8836947596893017764290195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11782596795857357019053593 8836947596893017764290195)
              ·
                refine ⟨13255421395339526646435293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8836947596893017764290195 13255421395339526646435293)
                ·
                  refine ⟨4970783023252322492413235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13255421395339526646435293 4970783023252322492413235)
                  ·
                    refine ⟨7456174534878483738619853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4970783023252322492413235 7456174534878483738619853)
                    ·
                      refine ⟨2796065450579431401982445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7456174534878483738619853 2796065450579431401982445)
                      ·
                        rfl

theorem cell23_5445318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_5445318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445318 prefixEnd_5445318 := by exact prefixLift 5445318
  have htrace : WordTrace (prefixWord ++ tailWord_5445318) baseStart_5445318 baseEnd_5445318 := by
    simpa [prefixWord, tailWord_5445318, baseEnd_5445318] using wordTrace_append hprefix tailTrace_5445318
  have hstable : (prefixWord ++ tailWord_5445318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445318).length < 2 ^ (prefixWord ++ tailWord_5445318).sum := by decide
  have hdescent : baseEnd_5445318 < baseStart_5445318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445337 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 4]
def baseStart_5445337 : Nat := 118140960795 + 5445337 * 2 ^ 59
def prefixEnd_5445337 : Nat := 4983230072969 + 3 ^ 40 * 5445337 * 2
def baseEnd_5445337 : Nat := 2796075206711866827644857

theorem tailTrace_5445337 : CollatzResearch.WordTrace tailWord_5445337 prefixEnd_5445337 2796075206711866827644857 := by
  unfold tailWord_5445337
  simp only [CollatzResearch.WordTrace]
  refine ⟨198607756673481513364462265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132405171115654342242974843 198607756673481513364462265)
  ·
    refine ⟨148955817505111135023346699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198607756673481513364462265 148955817505111135023346699)
    ·
      refine ⟨223433726257666702535020049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148955817505111135023346699 223433726257666702535020049)
      ·
        refine ⟨167575294693250026901265037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223433726257666702535020049 167575294693250026901265037)
        ·
          refine ⟨62840735509968760087974389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167575294693250026901265037 62840735509968760087974389)
          ·
            refine ⟨5891318954059571258247599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62840735509968760087974389 5891318954059571258247599)
            ·
              refine ⟨8836978431089356887371399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891318954059571258247599 8836978431089356887371399)
              ·
                refine ⟨13255467646634035331057099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8836978431089356887371399 13255467646634035331057099)
                ·
                  refine ⟨19883201469951052996585649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13255467646634035331057099 19883201469951052996585649)
                  ·
                    refine ⟨14912401102463289747439237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19883201469951052996585649 14912401102463289747439237)
                    ·
                      refine ⟨2796075206711866827644857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14912401102463289747439237 2796075206711866827644857)
                      ·
                        rfl

theorem cell23_5445337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_5445337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445337 prefixEnd_5445337 := by exact prefixLift 5445337
  have htrace : WordTrace (prefixWord ++ tailWord_5445337) baseStart_5445337 baseEnd_5445337 := by
    simpa [prefixWord, tailWord_5445337, baseEnd_5445337] using wordTrace_append hprefix tailTrace_5445337
  have hstable : (prefixWord ++ tailWord_5445337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445337).length < 2 ^ (prefixWord ++ tailWord_5445337).sum := by decide
  have hdescent : baseEnd_5445337 < baseStart_5445337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445341 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5445341 : Nat := 118140960795 + 5445341 * 2 ^ 59
def prefixEnd_5445341 : Nat := 4983230072969 + 3 ^ 40 * 5445341 * 2
def baseEnd_5445341 : Nat := 2796077260634484811994839

theorem tailTrace_5445341 : CollatzResearch.WordTrace tailWord_5445341 prefixEnd_5445341 2796077260634484811994839 := by
  unfold tailWord_5445341
  simp only [CollatzResearch.WordTrace]
  refine ⟨198607902565467022047607877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132405268376978014698405251 198607902565467022047607877)
  ·
    refine ⟨37238981731025066633926477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198607902565467022047607877 37238981731025066633926477)
    ·
      refine ⟨13964618149134399987722429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37238981731025066633926477 13964618149134399987722429)
      ·
        refine ⟨5236731805925399995395911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13964618149134399987722429 5236731805925399995395911)
        ·
          refine ⟨7855097708888099993093867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5236731805925399995395911 7855097708888099993093867)
          ·
            refine ⟨11782646563332149989640801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7855097708888099993093867 11782646563332149989640801)
            ·
              refine ⟨8836984922499112492230601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11782646563332149989640801 8836984922499112492230601)
              ·
                refine ⟨6627738691874334369172951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8836984922499112492230601 6627738691874334369172951)
                ·
                  refine ⟨9941608037811501553759427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6627738691874334369172951 9941608037811501553759427)
                  ·
                    refine ⟨14912412056717252330639141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9941608037811501553759427 14912412056717252330639141)
                    ·
                      refine ⟨2796077260634484811994839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14912412056717252330639141 2796077260634484811994839)
                      ·
                        rfl

theorem cell23_5445341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5445341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445341 prefixEnd_5445341 := by exact prefixLift 5445341
  have htrace : WordTrace (prefixWord ++ tailWord_5445341) baseStart_5445341 baseEnd_5445341 := by
    simpa [prefixWord, tailWord_5445341, baseEnd_5445341] using wordTrace_append hprefix tailTrace_5445341
  have hstable : (prefixWord ++ tailWord_5445341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445341).length < 2 ^ (prefixWord ++ tailWord_5445341).sum := by decide
  have hdescent : baseEnd_5445341 < baseStart_5445341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445364 : List Nat := [2, 6, 1, 1, 1, 3, 9]
def baseStart_5445364 : Nat := 118140960795 + 5445364 * 2 ^ 59
def prefixEnd_5445364 : Nat := 4983230072969 + 3 ^ 40 * 5445364 * 2
def baseEnd_5445364 : Nat := 34519618156660965703793

theorem tailTrace_5445364 : CollatzResearch.WordTrace tailWord_5445364 prefixEnd_5445364 34519618156660965703793 := by
  unfold tailWord_5445364
  simp only [CollatzResearch.WordTrace]
  refine ⟨99304370722191848487847573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132405827629589131317130097 99304370722191848487847573)
  ·
    refine ⟨4654892377602742897867855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99304370722191848487847573 4654892377602742897867855)
    ·
      refine ⟨6982338566404114346801783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4654892377602742897867855 6982338566404114346801783)
      ·
        refine ⟨10473507849606171520202675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982338566404114346801783 10473507849606171520202675)
        ·
          refine ⟨15710261774409257280304013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10473507849606171520202675 15710261774409257280304013)
          ·
            refine ⟨5891348165403471480114005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15710261774409257280304013 5891348165403471480114005)
            ·
              refine ⟨34519618156660965703793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5891348165403471480114005 34519618156660965703793)
              ·
                rfl

theorem cell23_5445364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 9].length) (baseStart_5445364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445364 prefixEnd_5445364 := by exact prefixLift 5445364
  have htrace : WordTrace (prefixWord ++ tailWord_5445364) baseStart_5445364 baseEnd_5445364 := by
    simpa [prefixWord, tailWord_5445364, baseEnd_5445364] using wordTrace_append hprefix tailTrace_5445364
  have hstable : (prefixWord ++ tailWord_5445364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445364).length < 2 ^ (prefixWord ++ tailWord_5445364).sum := by decide
  have hdescent : baseEnd_5445364 < baseStart_5445364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445390 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_5445390 : Nat := 118140960795 + 5445390 * 2 ^ 59
def prefixEnd_5445390 : Nat := 4983230072969 + 3 ^ 40 * 5445390 * 2
def baseEnd_5445390 : Nat := 932034140395518373427371

theorem tailTrace_5445390 : CollatzResearch.WordTrace tailWord_5445390 prefixEnd_5445390 932034140395518373427371 := by
  unfold tailWord_5445390
  simp only [CollatzResearch.WordTrace]
  refine ⟨24826211217786187927017703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132406459828193002277427749 24826211217786187927017703)
  ·
    refine ⟨37239316826679281890526555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24826211217786187927017703 37239316826679281890526555)
    ·
      refine ⟨55858975240018922835789833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37239316826679281890526555 55858975240018922835789833)
      ·
        refine ⟨41894231430014192126842375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55858975240018922835789833 41894231430014192126842375)
        ·
          refine ⟨62841347145021288190263563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41894231430014192126842375 62841347145021288190263563)
          ·
            refine ⟨94262020717531932285395345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62841347145021288190263563 94262020717531932285395345)
            ·
              refine ⟨70696515538148949214046509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94262020717531932285395345 70696515538148949214046509)
              ·
                refine ⟨26511193326805855955267441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70696515538148949214046509 26511193326805855955267441)
                ·
                  refine ⟨19883394995104391966450581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26511193326805855955267441 19883394995104391966450581)
                  ·
                    refine ⟨932034140395518373427371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19883394995104391966450581 932034140395518373427371)
                    ·
                      rfl

theorem cell23_5445390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_5445390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445390 prefixEnd_5445390 := by exact prefixLift 5445390
  have htrace : WordTrace (prefixWord ++ tailWord_5445390) baseStart_5445390 baseEnd_5445390 := by
    simpa [prefixWord, tailWord_5445390, baseEnd_5445390] using wordTrace_append hprefix tailTrace_5445390
  have hstable : (prefixWord ++ tailWord_5445390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445390).length < 2 ^ (prefixWord ++ tailWord_5445390).sum := by decide
  have hdescent : baseEnd_5445390 < baseStart_5445390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445400 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5445400 : Nat := 118140960795 + 5445400 * 2 ^ 59
def prefixEnd_5445400 : Nat := 4983230072969 + 3 ^ 40 * 5445400 * 2
def baseEnd_5445400 : Nat := 2796107555993100081157067

theorem tailTrace_5445400 : CollatzResearch.WordTrace tailWord_5445400 prefixEnd_5445400 2796107555993100081157067 := by
  unfold tailWord_5445400
  simp only [CollatzResearch.WordTrace]
  refine ⟨99305027236126637562002827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132406702981502183416003769 99305027236126637562002827)
  ·
    refine ⟨148957540854189956343004241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99305027236126637562002827 148957540854189956343004241)
    ·
      refine ⟨111718155640642467257253181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148957540854189956343004241 111718155640642467257253181)
      ·
        refine ⟨41894308365240925221469943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111718155640642467257253181 41894308365240925221469943)
        ·
          refine ⟨62841462547861387832204915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41894308365240925221469943 62841462547861387832204915)
          ·
            refine ⟨94262193821792081748307373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62841462547861387832204915 94262193821792081748307373)
            ·
              refine ⟨35348322683172030655615265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94262193821792081748307373 35348322683172030655615265)
              ·
                refine ⟨26511242012379022991711449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35348322683172030655615265 26511242012379022991711449)
                ·
                  refine ⟨19883431509284267243783587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26511242012379022991711449 19883431509284267243783587)
                  ·
                    refine ⟨29825147263926400865675381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19883431509284267243783587 29825147263926400865675381)
                    ·
                      refine ⟨2796107555993100081157067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29825147263926400865675381 2796107555993100081157067)
                      ·
                        rfl

theorem cell23_5445400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5445400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445400 prefixEnd_5445400 := by exact prefixLift 5445400
  have htrace : WordTrace (prefixWord ++ tailWord_5445400) baseStart_5445400 baseEnd_5445400 := by
    simpa [prefixWord, tailWord_5445400, baseEnd_5445400] using wordTrace_append hprefix tailTrace_5445400
  have hstable : (prefixWord ++ tailWord_5445400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445400).length < 2 ^ (prefixWord ++ tailWord_5445400).sum := by decide
  have hdescent : baseEnd_5445400 < baseStart_5445400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445450 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_5445450 : Nat := 118140960795 + 5445450 * 2 ^ 59
def prefixEnd_5445450 : Nat := 4983230072969 + 3 ^ 40 * 5445450 * 2
def baseEnd_5445450 : Nat := 932044410008608295177279

theorem tailTrace_5445450 : CollatzResearch.WordTrace tailWord_5445450 prefixEnd_5445450 932044410008608295177279 := by
  unfold tailWord_5445450
  simp only [CollatzResearch.WordTrace]
  refine ⟨49652969530518033415831451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132407918748048089108883869 49652969530518033415831451)
  ·
    refine ⟨74479454295777050123747177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49652969530518033415831451 74479454295777050123747177)
    ·
      refine ⟨55859590721832787592810383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74479454295777050123747177 55859590721832787592810383)
      ·
        refine ⟨83789386082749181389215575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55859590721832787592810383 83789386082749181389215575)
        ·
          refine ⟨125684079124123772083823363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83789386082749181389215575 125684079124123772083823363)
          ·
            refine ⟨188526118686185658125735045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125684079124123772083823363 188526118686185658125735045)
            ·
              refine ⟨35348647253659810898575321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188526118686185658125735045 35348647253659810898575321)
              ·
                refine ⟨26511485440244858173931491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35348647253659810898575321 26511485440244858173931491)
                ·
                  refine ⟨39767228160367287260897237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26511485440244858173931491 39767228160367287260897237)
                  ·
                    refine ⟨932044410008608295177279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39767228160367287260897237 932044410008608295177279)
                    ·
                      rfl

theorem cell23_5445450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_5445450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445450 prefixEnd_5445450 := by exact prefixLift 5445450
  have htrace : WordTrace (prefixWord ++ tailWord_5445450) baseStart_5445450 baseEnd_5445450 := by
    simpa [prefixWord, tailWord_5445450, baseEnd_5445450] using wordTrace_append hprefix tailTrace_5445450
  have hstable : (prefixWord ++ tailWord_5445450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445450).length < 2 ^ (prefixWord ++ tailWord_5445450).sum := by decide
  have hdescent : baseEnd_5445450 < baseStart_5445450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445482 : List Nat := [3, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_5445482 : Nat := 118140960795 + 5445482 * 2 ^ 59
def prefixEnd_5445482 : Nat := 4983230072969 + 3 ^ 40 * 5445482 * 2
def baseEnd_5445482 : Nat := 2796149661406768760331691

theorem tailTrace_5445482 : CollatzResearch.WordTrace tailWord_5445482 prefixEnd_5445482 2796149661406768760331691 := by
  unfold tailWord_5445482
  simp only [CollatzResearch.WordTrace]
  refine ⟨49653261314489050782122675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132408696838637468752327133 49653261314489050782122675)
  ·
    refine ⟨74479891971733576173184013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49653261314489050782122675 74479891971733576173184013)
    ·
      refine ⟨27929959489400091064944005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74479891971733576173184013 27929959489400091064944005)
      ·
        refine ⟨5236867404262517074677001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27929959489400091064944005 5236867404262517074677001)
        ·
          refine ⟨3927650553196887806007751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5236867404262517074677001 3927650553196887806007751)
          ·
            refine ⟨5891475829795331709011627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927650553196887806007751 5891475829795331709011627)
            ·
              refine ⟨8837213744692997563517441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891475829795331709011627 8837213744692997563517441)
              ·
                refine ⟨6627910308519748172638081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8837213744692997563517441 6627910308519748172638081)
                ·
                  refine ⟨4970932731389811129478561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6627910308519748172638081 4970932731389811129478561)
                  ·
                    refine ⟨3728199548542358347108921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4970932731389811129478561 3728199548542358347108921)
                    ·
                      refine ⟨2796149661406768760331691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3728199548542358347108921 2796149661406768760331691)
                      ·
                        rfl

theorem cell23_5445482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_5445482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445482 prefixEnd_5445482 := by exact prefixLift 5445482
  have htrace : WordTrace (prefixWord ++ tailWord_5445482) baseStart_5445482 baseEnd_5445482 := by
    simpa [prefixWord, tailWord_5445482, baseEnd_5445482] using wordTrace_append hprefix tailTrace_5445482
  have hstable : (prefixWord ++ tailWord_5445482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445482).length < 2 ^ (prefixWord ++ tailWord_5445482).sum := by decide
  have hdescent : baseEnd_5445482 < baseStart_5445482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445507 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 3]
def baseStart_5445507 : Nat := 118140960795 + 5445507 * 2 ^ 59
def prefixEnd_5445507 : Nat := 4983230072969 + 3 ^ 40 * 5445507 * 2
def baseEnd_5445507 : Nat := 2796162498423131162519075

theorem tailTrace_5445507 : CollatzResearch.WordTrace tailWord_5445507 prefixEnd_5445507 2796162498423131162519075 := by
  unfold tailWord_5445507
  simp only [CollatzResearch.WordTrace]
  refine ⟨198613957082865632398150775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132409304721910421598767183 198613957082865632398150775)
  ·
    refine ⟨297920935624298448597226163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198613957082865632398150775 297920935624298448597226163)
    ·
      refine ⟨446881403436447672895839245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297920935624298448597226163 446881403436447672895839245)
      ·
        refine ⟨167580526288667877335939717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446881403436447672895839245 167580526288667877335939717)
        ·
          refine ⟨31421348679125227000488697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167580526288667877335939717 31421348679125227000488697)
          ·
            refine ⟨23566011509343920250366523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31421348679125227000488697 23566011509343920250366523)
            ·
              refine ⟨35349017264015880375549785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23566011509343920250366523 35349017264015880375549785)
              ·
                refine ⟨26511762948011910281662339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35349017264015880375549785 26511762948011910281662339)
                ·
                  refine ⟨39767644422017865422493509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26511762948011910281662339 39767644422017865422493509)
                  ·
                    refine ⟨7456433329128349766717533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39767644422017865422493509 7456433329128349766717533)
                    ·
                      refine ⟨2796162498423131162519075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7456433329128349766717533 2796162498423131162519075)
                      ·
                        rfl

theorem cell23_5445507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_5445507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445507 prefixEnd_5445507 := by exact prefixLift 5445507
  have htrace : WordTrace (prefixWord ++ tailWord_5445507) baseStart_5445507 baseEnd_5445507 := by
    simpa [prefixWord, tailWord_5445507, baseEnd_5445507] using wordTrace_append hprefix tailTrace_5445507
  have hstable : (prefixWord ++ tailWord_5445507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445507).length < 2 ^ (prefixWord ++ tailWord_5445507).sum := by decide
  have hdescent : baseEnd_5445507 < baseStart_5445507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445524 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_5445524 : Nat := 118140960795 + 5445524 * 2 ^ 59
def prefixEnd_5445524 : Nat := 4983230072969 + 3 ^ 40 * 5445524 * 2
def baseEnd_5445524 : Nat := 2796171227594257596006497

theorem tailTrace_5445524 : CollatzResearch.WordTrace tailWord_5445524 prefixEnd_5445524 2796171227594257596006497 := by
  unfold tailWord_5445524
  simp only [CollatzResearch.WordTrace]
  refine ⟨99307288561902022150759813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132409718082536029534346417 99307288561902022150759813)
  ·
    refine ⟨18620116605356629153267465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99307288561902022150759813 18620116605356629153267465)
    ·
      refine ⟨13965087454017471864950599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18620116605356629153267465 13965087454017471864950599)
      ·
        refine ⟨20947631181026207797425899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13965087454017471864950599 20947631181026207797425899)
        ·
          refine ⟨31421446771539311696138849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20947631181026207797425899 31421446771539311696138849)
          ·
            refine ⟨23566085078654483772104137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31421446771539311696138849 23566085078654483772104137)
            ·
              refine ⟨17674563808990862829078103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23566085078654483772104137 17674563808990862829078103)
              ·
                refine ⟨26511845713486294243617155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17674563808990862829078103 26511845713486294243617155)
                ·
                  refine ⟨39767768570229441365425733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26511845713486294243617155 39767768570229441365425733)
                  ·
                    refine ⟨7456456606918020256017325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39767768570229441365425733 7456456606918020256017325)
                    ·
                      refine ⟨2796171227594257596006497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7456456606918020256017325 2796171227594257596006497)
                      ·
                        rfl

theorem cell23_5445524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_5445524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445524 prefixEnd_5445524 := by exact prefixLift 5445524
  have htrace : WordTrace (prefixWord ++ tailWord_5445524) baseStart_5445524 baseEnd_5445524 := by
    simpa [prefixWord, tailWord_5445524, baseEnd_5445524] using wordTrace_append hprefix tailTrace_5445524
  have hstable : (prefixWord ++ tailWord_5445524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445524).length < 2 ^ (prefixWord ++ tailWord_5445524).sum := by decide
  have hdescent : baseEnd_5445524 < baseStart_5445524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445577 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 4]
def baseStart_5445577 : Nat := 118140960795 + 5445577 * 2 ^ 59
def prefixEnd_5445577 : Nat := 4983230072969 + 3 ^ 40 * 5445577 * 2
def baseEnd_5445577 : Nat := 2796198442068945888643753

theorem tailTrace_5445577 : CollatzResearch.WordTrace tailWord_5445577 prefixEnd_5445577 2796198442068945888643753 := by
  unfold tailWord_5445577
  simp only [CollatzResearch.WordTrace]
  refine ⟨198616510192612034353198985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132411006795074689568799323 198616510192612034353198985)
  ·
    refine ⟨148962382644459025764899239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198616510192612034353198985 148962382644459025764899239)
    ·
      refine ⟨223443573966688538647348859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148962382644459025764899239 223443573966688538647348859)
      ·
        refine ⟨335165360950032807971023289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223443573966688538647348859 335165360950032807971023289)
        ·
          refine ⟨251374020712524605978267467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335165360950032807971023289 251374020712524605978267467)
          ·
            refine ⟨377061031068786908967401201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251374020712524605978267467 377061031068786908967401201)
            ·
              refine ⟨282795773301590181725550901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377061031068786908967401201 282795773301590181725550901)
              ·
                refine ⟨26512103747024079536770397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282795773301590181725550901 26512103747024079536770397)
                ·
                  refine ⟨9942038905134029826288899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26512103747024079536770397 9942038905134029826288899)
                  ·
                    refine ⟨14913058357701044739433349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9942038905134029826288899 14913058357701044739433349)
                    ·
                      refine ⟨2796198442068945888643753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14913058357701044739433349 2796198442068945888643753)
                      ·
                        rfl

theorem cell23_5445577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_5445577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445577 prefixEnd_5445577 := by exact prefixLift 5445577
  have htrace : WordTrace (prefixWord ++ tailWord_5445577) baseStart_5445577 baseEnd_5445577 := by
    simpa [prefixWord, tailWord_5445577, baseEnd_5445577] using wordTrace_append hprefix tailTrace_5445577
  have hstable : (prefixWord ++ tailWord_5445577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445577).length < 2 ^ (prefixWord ++ tailWord_5445577).sum := by decide
  have hdescent : baseEnd_5445577 < baseStart_5445577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445588 : List Nat := [2, 4, 1, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_5445588 : Nat := 118140960795 + 5445588 * 2 ^ 59
def prefixEnd_5445588 : Nat := 4983230072969 + 3 ^ 40 * 5445588 * 2
def baseEnd_5445588 : Nat := 2796204090356145345606203

theorem tailTrace_5445588 : CollatzResearch.WordTrace tailWord_5445588 prefixEnd_5445588 2796204090356145345606203 := by
  unfold tailWord_5445588
  simp only [CollatzResearch.WordTrace]
  refine ⟨99308455697786091615924709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132411274263714788821232945 99308455697786091615924709)
  ·
    refine ⟨18620335443334892177985883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99308455697786091615924709 18620335443334892177985883)
    ·
      refine ⟨27930503165002338266978825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18620335443334892177985883 27930503165002338266978825)
      ·
        refine ⟨20947877373751753700234119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27930503165002338266978825 20947877373751753700234119)
        ·
          refine ⟨31421816060627630550351179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20947877373751753700234119 31421816060627630550351179)
          ·
            refine ⟨47132724090941445825526769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31421816060627630550351179 47132724090941445825526769)
            ·
              refine ⟨35349543068206084369145077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47132724090941445825526769 35349543068206084369145077)
              ·
                refine ⟨3314019662644320409607351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35349543068206084369145077 3314019662644320409607351)
                ·
                  refine ⟨4971029493966480614411027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314019662644320409607351 4971029493966480614411027)
                  ·
                    refine ⟨7456544240949720921616541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4971029493966480614411027 7456544240949720921616541)
                    ·
                      refine ⟨2796204090356145345606203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7456544240949720921616541 2796204090356145345606203)
                      ·
                        rfl

theorem cell23_5445588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_5445588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445588 prefixEnd_5445588 := by exact prefixLift 5445588
  have htrace : WordTrace (prefixWord ++ tailWord_5445588) baseStart_5445588 baseEnd_5445588 := by
    simpa [prefixWord, tailWord_5445588, baseEnd_5445588] using wordTrace_append hprefix tailTrace_5445588
  have hstable : (prefixWord ++ tailWord_5445588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445588).length < 2 ^ (prefixWord ++ tailWord_5445588).sum := by decide
  have hdescent : baseEnd_5445588 < baseStart_5445588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445644 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_5445644 : Nat := 118140960795 + 5445644 * 2 ^ 59
def prefixEnd_5445644 : Nat := 4983230072969 + 3 ^ 40 * 5445644 * 2
def baseEnd_5445644 : Nat := 2796232845272797126505945

theorem tailTrace_5445644 : CollatzResearch.WordTrace tailWord_5445644 prefixEnd_5445644 2796232845272797126505945 := by
  unfold tailWord_5445644
  simp only [CollatzResearch.WordTrace]
  refine ⟨99309476941684652397943993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132412635922246203197258657 99309476941684652397943993)
  ·
    refine ⟨74482107706263489298457995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99309476941684652397943993 74482107706263489298457995)
    ·
      refine ⟨111723161559395233947686993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74482107706263489298457995 111723161559395233947686993)
      ·
        refine ⟨83792371169546425460765245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111723161559395233947686993 83792371169546425460765245)
        ·
          refine ⟨31422139188579909547786967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83792371169546425460765245 31422139188579909547786967)
          ·
            refine ⟨47133208782869864321680451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31422139188579909547786967 47133208782869864321680451)
            ·
              refine ⟨70699813174304796482520677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47133208782869864321680451 70699813174304796482520677)
              ·
                refine ⟨13256214970182149340472627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70699813174304796482520677 13256214970182149340472627)
                ·
                  refine ⟨19884322455273224010708941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13256214970182149340472627 19884322455273224010708941)
                  ·
                    refine ⟨7456620920727459004015853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19884322455273224010708941 7456620920727459004015853)
                    ·
                      refine ⟨2796232845272797126505945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7456620920727459004015853 2796232845272797126505945)
                      ·
                        rfl

theorem cell23_5445644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_5445644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445644 prefixEnd_5445644 := by exact prefixLift 5445644
  have htrace : WordTrace (prefixWord ++ tailWord_5445644) baseStart_5445644 baseEnd_5445644 := by
    simpa [prefixWord, tailWord_5445644, baseEnd_5445644] using wordTrace_append hprefix tailTrace_5445644
  have hstable : (prefixWord ++ tailWord_5445644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445644).length < 2 ^ (prefixWord ++ tailWord_5445644).sum := by decide
  have hdescent : baseEnd_5445644 < baseStart_5445644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445655 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 2, 4]
def baseStart_5445655 : Nat := 118140960795 + 5445655 * 2 ^ 59
def prefixEnd_5445655 : Nat := 4983230072969 + 3 ^ 40 * 5445655 * 2
def baseEnd_5445655 : Nat := 932079497853332194489465

theorem tailTrace_5445655 : CollatzResearch.WordTrace tailWord_5445655 prefixEnd_5445655 932079497853332194489465 := by
  unfold tailWord_5445655
  simp only [CollatzResearch.WordTrace]
  refine ⟨198619355086329453674538419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132412903390886302449692279 198619355086329453674538419)
  ·
    refine ⟨297929032629494180511807629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198619355086329453674538419 297929032629494180511807629)
    ·
      refine ⟨111723387236060317691927861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297929032629494180511807629 111723387236060317691927861)
      ·
        refine ⟨10474067553380654783618237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111723387236060317691927861 10474067553380654783618237)
        ·
          refine ⟨3927775332517745543856839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10474067553380654783618237 3927775332517745543856839)
          ·
            refine ⟨5891662998776618315785259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927775332517745543856839 5891662998776618315785259)
            ·
              refine ⟨8837494498164927473677889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891662998776618315785259 8837494498164927473677889)
              ·
                refine ⟨6628120873623695605258417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8837494498164927473677889 6628120873623695605258417)
                ·
                  refine ⟨4971090655217771703943813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6628120873623695605258417 4971090655217771703943813)
                  ·
                    refine ⟨932079497853332194489465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4971090655217771703943813 932079497853332194489465)
                    ·
                      rfl

theorem cell23_5445655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_5445655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445655 prefixEnd_5445655 := by exact prefixLift 5445655
  have htrace : WordTrace (prefixWord ++ tailWord_5445655) baseStart_5445655 baseEnd_5445655 := by
    simpa [prefixWord, tailWord_5445655, baseEnd_5445655] using wordTrace_append hprefix tailTrace_5445655
  have hstable : (prefixWord ++ tailWord_5445655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445655).length < 2 ^ (prefixWord ++ tailWord_5445655).sum := by decide
  have hdescent : baseEnd_5445655 < baseStart_5445655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445678 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_5445678 : Nat := 118140960795 + 5445678 * 2 ^ 59
def prefixEnd_5445678 : Nat := 4983230072969 + 3 ^ 40 * 5445678 * 2
def baseEnd_5445678 : Nat := 2796250303615049993480789

theorem tailTrace_5445678 : CollatzResearch.WordTrace tailWord_5445678 prefixEnd_5445678 2796250303615049993480789 := by
  unfold tailWord_5445678
  simp only [CollatzResearch.WordTrace]
  refine ⟨24827524245655766075328211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132413462643497419068417125 24827524245655766075328211)
  ·
    refine ⟨37241286368483649112992317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24827524245655766075328211 37241286368483649112992317)
    ·
      refine ⟨13965482388181368417372119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37241286368483649112992317 13965482388181368417372119)
      ·
        refine ⟨20948223582272052626058179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13965482388181368417372119 20948223582272052626058179)
        ·
          refine ⟨31422335373408078939087269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20948223582272052626058179 31422335373408078939087269)
          ·
            refine ⟨5891687882514014801078863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31422335373408078939087269 5891687882514014801078863)
            ·
              refine ⟨8837531823771022201618295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891687882514014801078863 8837531823771022201618295)
              ·
                refine ⟨13256297735656533302427443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8837531823771022201618295 13256297735656533302427443)
                ·
                  refine ⟨19884446603484799953641165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13256297735656533302427443 19884446603484799953641165)
                  ·
                    refine ⟨7456667476306799982615437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19884446603484799953641165 7456667476306799982615437)
                    ·
                      refine ⟨2796250303615049993480789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7456667476306799982615437 2796250303615049993480789)
                      ·
                        rfl

theorem cell23_5445678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_5445678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445678 prefixEnd_5445678 := by exact prefixLift 5445678
  have htrace : WordTrace (prefixWord ++ tailWord_5445678) baseStart_5445678 baseEnd_5445678 := by
    simpa [prefixWord, tailWord_5445678, baseEnd_5445678] using wordTrace_append hprefix tailTrace_5445678
  have hstable : (prefixWord ++ tailWord_5445678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445678).length < 2 ^ (prefixWord ++ tailWord_5445678).sum := by decide
  have hdescent : baseEnd_5445678 < baseStart_5445678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445727 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_5445727 : Nat := 118140960795 + 5445727 * 2 ^ 59
def prefixEnd_5445727 : Nat := 4983230072969 + 3 ^ 40 * 5445727 * 2
def baseEnd_5445727 : Nat := 2796275464167120301768063

theorem tailTrace_5445727 : CollatzResearch.WordTrace tailWord_5445727 prefixEnd_5445727 2796275464167120301768063 := by
  unfold tailWord_5445727
  simp only [CollatzResearch.WordTrace]
  refine ⟨198621981142068609971159435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132414654094712406647439623 198621981142068609971159435)
  ·
    refine ⟨297932971713102914956739153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198621981142068609971159435 297932971713102914956739153)
    ·
      refine ⟨223449728784827186217554365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297932971713102914956739153 223449728784827186217554365)
      ·
        refine ⟨83793648294310194831582887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223449728784827186217554365 83793648294310194831582887)
        ·
          refine ⟨125690472441465292247374331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83793648294310194831582887 125690472441465292247374331)
          ·
            refine ⟨188535708662197938371061497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125690472441465292247374331 188535708662197938371061497)
            ·
              refine ⟨141401781496648453778296123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188535708662197938371061497 141401781496648453778296123)
              ·
                refine ⟨212102672244972680667444185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141401781496648453778296123 212102672244972680667444185)
                ·
                  refine ⟨159077004183729510500583139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212102672244972680667444185 159077004183729510500583139)
                  ·
                    refine ⟨238615506275594265750874709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159077004183729510500583139 238615506275594265750874709)
                    ·
                      refine ⟨2796275464167120301768063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 238615506275594265750874709 2796275464167120301768063)
                      ·
                        rfl

theorem cell23_5445727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_5445727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445727 prefixEnd_5445727 := by exact prefixLift 5445727
  have htrace : WordTrace (prefixWord ++ tailWord_5445727) baseStart_5445727 baseEnd_5445727 := by
    simpa [prefixWord, tailWord_5445727, baseEnd_5445727] using wordTrace_append hprefix tailTrace_5445727
  have hstable : (prefixWord ++ tailWord_5445727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445727).length < 2 ^ (prefixWord ++ tailWord_5445727).sum := by decide
  have hdescent : baseEnd_5445727 < baseStart_5445727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445764 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_5445764 : Nat := 118140960795 + 5445764 * 2 ^ 59
def prefixEnd_5445764 : Nat := 4983230072969 + 3 ^ 40 * 5445764 * 2
def baseEnd_5445764 : Nat := 2796294462951336657005393

theorem tailTrace_5445764 : CollatzResearch.WordTrace tailWord_5445764 prefixEnd_5445764 2796294462951336657005393 := by
  unfold tailWord_5445764
  simp only [CollatzResearch.WordTrace]
  refine ⟨99311665321467282645128173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132415553761956376860170897 99311665321467282645128173)
  ·
    refine ⟨37241874495550230991923065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99311665321467282645128173 37241874495550230991923065)
    ·
      refine ⟨27931405871662673243942299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37241874495550230991923065 27931405871662673243942299)
      ·
        refine ⟨41897108807494009865913449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27931405871662673243942299 41897108807494009865913449)
        ·
          refine ⟨31422831605620507399435087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41897108807494009865913449 31422831605620507399435087)
          ·
            refine ⟨47134247408430761099152631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31422831605620507399435087 47134247408430761099152631)
            ·
              refine ⟨70701371112646141648728947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47134247408430761099152631 70701371112646141648728947)
              ·
                refine ⟨106052056668969212473093421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70701371112646141648728947 106052056668969212473093421)
                ·
                  refine ⟨39769521250863454677410033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106052056668969212473093421 39769521250863454677410033)
                  ·
                    refine ⟨29827140938147591008057525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39769521250863454677410033 29827140938147591008057525)
                    ·
                      refine ⟨2796294462951336657005393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29827140938147591008057525 2796294462951336657005393)
                      ·
                        rfl

theorem cell23_5445764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_5445764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445764 prefixEnd_5445764 := by exact prefixLift 5445764
  have htrace : WordTrace (prefixWord ++ tailWord_5445764) baseStart_5445764 baseEnd_5445764 := by
    simpa [prefixWord, tailWord_5445764, baseEnd_5445764] using wordTrace_append hprefix tailTrace_5445764
  have hstable : (prefixWord ++ tailWord_5445764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445764).length < 2 ^ (prefixWord ++ tailWord_5445764).sum := by decide
  have hdescent : baseEnd_5445764 < baseStart_5445764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445818 : List Nat := [3, 1, 1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_5445818 : Nat := 118140960795 + 5445818 * 2 ^ 59
def prefixEnd_5445818 : Nat := 4983230072969 + 3 ^ 40 * 5445818 * 2
def baseEnd_5445818 : Nat := 932107396968893148576715

theorem tailTrace_5445818 : CollatzResearch.WordTrace tailWord_5445818 prefixEnd_5445818 932107396968893148576715 := by
  unfold tailWord_5445818
  simp only [CollatzResearch.WordTrace]
  refine ⟨49656325046184733128180527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132416866789825955008481405 49656325046184733128180527)
  ·
    refine ⟨74484487569277099692270791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49656325046184733128180527 74484487569277099692270791)
    ·
      refine ⟨111726731353915649538406187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74484487569277099692270791 111726731353915649538406187)
      ·
        refine ⟨167590097030873474307609281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111726731353915649538406187 167590097030873474307609281)
        ·
          refine ⟨125692572773155105730706961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167590097030873474307609281 125692572773155105730706961)
          ·
            refine ⟨94269429579866329298030221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125692572773155105730706961 94269429579866329298030221)
            ·
              refine ⟨35351036092449873486761333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94269429579866329298030221 35351036092449873486761333)
              ·
                refine ⟨3314159633667175639383875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35351036092449873486761333 3314159633667175639383875)
                ·
                  refine ⟨4971239450500763459075813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314159633667175639383875 4971239450500763459075813)
                  ·
                    refine ⟨932107396968893148576715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4971239450500763459075813 932107396968893148576715)
                    ·
                      rfl

theorem cell23_5445818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_5445818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445818 prefixEnd_5445818 := by exact prefixLift 5445818
  have htrace : WordTrace (prefixWord ++ tailWord_5445818) baseStart_5445818 baseEnd_5445818 := by
    simpa [prefixWord, tailWord_5445818, baseEnd_5445818] using wordTrace_append hprefix tailTrace_5445818
  have hstable : (prefixWord ++ tailWord_5445818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445818).length < 2 ^ (prefixWord ++ tailWord_5445818).sum := by decide
  have hdescent : baseEnd_5445818 < baseStart_5445818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445834 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_5445834 : Nat := 118140960795 + 5445834 * 2 ^ 59
def prefixEnd_5445834 : Nat := 4983230072969 + 3 ^ 40 * 5445834 * 2
def baseEnd_5445834 : Nat := 2796330406597151383130071

theorem tailTrace_5445834 : CollatzResearch.WordTrace tailWord_5445834 prefixEnd_5445834 2796330406597151383130071 := by
  unfold tailWord_5445834
  simp only [CollatzResearch.WordTrace]
  refine ⟨49656470938170241811326139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132417255835120644830203037 49656470938170241811326139)
  ·
    refine ⟨74484706407255362716989209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49656470938170241811326139 74484706407255362716989209)
    ·
      refine ⟨55863529805441522037741907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74484706407255362716989209 55863529805441522037741907)
      ·
        refine ⟨83795294708162283056612861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55863529805441522037741907 83795294708162283056612861)
        ·
          refine ⟨31423235515560856146229823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83795294708162283056612861 31423235515560856146229823)
          ·
            refine ⟨47134853273341284219344735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31423235515560856146229823 47134853273341284219344735)
            ·
              refine ⟨70702279910011926329017103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47134853273341284219344735 70702279910011926329017103)
              ·
                refine ⟨106053419865017889493525655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70702279910011926329017103 106053419865017889493525655)
                ·
                  refine ⟨159080129797526834240288483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106053419865017889493525655 159080129797526834240288483)
                  ·
                    refine ⟨238620194696290251360432725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159080129797526834240288483 238620194696290251360432725)
                    ·
                      refine ⟨2796330406597151383130071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 238620194696290251360432725 2796330406597151383130071)
                      ·
                        rfl

theorem cell23_5445834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_5445834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445834 prefixEnd_5445834 := by exact prefixLift 5445834
  have htrace : WordTrace (prefixWord ++ tailWord_5445834) baseStart_5445834 baseEnd_5445834 := by
    simpa [prefixWord, tailWord_5445834, baseEnd_5445834] using wordTrace_append hprefix tailTrace_5445834
  have hstable : (prefixWord ++ tailWord_5445834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445834).length < 2 ^ (prefixWord ++ tailWord_5445834).sum := by decide
  have hdescent : baseEnd_5445834 < baseStart_5445834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445848 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 6]
def baseStart_5445848 : Nat := 118140960795 + 5445848 * 2 ^ 59
def prefixEnd_5445848 : Nat := 4983230072969 + 3 ^ 40 * 5445848 * 2
def baseEnd_5445848 : Nat := 310704177258479369817223

theorem tailTrace_5445848 : CollatzResearch.WordTrace tailWord_5445848 prefixEnd_5445848 310704177258479369817223 := by
  unfold tailWord_5445848
  simp only [CollatzResearch.WordTrace]
  refine ⟨99313197187315123818157099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132417596249753498424209465 99313197187315123818157099)
  ·
    refine ⟨148969795780972685727235649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99313197187315123818157099 148969795780972685727235649)
    ·
      refine ⟨111727346835729514295426737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148969795780972685727235649 111727346835729514295426737)
      ·
        refine ⟨83795510126797135721570053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111727346835729514295426737 83795510126797135721570053)
        ·
          refine ⟨15711658148774462947794385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83795510126797135721570053 15711658148774462947794385)
          ·
            refine ⟨11783743611580847210845789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15711658148774462947794385 11783743611580847210845789)
            ·
              refine ⟨4418903854342817704067171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11783743611580847210845789 4418903854342817704067171)
              ·
                refine ⟨6628355781514226556100757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418903854342817704067171 6628355781514226556100757)
                ·
                  refine ⟨310704177258479369817223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6628355781514226556100757 310704177258479369817223)
                  ·
                    rfl

theorem cell23_5445848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 6].length) (baseStart_5445848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445848 prefixEnd_5445848 := by exact prefixLift 5445848
  have htrace : WordTrace (prefixWord ++ tailWord_5445848) baseStart_5445848 baseEnd_5445848 := by
    simpa [prefixWord, tailWord_5445848, baseEnd_5445848] using wordTrace_append hprefix tailTrace_5445848
  have hstable : (prefixWord ++ tailWord_5445848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445848).length < 2 ^ (prefixWord ++ tailWord_5445848).sum := by decide
  have hdescent : baseEnd_5445848 < baseStart_5445848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445851 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 1, 5, 2]
def baseStart_5445851 : Nat := 118140960795 + 5445851 * 2 ^ 59
def prefixEnd_5445851 : Nat := 4983230072969 + 3 ^ 40 * 5445851 * 2
def baseEnd_5445851 : Nat := 2796339135768277816617493

theorem tailTrace_5445851 : CollatzResearch.WordTrace tailWord_5445851 prefixEnd_5445851 2796339135768277816617493 := by
  unfold tailWord_5445851
  simp only [CollatzResearch.WordTrace]
  refine ⟨198626503793619379148673407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132417669195746252765782271 198626503793619379148673407)
  ·
    refine ⟨297939755690429068723010111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198626503793619379148673407 297939755690429068723010111)
    ·
      refine ⟨446909633535643603084515167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297939755690429068723010111 446909633535643603084515167)
      ·
        refine ⟨670364450303465404626772751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446909633535643603084515167 670364450303465404626772751)
        ·
          refine ⟨1005546675455198106940159127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670364450303465404626772751 1005546675455198106940159127)
          ·
            refine ⟨1508320013182797160410238691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005546675455198106940159127 1508320013182797160410238691)
            ·
              refine ⟨2262480019774195740615358037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508320013182797160410238691 2262480019774195740615358037)
              ·
                refine ⟨26513437731728856335336227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2262480019774195740615358037 26513437731728856335336227)
                ·
                  refine ⟨39770156597593284503004341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26513437731728856335336227 39770156597593284503004341)
                  ·
                    refine ⟨3728452181024370422156657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39770156597593284503004341 3728452181024370422156657)
                    ·
                      refine ⟨2796339135768277816617493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3728452181024370422156657 2796339135768277816617493)
                      ·
                        rfl

theorem cell23_5445851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 5, 2].length) (baseStart_5445851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445851 prefixEnd_5445851 := by exact prefixLift 5445851
  have htrace : WordTrace (prefixWord ++ tailWord_5445851) baseStart_5445851 baseEnd_5445851 := by
    simpa [prefixWord, tailWord_5445851, baseEnd_5445851] using wordTrace_append hprefix tailTrace_5445851
  have hstable : (prefixWord ++ tailWord_5445851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445851).length < 2 ^ (prefixWord ++ tailWord_5445851).sum := by decide
  have hdescent : baseEnd_5445851 < baseStart_5445851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445868 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 2, 3, 2]
def baseStart_5445868 : Nat := 118140960795 + 5445868 * 2 ^ 59
def prefixEnd_5445868 : Nat := 4983230072969 + 3 ^ 40 * 5445868 * 2
def baseEnd_5445868 : Nat := 2796347864939404250104915

theorem tailTrace_5445868 : CollatzResearch.WordTrace tailWord_5445868 prefixEnd_5445868 2796347864939404250104915 := by
  unfold tailWord_5445868
  simp only [CollatzResearch.WordTrace]
  refine ⟨99313561917278895526021129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132418082556371860701361505 99313561917278895526021129)
  ·
    refine ⟨74485171437959171644515847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99313561917278895526021129 74485171437959171644515847)
    ·
      refine ⟨111727757156938757466773771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74485171437959171644515847 111727757156938757466773771)
      ·
        refine ⟨167591635735408136200160657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111727757156938757466773771 167591635735408136200160657)
        ·
          refine ⟨125693726801556102150120493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167591635735408136200160657 125693726801556102150120493)
          ·
            refine ⟨47135147550583538306295185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125693726801556102150120493 47135147550583538306295185)
            ·
              refine ⟨35351360662937653729721389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47135147550583538306295185 35351360662937653729721389)
              ·
                refine ⟨13256760248601620148645521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35351360662937653729721389 13256760248601620148645521)
                ·
                  refine ⟨9942570186451215111484141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13256760248601620148645521 9942570186451215111484141)
                  ·
                    refine ⟨3728463819919205666806553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9942570186451215111484141 3728463819919205666806553)
                    ·
                      refine ⟨2796347864939404250104915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3728463819919205666806553 2796347864939404250104915)
                      ·
                        rfl

theorem cell23_5445868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_5445868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445868 prefixEnd_5445868 := by exact prefixLift 5445868
  have htrace : WordTrace (prefixWord ++ tailWord_5445868) baseStart_5445868 baseEnd_5445868 := by
    simpa [prefixWord, tailWord_5445868, baseEnd_5445868] using wordTrace_append hprefix tailTrace_5445868
  have hstable : (prefixWord ++ tailWord_5445868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445868).length < 2 ^ (prefixWord ++ tailWord_5445868).sum := by decide
  have hdescent : baseEnd_5445868 < baseStart_5445868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445869 : List Nat := [1, 5, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_5445869 : Nat := 118140960795 + 5445869 * 2 ^ 59
def prefixEnd_5445869 : Nat := 4983230072969 + 3 ^ 40 * 5445869 * 2
def baseEnd_5445869 : Nat := 932116126140019582064137

theorem tailTrace_5445869 : CollatzResearch.WordTrace tailWord_5445869 prefixEnd_5445869 932116126140019582064137 := by
  unfold tailWord_5445869
  simp only [CollatzResearch.WordTrace]
  refine ⟨198627160307554168222828661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132418106871702778815219107 198627160307554168222828661)
  ·
    refine ⟨18621296278833203270890187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198627160307554168222828661 18621296278833203270890187)
    ·
      refine ⟨27931944418249804906335281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18621296278833203270890187 27931944418249804906335281)
      ·
        refine ⟨20948958313687353679751461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27931944418249804906335281 20948958313687353679751461)
        ·
          refine ⟨3927929683816378814953399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20948958313687353679751461 3927929683816378814953399)
          ·
            refine ⟨5891894525724568222430099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927929683816378814953399 5891894525724568222430099)
            ·
              refine ⟨8837841788586852333645149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891894525724568222430099 8837841788586852333645149)
              ·
                refine ⟨3314190670720069625116931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8837841788586852333645149 3314190670720069625116931)
                ·
                  refine ⟨4971286006080104437675397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314190670720069625116931 4971286006080104437675397)
                  ·
                    refine ⟨932116126140019582064137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4971286006080104437675397 932116126140019582064137)
                    ·
                      rfl

theorem cell23_5445869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_5445869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445869 prefixEnd_5445869 := by exact prefixLift 5445869
  have htrace : WordTrace (prefixWord ++ tailWord_5445869) baseStart_5445869 baseEnd_5445869 := by
    simpa [prefixWord, tailWord_5445869, baseEnd_5445869] using wordTrace_append hprefix tailTrace_5445869
  have hstable : (prefixWord ++ tailWord_5445869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445869).length < 2 ^ (prefixWord ++ tailWord_5445869).sum := by decide
  have hdescent : baseEnd_5445869 < baseStart_5445869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445878 : List Nat := [5, 1, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_5445878 : Nat := 118140960795 + 5445878 * 2 ^ 59
def prefixEnd_5445878 : Nat := 4983230072969 + 3 ^ 40 * 5445878 * 2
def baseEnd_5445878 : Nat := 932117666581983070326623

theorem tailTrace_5445878 : CollatzResearch.WordTrace tailWord_5445878 prefixEnd_5445878 932117666581983070326623 := by
  unfold tailWord_5445878
  simp only [CollatzResearch.WordTrace]
  refine ⟨12414218035282597672494143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132418325709681041839937525 12414218035282597672494143)
  ·
    refine ⟨18621327052923896508741215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12414218035282597672494143 18621327052923896508741215)
    ·
      refine ⟨27931990579385844763111823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18621327052923896508741215 27931990579385844763111823)
      ·
        refine ⟨41897985869078767144667735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27931990579385844763111823 41897985869078767144667735)
        ·
          refine ⟨62846978803618150717001603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41897985869078767144667735 62846978803618150717001603)
          ·
            refine ⟨94270468205427226075502405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62846978803618150717001603 94270468205427226075502405)
            ·
              refine ⟨17675712788517604889156701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94270468205427226075502405 17675712788517604889156701)
              ·
                refine ⟨6628392295694101833433763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17675712788517604889156701 6628392295694101833433763)
                ·
                  refine ⟨9942588443541152750150645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628392295694101833433763 9942588443541152750150645)
                  ·
                    refine ⟨932117666581983070326623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9942588443541152750150645 932117666581983070326623)
                    ·
                      rfl

theorem cell23_5445878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_5445878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445878 prefixEnd_5445878 := by exact prefixLift 5445878
  have htrace : WordTrace (prefixWord ++ tailWord_5445878) baseStart_5445878 baseEnd_5445878 := by
    simpa [prefixWord, tailWord_5445878, baseEnd_5445878] using wordTrace_append hprefix tailTrace_5445878
  have hstable : (prefixWord ++ tailWord_5445878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445878).length < 2 ^ (prefixWord ++ tailWord_5445878).sum := by decide
  have hdescent : baseEnd_5445878 < baseStart_5445878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445891 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 4, 4]
def baseStart_5445891 : Nat := 118140960795 + 5445891 * 2 ^ 59
def prefixEnd_5445891 : Nat := 4983230072969 + 3 ^ 40 * 5445891 * 2
def baseEnd_5445891 : Nat := 932119891664819220039103

theorem tailTrace_5445891 : CollatzResearch.WordTrace tailWord_5445891 prefixEnd_5445891 932119891664819220039103 := by
  unfold tailWord_5445891
  simp only [CollatzResearch.WordTrace]
  refine ⟨198627962713474465980129527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132418641808982977320086351 198627962713474465980129527)
  ·
    refine ⟨297941944070211698970194291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198627962713474465980129527 297941944070211698970194291)
    ·
      refine ⟨446912916105317548455291437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297941944070211698970194291 446912916105317548455291437)
      ·
        refine ⟨167592343539494080670734289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 446912916105317548455291437 167592343539494080670734289)
        ·
          refine ⟨125694257654620560503050717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167592343539494080670734289 125694257654620560503050717)
          ·
            refine ⟨47135346620482710188644019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125694257654620560503050717 47135346620482710188644019)
            ·
              refine ⟨70703019930724065282966029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47135346620482710188644019 70703019930724065282966029)
              ·
                refine ⟨26513632474021524481112261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70703019930724065282966029 26513632474021524481112261)
                ·
                  refine ⟨4971306088879035840208549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26513632474021524481112261 4971306088879035840208549)
                  ·
                    refine ⟨932119891664819220039103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4971306088879035840208549 932119891664819220039103)
                    ·
                      rfl

theorem cell23_5445891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 4].length) (baseStart_5445891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445891 prefixEnd_5445891 := by exact prefixLift 5445891
  have htrace : WordTrace (prefixWord ++ tailWord_5445891) baseStart_5445891 baseEnd_5445891 := by
    simpa [prefixWord, tailWord_5445891, baseEnd_5445891] using wordTrace_append hprefix tailTrace_5445891
  have hstable : (prefixWord ++ tailWord_5445891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445891).length < 2 ^ (prefixWord ++ tailWord_5445891).sum := by decide
  have hdescent : baseEnd_5445891 < baseStart_5445891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445892 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_5445892 : Nat := 118140960795 + 5445892 * 2 ^ 59
def prefixEnd_5445892 : Nat := 4983230072969 + 3 ^ 40 * 5445892 * 2
def baseEnd_5445892 : Nat := 2796360188475112156204805

theorem tailTrace_5445892 : CollatzResearch.WordTrace tailWord_5445892 prefixEnd_5445892 2796360188475112156204805 := by
  unfold tailWord_5445892
  simp only [CollatzResearch.WordTrace]
  refine ⟨99313999593235421575457965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132418666124313895433943953 99313999593235421575457965)
  ·
    refine ⟨37242749847463283090796737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99313999593235421575457965 37242749847463283090796737)
    ·
      refine ⟨27932062385597462318097553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37242749847463283090796737 27932062385597462318097553)
      ·
        refine ⟨20949046789198096738573165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27932062385597462318097553 20949046789198096738573165)
        ·
          refine ⟨7855892545949286276964937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20949046789198096738573165 7855892545949286276964937)
          ·
            refine ⟨5891919409461964707723703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7855892545949286276964937 5891919409461964707723703)
            ·
              refine ⟨8837879114192947061585555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891919409461964707723703 8837879114192947061585555)
              ·
                refine ⟨13256818671289420592378333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8837879114192947061585555 13256818671289420592378333)
                ·
                  refine ⟨4971307001733532722141875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13256818671289420592378333 4971307001733532722141875)
                  ·
                    refine ⟨7456960502600299083212813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4971307001733532722141875 7456960502600299083212813)
                    ·
                      refine ⟨2796360188475112156204805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7456960502600299083212813 2796360188475112156204805)
                      ·
                        rfl

theorem cell23_5445892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_5445892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445892 prefixEnd_5445892 := by exact prefixLift 5445892
  have htrace : WordTrace (prefixWord ++ tailWord_5445892) baseStart_5445892 baseEnd_5445892 := by
    simpa [prefixWord, tailWord_5445892, baseEnd_5445892] using wordTrace_append hprefix tailTrace_5445892
  have hstable : (prefixWord ++ tailWord_5445892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445892).length < 2 ^ (prefixWord ++ tailWord_5445892).sum := by decide
  have hdescent : baseEnd_5445892 < baseStart_5445892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445911 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_5445911 : Nat := 118140960795 + 5445911 * 2 ^ 59
def prefixEnd_5445911 : Nat := 4983230072969 + 3 ^ 40 * 5445911 * 2
def baseEnd_5445911 : Nat := 2796369944607547581867217

theorem tailTrace_5445911 : CollatzResearch.WordTrace tailWord_5445911 prefixEnd_5445911 2796369944607547581867217 := by
  unfold tailWord_5445911
  simp only [CollatzResearch.WordTrace]
  refine ⟨198628692173402009395857587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132419128115601339597238391 198628692173402009395857587)
  ·
    refine ⟨297943038260103014093786381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198628692173402009395857587 297943038260103014093786381)
    ·
      refine ⟨111728639347538630285169893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297943038260103014093786381 111728639347538630285169893)
      ·
        refine ⟨20949119877663493178469355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111728639347538630285169893 20949119877663493178469355)
        ·
          refine ⟨31423679816495239767704033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20949119877663493178469355 31423679816495239767704033)
          ·
            refine ⟨23567759862371429825778025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31423679816495239767704033 23567759862371429825778025)
            ·
              refine ⟨17675819896778572369333519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23567759862371429825778025 17675819896778572369333519)
              ·
                refine ⟨26513729845167858554000279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17675819896778572369333519 26513729845167858554000279)
                ·
                  refine ⟨39770594767751787831000419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26513729845167858554000279 39770594767751787831000419)
                  ·
                    refine ⟨59655892151627681746500629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39770594767751787831000419 59655892151627681746500629)
                    ·
                      refine ⟨2796369944607547581867217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59655892151627681746500629 2796369944607547581867217)
                      ·
                        rfl

theorem cell23_5445911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_5445911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445911 prefixEnd_5445911 := by exact prefixLift 5445911
  have htrace : WordTrace (prefixWord ++ tailWord_5445911) baseStart_5445911 baseEnd_5445911 := by
    simpa [prefixWord, tailWord_5445911, baseEnd_5445911] using wordTrace_append hprefix tailTrace_5445911
  have hstable : (prefixWord ++ tailWord_5445911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445911).length < 2 ^ (prefixWord ++ tailWord_5445911).sum := by decide
  have hdescent : baseEnd_5445911 < baseStart_5445911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445975 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 1, 3, 2]
def baseStart_5445975 : Nat := 118140960795 + 5445975 * 2 ^ 59
def prefixEnd_5445975 : Nat := 4983230072969 + 3 ^ 40 * 5445975 * 2
def baseEnd_5445975 : Nat := 2796402807369435331466923

theorem tailTrace_5445975 : CollatzResearch.WordTrace tailWord_5445975 prefixEnd_5445975 2796402807369435331466923 := by
  unfold tailWord_5445975
  simp only [CollatzResearch.WordTrace]
  refine ⟨198631026445170148326187379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132420684296780098884124919 198631026445170148326187379)
  ·
    refine ⟨297946539667755222489281069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198631026445170148326187379 297946539667755222489281069)
    ·
      refine ⟨111729952375408208433480401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297946539667755222489281069 111729952375408208433480401)
      ·
        refine ⟨83797464281556156325110301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111729952375408208433480401 83797464281556156325110301)
        ·
          refine ⟨31424049105583558621916363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83797464281556156325110301 31424049105583558621916363)
          ·
            refine ⟨47136073658375337932874545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31424049105583558621916363 47136073658375337932874545)
            ·
              refine ⟨35352055243781503449655909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47136073658375337932874545 35352055243781503449655909)
              ·
                refine ⟨6628510358209031896810483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35352055243781503449655909 6628510358209031896810483)
                ·
                  refine ⟨9942765537313547845215725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628510358209031896810483 9942765537313547845215725)
                  ·
                    refine ⟨3728537076492580441955897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9942765537313547845215725 3728537076492580441955897)
                    ·
                      refine ⟨2796402807369435331466923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3728537076492580441955897 2796402807369435331466923)
                      ·
                        rfl

theorem cell23_5445975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_5445975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445975 prefixEnd_5445975 := by exact prefixLift 5445975
  have htrace : WordTrace (prefixWord ++ tailWord_5445975) baseStart_5445975 baseEnd_5445975 := by
    simpa [prefixWord, tailWord_5445975, baseEnd_5445975] using wordTrace_append hprefix tailTrace_5445975
  have hstable : (prefixWord ++ tailWord_5445975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445975).length < 2 ^ (prefixWord ++ tailWord_5445975).sum := by decide
  have hdescent : baseEnd_5445975 < baseStart_5445975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5445992 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_5445992 : Nat := 118140960795 + 5445992 * 2 ^ 59
def prefixEnd_5445992 : Nat := 4983230072969 + 3 ^ 40 * 5445992 * 2
def baseEnd_5445992 : Nat := 2796411536540561764954345

theorem tailTrace_5445992 : CollatzResearch.WordTrace tailWord_5445992 prefixEnd_5445992 2796411536540561764954345 := by
  unfold tailWord_5445992
  simp only [CollatzResearch.WordTrace]
  refine ⟨99315823243054280114778115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132421097657405706819704153 99315823243054280114778115)
  ·
    refine ⟨148973734864581420172167173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99315823243054280114778115 148973734864581420172167173)
    ·
      refine ⟨27932575287109016282281345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148973734864581420172167173 27932575287109016282281345)
      ·
        refine ⟨20949431465331762211711009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27932575287109016282281345 20949431465331762211711009)
        ·
          refine ⟨15712073598998821658783257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20949431465331762211711009 15712073598998821658783257)
          ·
            refine ⟨11784055199249116244087443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15712073598998821658783257 11784055199249116244087443)
            ·
              refine ⟨17676082798873674366131165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11784055199249116244087443 17676082798873674366131165)
              ·
                refine ⟨6628531049577627887299187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17676082798873674366131165 6628531049577627887299187)
                ·
                  refine ⟨9942796574366441830948781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628531049577627887299187 9942796574366441830948781)
                  ·
                    refine ⟨3728548715387415686605793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9942796574366441830948781 3728548715387415686605793)
                    ·
                      refine ⟨2796411536540561764954345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3728548715387415686605793 2796411536540561764954345)
                      ·
                        rfl

theorem cell23_5445992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_5445992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5445992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5445992 prefixEnd_5445992 := by exact prefixLift 5445992
  have htrace : WordTrace (prefixWord ++ tailWord_5445992) baseStart_5445992 baseEnd_5445992 := by
    simpa [prefixWord, tailWord_5445992, baseEnd_5445992] using wordTrace_append hprefix tailTrace_5445992
  have hstable : (prefixWord ++ tailWord_5445992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5445992).length < 2 ^ (prefixWord ++ tailWord_5445992).sum := by decide
  have hdescent : baseEnd_5445992 < baseStart_5445992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5445992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446011 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 7]
def baseStart_5446011 : Nat := 118140960795 + 5446011 * 2 ^ 59
def prefixEnd_5446011 : Nat := 4983230072969 + 3 ^ 40 * 5446011 * 2
def baseEnd_5446011 : Nat := 310713476963666354512973

theorem tailTrace_5446011 : CollatzResearch.WordTrace tailWord_5446011 prefixEnd_5446011 310713476963666354512973 := by
  unfold tailWord_5446011
  simp only [CollatzResearch.WordTrace]
  refine ⟨198632339473039726474497887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132421559648693150982998591 198632339473039726474497887)
  ·
    refine ⟨297948509209559589711746831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198632339473039726474497887 297948509209559589711746831)
    ·
      refine ⟨446922763814339384567620247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297948509209559589711746831 446922763814339384567620247)
      ·
        refine ⟨670384145721509076851430371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446922763814339384567620247 670384145721509076851430371)
        ·
          refine ⟨1005576218582263615277145557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670384145721509076851430371 1005576218582263615277145557)
          ·
            refine ⟨23568192623021803483058099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1005576218582263615277145557 23568192623021803483058099)
            ·
              refine ⟨35352288934532705224587149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23568192623021803483058099 35352288934532705224587149)
              ·
                refine ⟨13257108350449764459220181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35352288934532705224587149 13257108350449764459220181)
                ·
                  refine ⟨310713476963666354512973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13257108350449764459220181 310713476963666354512973)
                  ·
                    rfl

theorem cell23_5446011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 7].length) (baseStart_5446011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446011 prefixEnd_5446011 := by exact prefixLift 5446011
  have htrace : WordTrace (prefixWord ++ tailWord_5446011) baseStart_5446011 baseEnd_5446011 := by
    simpa [prefixWord, tailWord_5446011, baseEnd_5446011] using wordTrace_append hprefix tailTrace_5446011
  have hstable : (prefixWord ++ tailWord_5446011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446011).length < 2 ^ (prefixWord ++ tailWord_5446011).sum := by decide
  have hdescent : baseEnd_5446011 < baseStart_5446011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446041 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 1, 7]
def baseStart_5446041 : Nat := 118140960795 + 5446041 * 2 ^ 59
def prefixEnd_5446041 : Nat := 4983230072969 + 3 ^ 40 * 5446041 * 2
def baseEnd_5446041 : Nat := 932145565697544024413873

theorem tailTrace_5446041 : CollatzResearch.WordTrace tailWord_5446041 prefixEnd_5446041 932145565697544024413873 := by
  unfold tailWord_5446041
  simp only [CollatzResearch.WordTrace]
  refine ⟨198633433662931041598089977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132422289108620694398726651 198633433662931041598089977)
  ·
    refine ⟨148975075247198281198567483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198633433662931041598089977 148975075247198281198567483)
    ·
      refine ⟨223462612870797421797851225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148975075247198281198567483 223462612870797421797851225)
      ·
        refine ⟨167596959653098066348388419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223462612870797421797851225 167596959653098066348388419)
        ·
          refine ⟨251395439479647099522582629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167596959653098066348388419 251395439479647099522582629)
          ·
            refine ⟨47136644902433831160484243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251395439479647099522582629 47136644902433831160484243)
            ·
              refine ⟨70704967353650746740726365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47136644902433831160484243 70704967353650746740726365)
              ·
                refine ⟨26514362757619030027772387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70704967353650746740726365 26514362757619030027772387)
                ·
                  refine ⟨39771544136428545041658581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26514362757619030027772387 39771544136428545041658581)
                  ·
                    refine ⟨932145565697544024413873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39771544136428545041658581 932145565697544024413873)
                    ·
                      rfl

theorem cell23_5446041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_5446041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446041 prefixEnd_5446041 := by exact prefixLift 5446041
  have htrace : WordTrace (prefixWord ++ tailWord_5446041) baseStart_5446041 baseEnd_5446041 := by
    simpa [prefixWord, tailWord_5446041, baseEnd_5446041] using wordTrace_append hprefix tailTrace_5446041
  have hstable : (prefixWord ++ tailWord_5446041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446041).length < 2 ^ (prefixWord ++ tailWord_5446041).sum := by decide
  have hdescent : baseEnd_5446041 < baseStart_5446041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446078 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_5446078 : Nat := 118140960795 + 5446078 * 2 ^ 59
def prefixEnd_5446078 : Nat := 4983230072969 + 3 ^ 40 * 5446078 * 2
def baseEnd_5446078 : Nat := 2796455695876848428478949

theorem tailTrace_5446078 : CollatzResearch.WordTrace tailWord_5446078 prefixEnd_5446078 2796455695876848428478949 := by
  unfold tailWord_5446078
  simp only [CollatzResearch.WordTrace]
  refine ⟨24829347895474624614648361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132423188775864664611457925 24829347895474624614648361)
  ·
    refine ⟨18622010921605968460986271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24829347895474624614648361 18622010921605968460986271)
    ·
      refine ⟨27933016382408952691479407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18622010921605968460986271 27933016382408952691479407)
      ·
        refine ⟨41899524573613429037219111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27933016382408952691479407 41899524573613429037219111)
        ·
          refine ⟨62849286860420143555828667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41899524573613429037219111 62849286860420143555828667)
          ·
            refine ⟨94273930290630215333743001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62849286860420143555828667 94273930290630215333743001)
            ·
              refine ⟨70705447717972661500307251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94273930290630215333743001 70705447717972661500307251)
              ·
                refine ⟨106058171576958992250460877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70705447717972661500307251 106058171576958992250460877)
                ·
                  refine ⟨39771814341359622093922829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106058171576958992250460877 39771814341359622093922829)
                  ·
                    refine ⟨14914430378009858285221061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39771814341359622093922829 14914430378009858285221061)
                    ·
                      refine ⟨2796455695876848428478949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14914430378009858285221061 2796455695876848428478949)
                      ·
                        rfl

theorem cell23_5446078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_5446078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446078 prefixEnd_5446078 := by exact prefixLift 5446078
  have htrace : WordTrace (prefixWord ++ tailWord_5446078) baseStart_5446078 baseEnd_5446078 := by
    simpa [prefixWord, tailWord_5446078, baseEnd_5446078] using wordTrace_append hprefix tailTrace_5446078
  have hstable : (prefixWord ++ tailWord_5446078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446078).length < 2 ^ (prefixWord ++ tailWord_5446078).sum := by decide
  have hdescent : baseEnd_5446078 < baseStart_5446078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446091 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 6]
def baseStart_5446091 : Nat := 118140960795 + 5446091 * 2 ^ 59
def prefixEnd_5446091 : Nat := 4983230072969 + 3 ^ 40 * 5446091 * 2
def baseEnd_5446091 : Nat := 2796462371125356877616389

theorem tailTrace_5446091 : CollatzResearch.WordTrace tailWord_5446091 prefixEnd_5446091 2796462371125356877616389 := by
  unfold tailWord_5446091
  simp only [CollatzResearch.WordTrace]
  refine ⟨198635257312749900137410127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132423504875166600091606751 198635257312749900137410127)
  ·
    refine ⟨297952885969124850206115191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198635257312749900137410127 297952885969124850206115191)
    ·
      refine ⟨446929328953687275309172787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297952885969124850206115191 446929328953687275309172787)
      ·
        refine ⟨670393993430530912963759181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446929328953687275309172787 670393993430530912963759181)
        ·
          refine ⟨251397747536449092361409693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 670393993430530912963759181 251397747536449092361409693)
          ·
            refine ⟨94274155326168409635528635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251397747536449092361409693 94274155326168409635528635)
            ·
              refine ⟨141411232989252614453292953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94274155326168409635528635 141411232989252614453292953)
              ·
                refine ⟨106058424741939460839969715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141411232989252614453292953 106058424741939460839969715)
                ·
                  refine ⟨159087637112909191259954573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106058424741939460839969715 159087637112909191259954573)
                  ·
                    refine ⟨59657863917340946722482965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159087637112909191259954573 59657863917340946722482965)
                    ·
                      refine ⟨2796462371125356877616389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59657863917340946722482965 2796462371125356877616389)
                      ·
                        rfl

theorem cell23_5446091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_5446091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446091 prefixEnd_5446091 := by exact prefixLift 5446091
  have htrace : WordTrace (prefixWord ++ tailWord_5446091) baseStart_5446091 baseEnd_5446091 := by
    simpa [prefixWord, tailWord_5446091, baseEnd_5446091] using wordTrace_append hprefix tailTrace_5446091
  have hstable : (prefixWord ++ tailWord_5446091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446091).length < 2 ^ (prefixWord ++ tailWord_5446091).sum := by decide
  have hdescent : baseEnd_5446091 < baseStart_5446091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446146 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_5446146 : Nat := 118140960795 + 5446146 * 2 ^ 59
def prefixEnd_5446146 : Nat := 4983230072969 + 3 ^ 40 * 5446146 * 2
def baseEnd_5446146 : Nat := 2796490612561354162428637

theorem tailTrace_5446146 : CollatzResearch.WordTrace tailWord_5446146 prefixEnd_5446146 2796490612561354162428637 := by
  unfold tailWord_5446146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49659315831887661132665573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132424842218367096353774861 49659315831887661132665573)
  ·
    refine ⟨9311121718478936462374795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49659315831887661132665573 9311121718478936462374795)
    ·
      refine ⟨13966682577718404693562193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9311121718478936462374795 13966682577718404693562193)
      ·
        refine ⟨10475011933288803520171645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13966682577718404693562193 10475011933288803520171645)
        ·
          refine ⟨3928129474983301320064367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10475011933288803520171645 3928129474983301320064367)
          ·
            refine ⟨5892194212474951980096551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928129474983301320064367 5892194212474951980096551)
            ·
              refine ⟨8838291318712427970144827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5892194212474951980096551 8838291318712427970144827)
              ·
                refine ⟨13257436978068641955217241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8838291318712427970144827 13257436978068641955217241)
                ·
                  refine ⟨9943077733551481466412931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13257436978068641955217241 9943077733551481466412931)
                  ·
                    refine ⟨14914616600327222199619397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9943077733551481466412931 14914616600327222199619397)
                    ·
                      refine ⟨2796490612561354162428637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14914616600327222199619397 2796490612561354162428637)
                      ·
                        rfl

theorem cell23_5446146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_5446146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446146 prefixEnd_5446146 := by exact prefixLift 5446146
  have htrace : WordTrace (prefixWord ++ tailWord_5446146) baseStart_5446146 baseEnd_5446146 := by
    simpa [prefixWord, tailWord_5446146, baseEnd_5446146] using wordTrace_append hprefix tailTrace_5446146
  have hstable : (prefixWord ++ tailWord_5446146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446146).length < 2 ^ (prefixWord ++ tailWord_5446146).sum := by decide
  have hdescent : baseEnd_5446146 < baseStart_5446146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446165 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_5446165 : Nat := 118140960795 + 5446165 * 2 ^ 59
def prefixEnd_5446165 : Nat := 4983230072969 + 3 ^ 40 * 5446165 * 2
def baseEnd_5446165 : Nat := 932166789564596529363683

theorem tailTrace_5446165 : CollatzResearch.WordTrace tailWord_5446165 prefixEnd_5446165 932166789564596529363683 := by
  unfold tailWord_5446165
  simp only [CollatzResearch.WordTrace]
  refine ⟨198637956314481810775603949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132425304209654540517069299 198637956314481810775603949)
  ·
    refine ⟨74489233617930679040851481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198637956314481810775603949 74489233617930679040851481)
    ·
      refine ⟨55866925213448009280638611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74489233617930679040851481 55866925213448009280638611)
      ·
        refine ⟨83800387820172013920957917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55866925213448009280638611 83800387820172013920957917)
        ·
          refine ⟨31425145432564505220359219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83800387820172013920957917 31425145432564505220359219)
          ·
            refine ⟨47137718148846757830538829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31425145432564505220359219 47137718148846757830538829)
            ·
              refine ⟨17676644305817534186452061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47137718148846757830538829 17676644305817534186452061)
              ·
                refine ⟨6628741614681575319919523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17676644305817534186452061 6628741614681575319919523)
                ·
                  refine ⟨9943112422022362979879285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628741614681575319919523 9943112422022362979879285)
                  ·
                    refine ⟨932166789564596529363683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9943112422022362979879285 932166789564596529363683)
                    ·
                      rfl

theorem cell23_5446165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_5446165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446165 prefixEnd_5446165 := by exact prefixLift 5446165
  have htrace : WordTrace (prefixWord ++ tailWord_5446165) baseStart_5446165 baseEnd_5446165 := by
    simpa [prefixWord, tailWord_5446165, baseEnd_5446165] using wordTrace_append hprefix tailTrace_5446165
  have hstable : (prefixWord ++ tailWord_5446165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446165).length < 2 ^ (prefixWord ++ tailWord_5446165).sum := by decide
  have hdescent : baseEnd_5446165 < baseStart_5446165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446179 : List Nat := [1, 1, 1, 4, 4, 1, 2, 4, 1, 1, 3]
def baseStart_5446179 : Nat := 118140960795 + 5446179 * 2 ^ 59
def prefixEnd_5446179 : Nat := 4983230072969 + 3 ^ 40 * 5446179 * 2
def baseEnd_5446179 : Nat := 2796507557422952533315985

theorem tailTrace_5446179 : CollatzResearch.WordTrace tailWord_5446179 prefixEnd_5446179 2796507557422952533315985 := by
  unfold tailWord_5446179
  simp only [CollatzResearch.WordTrace]
  refine ⟨198638466936431091166613591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132425644624287394111075727 198638466936431091166613591)
  ·
    refine ⟨297957700404646636749920387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198638466936431091166613591 297957700404646636749920387)
    ·
      refine ⟨446936550606969955124880581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297957700404646636749920387 446936550606969955124880581)
      ·
        refine ⟨83800603238806866585915109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 446936550606969955124880581 83800603238806866585915109)
        ·
          refine ⟨15712613107276287484859083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83800603238806866585915109 15712613107276287484859083)
          ·
            refine ⟨23568919660914431227288625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15712613107276287484859083 23568919660914431227288625)
            ·
              refine ⟨17676689745685823420466469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23568919660914431227288625 17676689745685823420466469)
              ·
                refine ⟨3314379327316091891337463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17676689745685823420466469 3314379327316091891337463)
                ·
                  refine ⟨4971568990974137837006195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314379327316091891337463 4971568990974137837006195)
                  ·
                    refine ⟨7457353486461206755509293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4971568990974137837006195 7457353486461206755509293)
                    ·
                      refine ⟨2796507557422952533315985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7457353486461206755509293 2796507557422952533315985)
                      ·
                        rfl

theorem cell23_5446179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_5446179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446179 prefixEnd_5446179 := by exact prefixLift 5446179
  have htrace : WordTrace (prefixWord ++ tailWord_5446179) baseStart_5446179 baseEnd_5446179 := by
    simpa [prefixWord, tailWord_5446179, baseEnd_5446179] using wordTrace_append hprefix tailTrace_5446179
  have hstable : (prefixWord ++ tailWord_5446179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446179).length < 2 ^ (prefixWord ++ tailWord_5446179).sum := by decide
  have hdescent : baseEnd_5446179 < baseStart_5446179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446202 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4]
def baseStart_5446202 : Nat := 118140960795 + 5446202 * 2 ^ 59
def prefixEnd_5446202 : Nat := 4983230072969 + 3 ^ 40 * 5446202 * 2
def baseEnd_5446202 : Nat := 2796519367478005943328379

theorem tailTrace_5446202 : CollatzResearch.WordTrace tailWord_5446202 prefixEnd_5446202 2796519367478005943328379 := by
  unfold tailWord_5446202
  simp only [CollatzResearch.WordTrace]
  refine ⟨49659826453836941523675215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132426203876898510729800573 49659826453836941523675215)
  ·
    refine ⟨74489739680755412285512823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49659826453836941523675215 74489739680755412285512823)
    ·
      refine ⟨111734609521133118428269235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74489739680755412285512823 111734609521133118428269235)
      ·
        refine ⟨167601914281699677642403853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111734609521133118428269235 167601914281699677642403853)
        ·
          refine ⟨62850717855637379115901445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167601914281699677642403853 62850717855637379115901445)
          ·
            refine ⟨11784509597932008584231521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62850717855637379115901445 11784509597932008584231521)
            ·
              refine ⟨8838382198449006438173641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11784509597932008584231521 8838382198449006438173641)
              ·
                refine ⟨6628786648836754828630231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8838382198449006438173641 6628786648836754828630231)
                ·
                  refine ⟨9943179973255132242945347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628786648836754828630231 9943179973255132242945347)
                  ·
                    refine ⟨14914769959882698364418021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9943179973255132242945347 14914769959882698364418021)
                    ·
                      refine ⟨2796519367478005943328379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14914769959882698364418021 2796519367478005943328379)
                      ·
                        rfl

theorem cell23_5446202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_5446202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446202 prefixEnd_5446202 := by exact prefixLift 5446202
  have htrace : WordTrace (prefixWord ++ tailWord_5446202) baseStart_5446202 baseEnd_5446202 := by
    simpa [prefixWord, tailWord_5446202, baseEnd_5446202] using wordTrace_append hprefix tailTrace_5446202
  have hstable : (prefixWord ++ tailWord_5446202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446202).length < 2 ^ (prefixWord ++ tailWord_5446202).sum := by decide
  have hdescent : baseEnd_5446202 < baseStart_5446202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446222 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_5446222 : Nat := 118140960795 + 5446222 * 2 ^ 59
def prefixEnd_5446222 : Nat := 4983230072969 + 3 ^ 40 * 5446222 * 2
def baseEnd_5446222 : Nat := 2796529637091095865078287

theorem tailTrace_5446222 : CollatzResearch.WordTrace tailWord_5446222 prefixEnd_5446222 2796529637091095865078287 := by
  unfold tailWord_5446222
  simp only [CollatzResearch.WordTrace]
  refine ⟨24830004409409413688803615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132426690183516873006952613 24830004409409413688803615)
  ·
    refine ⟨37245006614114120533205423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24830004409409413688803615 37245006614114120533205423)
    ·
      refine ⟨55867509921171180799808135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37245006614114120533205423 55867509921171180799808135)
      ·
        refine ⟨83801264881756771199712203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55867509921171180799808135 83801264881756771199712203)
        ·
          refine ⟨125701897322635156799568305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83801264881756771199712203 125701897322635156799568305)
          ·
            refine ⟨94276422991976367599676229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125701897322635156799568305 94276422991976367599676229)
            ·
              refine ⟨17676829310995568924939293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94276422991976367599676229 17676829310995568924939293)
              ·
                refine ⟨6628810991623338346852235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17676829310995568924939293 6628810991623338346852235)
                ·
                  refine ⟨9943216487435007520278353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628810991623338346852235 9943216487435007520278353)
                  ·
                    refine ⟨7457412365576255640208765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9943216487435007520278353 7457412365576255640208765)
                    ·
                      refine ⟨2796529637091095865078287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7457412365576255640208765 2796529637091095865078287)
                      ·
                        rfl

theorem cell23_5446222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_5446222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446222 prefixEnd_5446222 := by exact prefixLift 5446222
  have htrace : WordTrace (prefixWord ++ tailWord_5446222) baseStart_5446222 baseEnd_5446222 := by
    simpa [prefixWord, tailWord_5446222, baseEnd_5446222] using wordTrace_append hprefix tailTrace_5446222
  have hstable : (prefixWord ++ tailWord_5446222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446222).length < 2 ^ (prefixWord ++ tailWord_5446222).sum := by decide
  have hdescent : baseEnd_5446222 < baseStart_5446222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446256 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 1, 2, 3]
def baseStart_5446256 : Nat := 118140960795 + 5446256 * 2 ^ 59
def prefixEnd_5446256 : Nat := 4983230072969 + 3 ^ 40 * 5446256 * 2
def baseEnd_5446256 : Nat := 2796547095433348732053131

theorem tailTrace_5446256 : CollatzResearch.WordTrace tailWord_5446256 prefixEnd_5446256 2796547095433348732053131 := by
  unfold tailWord_5446256
  simp only [CollatzResearch.WordTrace]
  refine ⟨99320637678576066658583311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132427516904768088878111081 99320637678576066658583311)
  ·
    refine ⟨148980956517864099987874967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99320637678576066658583311 148980956517864099987874967)
    ·
      refine ⟨223471434776796149981812451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148980956517864099987874967 223471434776796149981812451)
      ·
        refine ⟨335207152165194224972718677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223471434776796149981812451 335207152165194224972718677)
        ·
          refine ⟨3928208814435869823899047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 335207152165194224972718677 3928208814435869823899047)
          ·
            refine ⟨5892313221653804735848571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928208814435869823899047 5892313221653804735848571)
            ·
              refine ⟨8838469832480707103772857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5892313221653804735848571 8838469832480707103772857)
              ·
                refine ⟨6628852374360530327829643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8838469832480707103772857 6628852374360530327829643)
                ·
                  refine ⟨9943278561540795491744465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628852374360530327829643 9943278561540795491744465)
                  ·
                    refine ⟨7457458921155596618808349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9943278561540795491744465 7457458921155596618808349)
                    ·
                      refine ⟨2796547095433348732053131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7457458921155596618808349 2796547095433348732053131)
                      ·
                        rfl

theorem cell23_5446256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 2, 3].length) (baseStart_5446256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446256 prefixEnd_5446256 := by exact prefixLift 5446256
  have htrace : WordTrace (prefixWord ++ tailWord_5446256) baseStart_5446256 baseEnd_5446256 := by
    simpa [prefixWord, tailWord_5446256, baseEnd_5446256] using wordTrace_append hprefix tailTrace_5446256
  have hstable : (prefixWord ++ tailWord_5446256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446256).length < 2 ^ (prefixWord ++ tailWord_5446256).sum := by decide
  have hdescent : baseEnd_5446256 < baseStart_5446256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446288 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_5446288 : Nat := 118140960795 + 5446288 * 2 ^ 59
def prefixEnd_5446288 : Nat := 4983230072969 + 3 ^ 40 * 5446288 * 2
def baseEnd_5446288 : Nat := 2796563526814292606852983

theorem tailTrace_5446288 : CollatzResearch.WordTrace tailWord_5446288 prefixEnd_5446288 2796563526814292606852983 := by
  unfold tailWord_5446288
  simp only [CollatzResearch.WordTrace]
  refine ⟨99321221246518101391165759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132428294995357468521554345 99321221246518101391165759)
  ·
    refine ⟨148981831869777152086748639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99321221246518101391165759 148981831869777152086748639)
    ·
      refine ⟨223472747804665728130122959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148981831869777152086748639 223472747804665728130122959)
      ·
        refine ⟨335209121706998592195184439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223472747804665728130122959 335209121706998592195184439)
        ·
          refine ⟨502813682560497888292776659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335209121706998592195184439 502813682560497888292776659)
          ·
            refine ⟨754220523840746832439164989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502813682560497888292776659 754220523840746832439164989)
            ·
              refine ⟨282832696440280062164686871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 754220523840746832439164989 282832696440280062164686871)
              ·
                refine ⟨424249044660420093247030307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282832696440280062164686871 424249044660420093247030307)
                ·
                  refine ⟨636373566990630139870545461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424249044660420093247030307 636373566990630139870545461)
                  ·
                    refine ⟨59660021905371575612863637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 636373566990630139870545461 59660021905371575612863637)
                    ·
                      refine ⟨2796563526814292606852983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59660021905371575612863637 2796563526814292606852983)
                      ·
                        rfl

theorem cell23_5446288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_5446288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446288 prefixEnd_5446288 := by exact prefixLift 5446288
  have htrace : WordTrace (prefixWord ++ tailWord_5446288) baseStart_5446288 baseEnd_5446288 := by
    simpa [prefixWord, tailWord_5446288, baseEnd_5446288] using wordTrace_append hprefix tailTrace_5446288
  have hstable : (prefixWord ++ tailWord_5446288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446288).length < 2 ^ (prefixWord ++ tailWord_5446288).sum := by decide
  have hdescent : baseEnd_5446288 < baseStart_5446288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446292 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_5446292 : Nat := 118140960795 + 5446292 * 2 ^ 59
def prefixEnd_5446292 : Nat := 4983230072969 + 3 ^ 40 * 5446292 * 2
def baseEnd_5446292 : Nat := 2796565580736910591202965

theorem tailTrace_5446292 : CollatzResearch.WordTrace tailWord_5446292 prefixEnd_5446292 2796565580736910591202965 := by
  unfold tailWord_5446292
  simp only [CollatzResearch.WordTrace]
  refine ⟨99321294192510855732738565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132428392256681140976984753 99321294192510855732738565)
  ·
    refine ⟨18622742661095785449888481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99321294192510855732738565 18622742661095785449888481)
    ·
      refine ⟨13967056995821839087416361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18622742661095785449888481 13967056995821839087416361)
      ·
        refine ⟨10475292746866379315562271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13967056995821839087416361 10475292746866379315562271)
        ·
          refine ⟨15712939120299568973343407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10475292746866379315562271 15712939120299568973343407)
          ·
            refine ⟨23569408680449353460015111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15712939120299568973343407 23569408680449353460015111)
            ·
              refine ⟨35354113020674030190022667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23569408680449353460015111 35354113020674030190022667)
              ·
                refine ⟨53031169531011045285034001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35354113020674030190022667 53031169531011045285034001)
                ·
                  refine ⟨39773377148258283963775501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53031169531011045285034001 39773377148258283963775501)
                  ·
                    refine ⟨14915016430596856486415813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39773377148258283963775501 14915016430596856486415813)
                    ·
                      refine ⟨2796565580736910591202965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14915016430596856486415813 2796565580736910591202965)
                      ·
                        rfl

theorem cell23_5446292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_5446292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446292 prefixEnd_5446292 := by exact prefixLift 5446292
  have htrace : WordTrace (prefixWord ++ tailWord_5446292) baseStart_5446292 baseEnd_5446292 := by
    simpa [prefixWord, tailWord_5446292, baseEnd_5446292] using wordTrace_append hprefix tailTrace_5446292
  have hstable : (prefixWord ++ tailWord_5446292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446292).length < 2 ^ (prefixWord ++ tailWord_5446292).sum := by decide
  have hdescent : baseEnd_5446292 < baseStart_5446292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446295 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_5446295 : Nat := 118140960795 + 5446295 * 2 ^ 59
def prefixEnd_5446295 : Nat := 4983230072969 + 3 ^ 40 * 5446295 * 2
def baseEnd_5446295 : Nat := 2796567121178874079465451

theorem tailTrace_5446295 : CollatzResearch.WordTrace tailWord_5446295 prefixEnd_5446295 2796567121178874079465451 := by
  unfold tailWord_5446295
  simp only [CollatzResearch.WordTrace]
  refine ⟨198642697804010842977836339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132428465202673895318557559 198642697804010842977836339)
  ·
    refine ⟨297964046706016264466754509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198642697804010842977836339 297964046706016264466754509)
    ·
      refine ⟨111736517514756099175032941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297964046706016264466754509 111736517514756099175032941)
      ·
        refine ⟨41901194068033537190637353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111736517514756099175032941 41901194068033537190637353)
        ·
          refine ⟨31425895551025152892978015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41901194068033537190637353 31425895551025152892978015)
          ·
            refine ⟨47138843326537729339467023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31425895551025152892978015 47138843326537729339467023)
            ·
              refine ⟨70708264989806594009200535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47138843326537729339467023 70708264989806594009200535)
              ·
                refine ⟨106062397484709891013800803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70708264989806594009200535 106062397484709891013800803)
                ·
                  refine ⟨159093596227064836520701205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106062397484709891013800803 159093596227064836520701205)
                  ·
                    refine ⟨7457512323143664211907869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 159093596227064836520701205 7457512323143664211907869)
                    ·
                      refine ⟨2796567121178874079465451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7457512323143664211907869 2796567121178874079465451)
                      ·
                        rfl

theorem cell23_5446295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_5446295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446295 prefixEnd_5446295 := by exact prefixLift 5446295
  have htrace : WordTrace (prefixWord ++ tailWord_5446295) baseStart_5446295 baseEnd_5446295 := by
    simpa [prefixWord, tailWord_5446295, baseEnd_5446295] using wordTrace_append hprefix tailTrace_5446295
  have hstable : (prefixWord ++ tailWord_5446295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446295).length < 2 ^ (prefixWord ++ tailWord_5446295).sum := by decide
  have hdescent : baseEnd_5446295 < baseStart_5446295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446302 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_5446302 : Nat := 118140960795 + 5446302 * 2 ^ 59
def prefixEnd_5446302 : Nat := 4983230072969 + 3 ^ 40 * 5446302 * 2
def baseEnd_5446302 : Nat := 932190238514485184025973

theorem tailTrace_5446302 : CollatzResearch.WordTrace tailWord_5446302 prefixEnd_5446302 932190238514485184025973 := by
  unfold tailWord_5446302
  simp only [CollatzResearch.WordTrace]
  refine ⟨24830369139373185396667645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132428635409990322115560773 24830369139373185396667645)
  ·
    refine ⟨9311388427264944523750367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24830369139373185396667645 9311388427264944523750367)
    ·
      refine ⟨13967082640897416785625551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9311388427264944523750367 13967082640897416785625551)
      ·
        refine ⟨20950623961346125178438327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13967082640897416785625551 20950623961346125178438327)
        ·
          refine ⟨31425935942019187767657491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20950623961346125178438327 31425935942019187767657491)
          ·
            refine ⟨47138903913028781651486237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31425935942019187767657491 47138903913028781651486237)
            ·
              refine ⟨17677088967385793119307339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47138903913028781651486237 17677088967385793119307339)
              ·
                refine ⟨26515633451078689678961009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17677088967385793119307339 26515633451078689678961009)
                ·
                  refine ⟨19886725088309017259220757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26515633451078689678961009 19886725088309017259220757)
                  ·
                    refine ⟨932190238514485184025973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19886725088309017259220757 932190238514485184025973)
                    ·
                      rfl

theorem cell23_5446302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_5446302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446302 prefixEnd_5446302 := by exact prefixLift 5446302
  have htrace : WordTrace (prefixWord ++ tailWord_5446302) baseStart_5446302 baseEnd_5446302 := by
    simpa [prefixWord, tailWord_5446302, baseEnd_5446302] using wordTrace_append hprefix tailTrace_5446302
  have hstable : (prefixWord ++ tailWord_5446302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446302).length < 2 ^ (prefixWord ++ tailWord_5446302).sum := by decide
  have hdescent : baseEnd_5446302 < baseStart_5446302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446382 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_5446382 : Nat := 118140960795 + 5446382 * 2 ^ 59
def prefixEnd_5446382 : Nat := 4983230072969 + 3 ^ 40 * 5446382 * 2
def baseEnd_5446382 : Nat := 2796611793995815239077551

theorem tailTrace_5446382 : CollatzResearch.WordTrace tailWord_5446382 prefixEnd_5446382 2796611793995815239077551 := by
  unfold tailWord_5446382
  simp only [CollatzResearch.WordTrace]
  refine ⟨24830733869336957104531675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132430580636463771224168933 24830733869336957104531675)
  ·
    refine ⟨37246100804005435656797513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24830733869336957104531675 37246100804005435656797513)
    ·
      refine ⟨27934575603004076742598135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37246100804005435656797513 27934575603004076742598135)
      ·
        refine ⟨41901863404506115113897203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27934575603004076742598135 41901863404506115113897203)
        ·
          refine ⟨62852795106759172670845805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41901863404506115113897203 62852795106759172670845805)
          ·
            refine ⟨23569798165034689751567177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62852795106759172670845805 23569798165034689751567177)
            ·
              refine ⟨17677348623776017313675383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23569798165034689751567177 17677348623776017313675383)
              ·
                refine ⟨26516022935664025970513075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17677348623776017313675383 26516022935664025970513075)
                ·
                  refine ⟨39774034403496038955769613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26516022935664025970513075 39774034403496038955769613)
                  ·
                    refine ⟨14915262901311014608413605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39774034403496038955769613 14915262901311014608413605)
                    ·
                      refine ⟨2796611793995815239077551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14915262901311014608413605 2796611793995815239077551)
                      ·
                        rfl

theorem cell23_5446382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_5446382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446382 prefixEnd_5446382 := by exact prefixLift 5446382
  have htrace : WordTrace (prefixWord ++ tailWord_5446382) baseStart_5446382 baseEnd_5446382 := by
    simpa [prefixWord, tailWord_5446382, baseEnd_5446382] using wordTrace_append hprefix tailTrace_5446382
  have hstable : (prefixWord ++ tailWord_5446382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446382).length < 2 ^ (prefixWord ++ tailWord_5446382).sum := by decide
  have hdescent : baseEnd_5446382 < baseStart_5446382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446409 : List Nat := [1, 2, 1, 1, 3, 2, 2, 6, 1, 4]
def baseStart_5446409 : Nat := 118140960795 + 5446409 * 2 ^ 59
def prefixEnd_5446409 : Nat := 4983230072969 + 3 ^ 40 * 5446409 * 2
def baseEnd_5446409 : Nat := 932208552657828877813309

theorem tailTrace_5446409 : CollatzResearch.WordTrace tailWord_5446409 prefixEnd_5446409 932208552657828877813309 := by
  unfold tailWord_5446409
  simp only [CollatzResearch.WordTrace]
  refine ⟨198646855725597840447486281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132431237150398560298324187 198646855725597840447486281)
  ·
    refine ⟨148985141794198380335614711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198646855725597840447486281 148985141794198380335614711)
    ·
      refine ⟨223477712691297570503422067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148985141794198380335614711 223477712691297570503422067)
      ·
        refine ⟨335216569036946355755133101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223477712691297570503422067 335216569036946355755133101)
        ·
          refine ⟨125706213388854883408174913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335216569036946355755133101 125706213388854883408174913)
          ·
            refine ⟨94279660041641162556131185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125706213388854883408174913 94279660041641162556131185)
            ·
              refine ⟨70709745031230871917098389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94279660041641162556131185 70709745031230871917098389)
              ·
                refine ⟨3314519298338947121113987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70709745031230871917098389 3314519298338947121113987)
                ·
                  refine ⟨4971778947508420681670981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314519298338947121113987 4971778947508420681670981)
                  ·
                    refine ⟨932208552657828877813309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4971778947508420681670981 932208552657828877813309)
                    ·
                      rfl

theorem cell23_5446409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 4].length) (baseStart_5446409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446409 prefixEnd_5446409 := by exact prefixLift 5446409
  have htrace : WordTrace (prefixWord ++ tailWord_5446409) baseStart_5446409 baseEnd_5446409 := by
    simpa [prefixWord, tailWord_5446409, baseEnd_5446409] using wordTrace_append hprefix tailTrace_5446409
  have hstable : (prefixWord ++ tailWord_5446409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446409).length < 2 ^ (prefixWord ++ tailWord_5446409).sum := by decide
  have hdescent : baseEnd_5446409 < baseStart_5446409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446436 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_5446436 : Nat := 118140960795 + 5446436 * 2 ^ 59
def prefixEnd_5446436 : Nat := 4983230072969 + 3 ^ 40 * 5446436 * 2
def baseEnd_5446436 : Nat := 2796639521951158027802303

theorem tailTrace_5446436 : CollatzResearch.WordTrace tailWord_5446436 prefixEnd_5446436 2796639521951158027802303 := by
  unfold tailWord_5446436
  simp only [CollatzResearch.WordTrace]
  refine ⟨99323920248250012029359581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132431893664333349372479441 99323920248250012029359581)
  ·
    refine ⟨37246470093093754511009843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99323920248250012029359581 37246470093093754511009843)
    ·
      refine ⟨55869705139640631766514765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37246470093093754511009843 55869705139640631766514765)
      ·
        refine ⟨20951139427365236912443037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55869705139640631766514765 20951139427365236912443037)
        ·
          refine ⟨7856677285261963842166139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20951139427365236912443037 7856677285261963842166139)
          ·
            refine ⟨11785015927892945763249209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7856677285261963842166139 11785015927892945763249209)
            ·
              refine ⟨8838761945919709322436907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11785015927892945763249209 8838761945919709322436907)
              ·
                refine ⟨13258142918879563983655361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8838761945919709322436907 13258142918879563983655361)
                ·
                  refine ⟨9943607189159672987741521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13258142918879563983655361 9943607189159672987741521)
                  ·
                    refine ⟨7457705391869754740806141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9943607189159672987741521 7457705391869754740806141)
                    ·
                      refine ⟨2796639521951158027802303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7457705391869754740806141 2796639521951158027802303)
                      ·
                        rfl

theorem cell23_5446436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_5446436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446436 prefixEnd_5446436 := by exact prefixLift 5446436
  have htrace : WordTrace (prefixWord ++ tailWord_5446436) baseStart_5446436 baseEnd_5446436 := by
    simpa [prefixWord, tailWord_5446436, baseEnd_5446436] using wordTrace_append hprefix tailTrace_5446436
  have hstable : (prefixWord ++ tailWord_5446436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446436).length < 2 ^ (prefixWord ++ tailWord_5446436).sum := by decide
  have hdescent : baseEnd_5446436 < baseStart_5446436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446472 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_5446472 : Nat := 118140960795 + 5446472 * 2 ^ 59
def prefixEnd_5446472 : Nat := 4983230072969 + 3 ^ 40 * 5446472 * 2
def baseEnd_5446472 : Nat := 2796658007254719886952137

theorem tailTrace_5446472 : CollatzResearch.WordTrace tailWord_5446472 prefixEnd_5446472 2796658007254719886952137 := by
  unfold tailWord_5446472
  simp only [CollatzResearch.WordTrace]
  refine ⟨99324576762184801103514835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132432769016246401471353113 99324576762184801103514835)
  ·
    refine ⟨148986865143277201655272253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99324576762184801103514835 148986865143277201655272253)
    ·
      refine ⟨55870074428728950620727095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148986865143277201655272253 55870074428728950620727095)
      ·
        refine ⟨83805111643093425931090643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55870074428728950620727095 83805111643093425931090643)
        ·
          refine ⟨125707667464640138896635965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83805111643093425931090643 125707667464640138896635965)
          ·
            refine ⟨47140375299240052086238487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125707667464640138896635965 47140375299240052086238487)
            ·
              refine ⟨70710562948860078129357731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47140375299240052086238487 70710562948860078129357731)
              ·
                refine ⟨106065844423290117194036597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70710562948860078129357731 106065844423290117194036597)
                ·
                  refine ⟨9943672914683448486940931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106065844423290117194036597 9943672914683448486940931)
                  ·
                    refine ⟨14915509372025172730411397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9943672914683448486940931 14915509372025172730411397)
                    ·
                      refine ⟨2796658007254719886952137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14915509372025172730411397 2796658007254719886952137)
                      ·
                        rfl

theorem cell23_5446472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_5446472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446472 prefixEnd_5446472 := by exact prefixLift 5446472
  have htrace : WordTrace (prefixWord ++ tailWord_5446472) baseStart_5446472 baseEnd_5446472 := by
    simpa [prefixWord, tailWord_5446472, baseEnd_5446472] using wordTrace_append hprefix tailTrace_5446472
  have hstable : (prefixWord ++ tailWord_5446472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446472).length < 2 ^ (prefixWord ++ tailWord_5446472).sum := by decide
  have hdescent : baseEnd_5446472 < baseStart_5446472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446523 : List Nat := [1, 1, 1, 1, 1, 5, 4, 4, 1, 2, 2]
def baseStart_5446523 : Nat := 118140960795 + 5446523 * 2 ^ 59
def prefixEnd_5446523 : Nat := 4983230072969 + 3 ^ 40 * 5446523 * 2
def baseEnd_5446523 : Nat := 2796684194768099187414403

theorem tailTrace_5446523 : CollatzResearch.WordTrace tailWord_5446523 prefixEnd_5446523 2796684194768099187414403 := by
  unfold tailWord_5446523
  simp only [CollatzResearch.WordTrace]
  refine ⟨198651013647184837917136223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132434009098123225278090815 198651013647184837917136223)
  ·
    refine ⟨297976520470777256875704335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198651013647184837917136223 297976520470777256875704335)
    ·
      refine ⟨446964780706165885313556503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297976520470777256875704335 446964780706165885313556503)
      ·
        refine ⟨670447171059248827970334755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446964780706165885313556503 670447171059248827970334755)
        ·
          refine ⟨1005670756588873241955502133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670447171059248827970334755 1005670756588873241955502133)
          ·
            refine ⟨94281633430206866433328325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1005670756588873241955502133 94281633430206866433328325)
            ·
              refine ⟨17677806268163787456249061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94281633430206866433328325 17677806268163787456249061)
              ·
                refine ⟨3314588675280710148046699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17677806268163787456249061 3314588675280710148046699)
                ·
                  refine ⟨4971883012921065222070049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314588675280710148046699 4971883012921065222070049)
                  ·
                    refine ⟨3728912259690798916552537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4971883012921065222070049 3728912259690798916552537)
                    ·
                      refine ⟨2796684194768099187414403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3728912259690798916552537 2796684194768099187414403)
                      ·
                        rfl

theorem cell23_5446523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 4, 1, 2, 2].length) (baseStart_5446523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446523 prefixEnd_5446523 := by exact prefixLift 5446523
  have htrace : WordTrace (prefixWord ++ tailWord_5446523) baseStart_5446523 baseEnd_5446523 := by
    simpa [prefixWord, tailWord_5446523, baseEnd_5446523] using wordTrace_append hprefix tailTrace_5446523
  have hstable : (prefixWord ++ tailWord_5446523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446523).length < 2 ^ (prefixWord ++ tailWord_5446523).sum := by decide
  have hdescent : baseEnd_5446523 < baseStart_5446523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446536 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_5446536 : Nat := 118140960795 + 5446536 * 2 ^ 59
def prefixEnd_5446536 : Nat := 4983230072969 + 3 ^ 40 * 5446536 * 2
def baseEnd_5446536 : Nat := 2796690870016607636551843

theorem tailTrace_5446536 : CollatzResearch.WordTrace tailWord_5446536 prefixEnd_5446536 2796690870016607636551843 := by
  unfold tailWord_5446536
  simp only [CollatzResearch.WordTrace]
  refine ⟨99325743898068870568679731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132434325197425160758239641 99325743898068870568679731)
  ·
    refine ⟨148988615847103305853019597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99325743898068870568679731 148988615847103305853019597)
    ·
      refine ⟨55870730942663739694882349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148988615847103305853019597 55870730942663739694882349)
      ·
        refine ⟨20951524103498902385580881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55870730942663739694882349 20951524103498902385580881)
        ·
          refine ⟨15713643077624176789185661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20951524103498902385580881 15713643077624176789185661)
          ·
            refine ⟨5892616154109066295944623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15713643077624176789185661 5892616154109066295944623)
            ·
              refine ⟨8838924231163599443916935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5892616154109066295944623 8838924231163599443916935)
              ·
                refine ⟨13258386346745399165875403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8838924231163599443916935 13258386346745399165875403)
                ·
                  refine ⟨19887579520118098748813105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13258386346745399165875403 19887579520118098748813105)
                  ·
                    refine ⟨14915684640088574061609829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19887579520118098748813105 14915684640088574061609829)
                    ·
                      refine ⟨2796690870016607636551843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14915684640088574061609829 2796690870016607636551843)
                      ·
                        rfl

theorem cell23_5446536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_5446536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446536 prefixEnd_5446536 := by exact prefixLift 5446536
  have htrace : WordTrace (prefixWord ++ tailWord_5446536) baseStart_5446536 baseEnd_5446536 := by
    simpa [prefixWord, tailWord_5446536, baseEnd_5446536] using wordTrace_append hprefix tailTrace_5446536
  have hstable : (prefixWord ++ tailWord_5446536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446536).length < 2 ^ (prefixWord ++ tailWord_5446536).sum := by decide
  have hdescent : baseEnd_5446536 < baseStart_5446536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446539 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 3]
def baseStart_5446539 : Nat := 118140960795 + 5446539 * 2 ^ 59
def prefixEnd_5446539 : Nat := 4983230072969 + 3 ^ 40 * 5446539 * 2
def baseEnd_5446539 : Nat := 2796692410458571124814329

theorem tailTrace_5446539 : CollatzResearch.WordTrace tailWord_5446539 prefixEnd_5446539 2796692410458571124814329 := by
  unfold tailWord_5446539
  simp only [CollatzResearch.WordTrace]
  refine ⟨198651597215126872649718671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132434398143417915099812447 198651597215126872649718671)
  ·
    refine ⟨297977395822690308974578007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198651597215126872649718671 297977395822690308974578007)
    ·
      refine ⟨446966093734035463461867011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297977395822690308974578007 446966093734035463461867011)
      ·
        refine ⟨670449140601053195192800517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446966093734035463461867011 670449140601053195192800517)
        ·
          refine ⟨125709213862697474098650097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 670449140601053195192800517 125709213862697474098650097)
          ·
            refine ⟨94281910397023105573987573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125709213862697474098650097 94281910397023105573987573)
            ·
              refine ⟨8838929099720916147561335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94281910397023105573987573 8838929099720916147561335)
              ·
                refine ⟨13258393649581374221342003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8838929099720916147561335 13258393649581374221342003)
                ·
                  refine ⟨19887590474372061332013005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13258393649581374221342003 19887590474372061332013005)
                  ·
                    refine ⟨7457846427889522999504877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19887590474372061332013005 7457846427889522999504877)
                    ·
                      refine ⟨2796692410458571124814329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7457846427889522999504877 2796692410458571124814329)
                      ·
                        rfl

theorem cell23_5446539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 3].length) (baseStart_5446539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446539 prefixEnd_5446539 := by exact prefixLift 5446539
  have htrace : WordTrace (prefixWord ++ tailWord_5446539) baseStart_5446539 baseEnd_5446539 := by
    simpa [prefixWord, tailWord_5446539, baseEnd_5446539] using wordTrace_append hprefix tailTrace_5446539
  have hstable : (prefixWord ++ tailWord_5446539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446539).length < 2 ^ (prefixWord ++ tailWord_5446539).sum := by decide
  have hdescent : baseEnd_5446539 < baseStart_5446539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446579 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 5, 4, 2]
def baseStart_5446579 : Nat := 118140960795 + 5446579 * 2 ^ 59
def prefixEnd_5446579 : Nat := 4983230072969 + 3 ^ 40 * 5446579 * 2
def baseEnd_5446579 : Nat := 2796712949684750968314145

theorem tailTrace_5446579 : CollatzResearch.WordTrace tailWord_5446579 prefixEnd_5446579 2796712949684750968314145 := by
  unfold tailWord_5446579
  simp only [CollatzResearch.WordTrace]
  refine ⟨198653056134981959481174791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132435370756654639654116527 198653056134981959481174791)
  ·
    refine ⟨297979584202472939221762187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198653056134981959481174791 297979584202472939221762187)
    ·
      refine ⟨446969376303709408832643281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297979584202472939221762187 446969376303709408832643281)
      ·
        refine ⟨335227032227782056624482461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446969376303709408832643281 335227032227782056624482461)
        ·
          refine ⟨125710137085418271234180923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335227032227782056624482461 125710137085418271234180923)
          ·
            refine ⟨188565205628127406851271385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125710137085418271234180923 188565205628127406851271385)
            ·
              refine ⟨141423904221095555138453539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188565205628127406851271385 141423904221095555138453539)
              ·
                refine ⟨212135856331643332707680309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141423904221095555138453539 212135856331643332707680309)
                ·
                  refine ⟨19887736531091562441345029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212135856331643332707680309 19887736531091562441345029)
                  ·
                    refine ⟨3728950599579667957752193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19887736531091562441345029 3728950599579667957752193)
                    ·
                      refine ⟨2796712949684750968314145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3728950599579667957752193 2796712949684750968314145)
                      ·
                        rfl

theorem cell23_5446579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 4, 2].length) (baseStart_5446579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446579 prefixEnd_5446579 := by exact prefixLift 5446579
  have htrace : WordTrace (prefixWord ++ tailWord_5446579) baseStart_5446579 baseEnd_5446579 := by
    simpa [prefixWord, tailWord_5446579, baseEnd_5446579] using wordTrace_append hprefix tailTrace_5446579
  have hstable : (prefixWord ++ tailWord_5446579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446579).length < 2 ^ (prefixWord ++ tailWord_5446579).sum := by decide
  have hdescent : baseEnd_5446579 < baseStart_5446579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446600 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_5446600 : Nat := 118140960795 + 5446600 * 2 ^ 59
def prefixEnd_5446600 : Nat := 4983230072969 + 3 ^ 40 * 5446600 * 2
def baseEnd_5446600 : Nat := 2796723732778495386151549

theorem tailTrace_5446600 : CollatzResearch.WordTrace tailWord_5446600 prefixEnd_5446600 2796723732778495386151549 := by
  unfold tailWord_5446600
  simp only [CollatzResearch.WordTrace]
  refine ⟨99326911033952940033844627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132435881378603920045126169 99326911033952940033844627)
  ·
    refine ⟨148990366550929410050766941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99326911033952940033844627 148990366550929410050766941)
    ·
      refine ⟨55871387456598528769037603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148990366550929410050766941 55871387456598528769037603)
      ·
        refine ⟨83807081184897793153556405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55871387456598528769037603 83807081184897793153556405)
        ·
          refine ⟨7856913861084168108145913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83807081184897793153556405 7856913861084168108145913)
          ·
            refine ⟨5892685395813126081109435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7856913861084168108145913 5892685395813126081109435)
            ·
              refine ⟨8839028093719689121664153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5892685395813126081109435 8839028093719689121664153)
              ·
                refine ⟨6629271070289766841248115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8839028093719689121664153 6629271070289766841248115)
                ·
                  refine ⟨9943906605434650261872173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6629271070289766841248115 9943906605434650261872173)
                  ·
                    refine ⟨3728964977037993848202065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9943906605434650261872173 3728964977037993848202065)
                    ·
                      refine ⟨2796723732778495386151549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3728964977037993848202065 2796723732778495386151549)
                      ·
                        rfl

theorem cell23_5446600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_5446600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446600 prefixEnd_5446600 := by exact prefixLift 5446600
  have htrace : WordTrace (prefixWord ++ tailWord_5446600) baseStart_5446600 baseEnd_5446600 := by
    simpa [prefixWord, tailWord_5446600, baseEnd_5446600] using wordTrace_append hprefix tailTrace_5446600
  have hstable : (prefixWord ++ tailWord_5446600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446600).length < 2 ^ (prefixWord ++ tailWord_5446600).sum := by decide
  have hdescent : baseEnd_5446600 < baseStart_5446600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446602 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 9]
def baseStart_5446602 : Nat := 118140960795 + 5446602 * 2 ^ 59
def prefixEnd_5446602 : Nat := 4983230072969 + 3 ^ 40 * 5446602 * 2
def baseEnd_5446602 : Nat := 310747195526644930925171

theorem tailTrace_5446602 : CollatzResearch.WordTrace tailWord_5446602 prefixEnd_5446602 310747195526644930925171 := by
  unfold tailWord_5446602
  simp only [CollatzResearch.WordTrace]
  refine ⟨49663473753474658602315515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132435930009265756272841373 49663473753474658602315515)
  ·
    refine ⟨74495210630211987903473273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49663473753474658602315515 74495210630211987903473273)
    ·
      refine ⟨55871407972658990927604955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74495210630211987903473273 55871407972658990927604955)
      ·
        refine ⟨83807111958988486391407433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55871407972658990927604955 83807111958988486391407433)
        ·
          refine ⟨62855333969241364793555575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83807111958988486391407433 62855333969241364793555575)
          ·
            refine ⟨94283000953862047190333363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62855333969241364793555575 94283000953862047190333363)
            ·
              refine ⟨141424501430793070785500045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94283000953862047190333363 141424501430793070785500045)
              ·
                refine ⟨53034188036547401544562517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141424501430793070785500045 53034188036547401544562517)
                ·
                  refine ⟨310747195526644930925171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53034188036547401544562517 310747195526644930925171)
                  ·
                    rfl

theorem cell23_5446602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_5446602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446602 prefixEnd_5446602 := by exact prefixLift 5446602
  have htrace : WordTrace (prefixWord ++ tailWord_5446602) baseStart_5446602 baseEnd_5446602 := by
    simpa [prefixWord, tailWord_5446602, baseEnd_5446602] using wordTrace_append hprefix tailTrace_5446602
  have hstable : (prefixWord ++ tailWord_5446602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446602).length < 2 ^ (prefixWord ++ tailWord_5446602).sum := by decide
  have hdescent : baseEnd_5446602 < baseStart_5446602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446613 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 1, 4, 2]
def baseStart_5446613 : Nat := 118140960795 + 5446613 * 2 ^ 59
def prefixEnd_5446613 : Nat := 4983230072969 + 3 ^ 40 * 5446613 * 2
def baseEnd_5446613 : Nat := 2796730408027003835288989

theorem tailTrace_5446613 : CollatzResearch.WordTrace tailWord_5446613 prefixEnd_5446613 2796730408027003835288989 := by
  unfold tailWord_5446613
  simp only [CollatzResearch.WordTrace]
  refine ⟨198654296216858783287912493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132436197477905855525274995 198654296216858783287912493)
  ·
    refine ⟨74495361081322043732967185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198654296216858783287912493 74495361081322043732967185)
    ·
      refine ⟨55871520810991532799725389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74495361081322043732967185 55871520810991532799725389)
      ·
        refine ⟨20951820304121824799897021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55871520810991532799725389 20951820304121824799897021)
        ·
          refine ⟨7856932614045684299961383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20951820304121824799897021 7856932614045684299961383)
          ·
            refine ⟨11785398921068526449942075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7856932614045684299961383 11785398921068526449942075)
            ·
              refine ⟨17678098381602789674913113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11785398921068526449942075 17678098381602789674913113)
              ·
                refine ⟨13258573786202092256184835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17678098381602789674913113 13258573786202092256184835)
                ·
                  refine ⟨19887860679303138384277253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13258573786202092256184835 19887860679303138384277253)
                  ·
                    refine ⟨3728973877369338447051985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19887860679303138384277253 3728973877369338447051985)
                    ·
                      refine ⟨2796730408027003835288989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3728973877369338447051985 2796730408027003835288989)
                      ·
                        rfl

theorem cell23_5446613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_5446613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446613 prefixEnd_5446613 := by exact prefixLift 5446613
  have htrace : WordTrace (prefixWord ++ tailWord_5446613) baseStart_5446613 baseEnd_5446613 := by
    simpa [prefixWord, tailWord_5446613, baseEnd_5446613] using wordTrace_append hprefix tailTrace_5446613
  have hstable : (prefixWord ++ tailWord_5446613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446613).length < 2 ^ (prefixWord ++ tailWord_5446613).sum := by decide
  have hdescent : baseEnd_5446613 < baseStart_5446613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446646 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_5446646 : Nat := 118140960795 + 5446646 * 2 ^ 59
def prefixEnd_5446646 : Nat := 4983230072969 + 3 ^ 40 * 5446646 * 2
def baseEnd_5446646 : Nat := 2796747352888602206176337

theorem tailTrace_5446646 : CollatzResearch.WordTrace tailWord_5446646 prefixEnd_5446646 2796747352888602206176337 := by
  unfold tailWord_5446646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12415968739108701870241487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132436999883826153282575861 12415968739108701870241487)
  ·
    refine ⟨18623953108663052805362231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12415968739108701870241487 18623953108663052805362231)
    ·
      refine ⟨27935929662994579208043347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18623953108663052805362231 27935929662994579208043347)
      ·
        refine ⟨41903894494491868812065021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27935929662994579208043347 41903894494491868812065021)
        ·
          refine ⟨15713960435434450804524383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41903894494491868812065021 15713960435434450804524383)
          ·
            refine ⟨23570940653151676206786575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15713960435434450804524383 23570940653151676206786575)
            ·
              refine ⟨35356410979727514310179863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23570940653151676206786575 35356410979727514310179863)
              ·
                refine ⟨53034616469591271465269795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35356410979727514310179863 53034616469591271465269795)
                ·
                  refine ⟨79551924704386907197904693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53034616469591271465269795 79551924704386907197904693)
                  ·
                    refine ⟨7457992941036272549803565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79551924704386907197904693 7457992941036272549803565)
                    ·
                      refine ⟨2796747352888602206176337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7457992941036272549803565 2796747352888602206176337)
                      ·
                        rfl

theorem cell23_5446646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_5446646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446646 prefixEnd_5446646 := by exact prefixLift 5446646
  have htrace : WordTrace (prefixWord ++ tailWord_5446646) baseStart_5446646 baseEnd_5446646 := by
    simpa [prefixWord, tailWord_5446646, baseEnd_5446646] using wordTrace_append hprefix tailTrace_5446646
  have hstable : (prefixWord ++ tailWord_5446646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446646).length < 2 ^ (prefixWord ++ tailWord_5446646).sum := by decide
  have hdescent : baseEnd_5446646 < baseStart_5446646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446666 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_5446666 : Nat := 118140960795 + 5446666 * 2 ^ 59
def prefixEnd_5446666 : Nat := 4983230072969 + 3 ^ 40 * 5446666 * 2
def baseEnd_5446666 : Nat := 932252540833897375975415

theorem tailTrace_5446666 : CollatzResearch.WordTrace tailWord_5446666 prefixEnd_5446666 932252540833897375975415 := by
  unfold tailWord_5446666
  simp only [CollatzResearch.WordTrace]
  refine ⟨49664057321416693334897963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132437486190444515559727901 49664057321416693334897963)
  ·
    refine ⟨74496085982125040002346945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49664057321416693334897963 74496085982125040002346945)
    ·
      refine ⟨55872064486593780001760209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74496085982125040002346945 55872064486593780001760209)
      ·
        refine ⟨41904048364945335001320157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55872064486593780001760209 41904048364945335001320157)
        ·
          refine ⟨15714018136854500625495059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41904048364945335001320157 15714018136854500625495059)
          ·
            refine ⟨23571027205281750938242589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15714018136854500625495059 23571027205281750938242589)
            ·
              refine ⟨8839135201980656601840971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23571027205281750938242589 8839135201980656601840971)
              ·
                refine ⟨13258702802970984902761457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8839135201980656601840971 13258702802970984902761457)
                ·
                  refine ⟨9944027102228238677071093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13258702802970984902761457 9944027102228238677071093)
                  ·
                    refine ⟨932252540833897375975415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9944027102228238677071093 932252540833897375975415)
                    ·
                      rfl

theorem cell23_5446666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_5446666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446666 prefixEnd_5446666 := by exact prefixLift 5446666
  have htrace : WordTrace (prefixWord ++ tailWord_5446666) baseStart_5446666 baseEnd_5446666 := by
    simpa [prefixWord, tailWord_5446666, baseEnd_5446666] using wordTrace_append hprefix tailTrace_5446666
  have hstable : (prefixWord ++ tailWord_5446666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446666).length < 2 ^ (prefixWord ++ tailWord_5446666).sum := by decide
  have hdescent : baseEnd_5446666 < baseStart_5446666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446672 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_5446672 : Nat := 118140960795 + 5446672 * 2 ^ 59
def prefixEnd_5446672 : Nat := 4983230072969 + 3 ^ 40 * 5446672 * 2
def baseEnd_5446672 : Nat := 2796760703385619104451217

theorem tailTrace_5446672 : CollatzResearch.WordTrace tailWord_5446672 prefixEnd_5446672 2796760703385619104451217 := by
  unfold tailWord_5446672
  simp only [CollatzResearch.WordTrace]
  refine ⟨99328224061822518182155135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132437632082430024242873513 99328224061822518182155135)
  ·
    refine ⟨148992336092733777273232703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99328224061822518182155135 148992336092733777273232703)
    ·
      refine ⟨223488504139100665909849055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148992336092733777273232703 223488504139100665909849055)
      ·
        refine ⟨335232756208650998864773583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223488504139100665909849055 335232756208650998864773583)
        ·
          refine ⟨502849134312976498297160375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335232756208650998864773583 502849134312976498297160375)
          ·
            refine ⟨754273701469464747445740563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502849134312976498297160375 754273701469464747445740563)
            ·
              refine ⟨1131410552204197121168610845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754273701469464747445740563 1131410552204197121168610845)
              ·
                refine ⟨424278957076573920438229067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1131410552204197121168610845 424278957076573920438229067)
                ·
                  refine ⟨636418435614860880657343601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424278957076573920438229067 636418435614860880657343601)
                  ·
                    refine ⟨477313826711145660493007701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 636418435614860880657343601 477313826711145660493007701)
                    ·
                      refine ⟨2796760703385619104451217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 477313826711145660493007701 2796760703385619104451217)
                      ·
                        rfl

theorem cell23_5446672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_5446672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446672 prefixEnd_5446672 := by exact prefixLift 5446672
  have htrace : WordTrace (prefixWord ++ tailWord_5446672) baseStart_5446672 baseEnd_5446672 := by
    simpa [prefixWord, tailWord_5446672, baseEnd_5446672] using wordTrace_append hprefix tailTrace_5446672
  have hstable : (prefixWord ++ tailWord_5446672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446672).length < 2 ^ (prefixWord ++ tailWord_5446672).sum := by decide
  have hdescent : baseEnd_5446672 < baseStart_5446672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446719 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 3]
def baseStart_5446719 : Nat := 118140960795 + 5446719 * 2 ^ 59
def prefixEnd_5446719 : Nat := 4983230072969 + 3 ^ 40 * 5446719 * 2
def baseEnd_5446719 : Nat := 2796784836976380420563501

theorem tailTrace_5446719 : CollatzResearch.WordTrace tailWord_5446719 prefixEnd_5446719 2796784836976380420563501 := by
  unfold tailWord_5446719
  simp only [CollatzResearch.WordTrace]
  refine ⟨198658162354474763391271211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132438774902983175594180807 198658162354474763391271211)
  ·
    refine ⟨297987243531712145086906817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198658162354474763391271211 297987243531712145086906817)
    ·
      refine ⟨223490432648784108815180113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297987243531712145086906817 223490432648784108815180113)
      ·
        refine ⟨167617824486588081611385085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223490432648784108815180113 167617824486588081611385085)
        ·
          refine ⟨62856684182470530604269407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167617824486588081611385085 62856684182470530604269407)
          ·
            refine ⟨94285026273705795906404111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62856684182470530604269407 94285026273705795906404111)
            ·
              refine ⟨141427539410558693859606167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94285026273705795906404111 141427539410558693859606167)
              ·
                refine ⟨212141309115838040789409251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141427539410558693859606167 212141309115838040789409251)
                ·
                  refine ⟨318211963673757061184113877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212141309115838040789409251 318211963673757061184113877)
                  ·
                    refine ⟨7458092898603681121502669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 318211963673757061184113877 7458092898603681121502669)
                    ·
                      refine ⟨2796784836976380420563501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7458092898603681121502669 2796784836976380420563501)
                      ·
                        rfl

theorem cell23_5446719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_5446719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446719 prefixEnd_5446719 := by exact prefixLift 5446719
  have htrace : WordTrace (prefixWord ++ tailWord_5446719) baseStart_5446719 baseEnd_5446719 := by
    simpa [prefixWord, tailWord_5446719, baseEnd_5446719] using wordTrace_append hprefix tailTrace_5446719
  have hstable : (prefixWord ++ tailWord_5446719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446719).length < 2 ^ (prefixWord ++ tailWord_5446719).sum := by decide
  have hdescent : baseEnd_5446719 < baseStart_5446719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446736 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 5, 1, 3]
def baseStart_5446736 : Nat := 118140960795 + 5446736 * 2 ^ 59
def prefixEnd_5446736 : Nat := 4983230072969 + 3 ^ 40 * 5446736 * 2
def baseEnd_5446736 : Nat := 2796793566147506854050923

theorem tailTrace_5446736 : CollatzResearch.WordTrace tailWord_5446736 prefixEnd_5446736 2796793566147506854050923 := by
  unfold tailWord_5446736
  simp only [CollatzResearch.WordTrace]
  refine ⟨99329391197706587647320031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132439188263608783529760041 99329391197706587647320031)
  ·
    refine ⟨148994086796559881470980047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99329391197706587647320031 148994086796559881470980047)
    ·
      refine ⟨223491130194839822206470071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148994086796559881470980047 223491130194839822206470071)
      ·
        refine ⟨335236695292259733309705107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223491130194839822206470071 335236695292259733309705107)
        ·
          refine ⟨502855042938389599964557661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335236695292259733309705107 502855042938389599964557661)
          ·
            refine ⟨188570641101896099986709123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 502855042938389599964557661 188570641101896099986709123)
            ·
              refine ⟨282855961652844149980063685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188570641101896099986709123 282855961652844149980063685)
              ·
                refine ⟨53035492809908278121261941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282855961652844149980063685 53035492809908278121261941)
                ·
                  refine ⟨4972077450928901073868307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53035492809908278121261941 4972077450928901073868307)
                  ·
                    refine ⟨7458116176393351610802461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4972077450928901073868307 7458116176393351610802461)
                    ·
                      refine ⟨2796793566147506854050923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7458116176393351610802461 2796793566147506854050923)
                      ·
                        rfl

theorem cell23_5446736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 1, 3].length) (baseStart_5446736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446736 prefixEnd_5446736 := by exact prefixLift 5446736
  have htrace : WordTrace (prefixWord ++ tailWord_5446736) baseStart_5446736 baseEnd_5446736 := by
    simpa [prefixWord, tailWord_5446736, baseEnd_5446736] using wordTrace_append hprefix tailTrace_5446736
  have hstable : (prefixWord ++ tailWord_5446736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446736).length < 2 ^ (prefixWord ++ tailWord_5446736).sum := by decide
  have hdescent : baseEnd_5446736 < baseStart_5446736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446746 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2]
def baseStart_5446746 : Nat := 118140960795 + 5446746 * 2 ^ 59
def prefixEnd_5446746 : Nat := 4983230072969 + 3 ^ 40 * 5446746 * 2
def baseEnd_5446746 : Nat := 2796798700954051814925877

theorem tailTrace_5446746 : CollatzResearch.WordTrace tailWord_5446746 prefixEnd_5446746 2796798700954051814925877 := by
  unfold tailWord_5446746
  simp only [CollatzResearch.WordTrace]
  refine ⟨49664786781344236750626023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132439431416917964668336061 49664786781344236750626023)
  ·
    refine ⟨74497180172016355125939035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49664786781344236750626023 74497180172016355125939035)
    ·
      refine ⟨111745770258024532688908553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74497180172016355125939035 111745770258024532688908553)
      ·
        refine ⟨83809327693518399516681415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111745770258024532688908553 83809327693518399516681415)
        ·
          refine ⟨125713991540277599275022123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83809327693518399516681415 125713991540277599275022123)
          ·
            refine ⟨188570987310416398912533185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125713991540277599275022123 188570987310416398912533185)
            ·
              refine ⟨141428240482812299184399889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188570987310416398912533185 141428240482812299184399889)
              ·
                refine ⟨106071180362109224388299917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141428240482812299184399889 106071180362109224388299917)
                ·
                  refine ⟨39776692635790959145612469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106071180362109224388299917 39776692635790959145612469)
                  ·
                    refine ⟨3729064934605402419901169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39776692635790959145612469 3729064934605402419901169)
                    ·
                      refine ⟨2796798700954051814925877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729064934605402419901169 2796798700954051814925877)
                      ·
                        rfl

theorem cell23_5446746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_5446746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446746 prefixEnd_5446746 := by exact prefixLift 5446746
  have htrace : WordTrace (prefixWord ++ tailWord_5446746) baseStart_5446746 baseEnd_5446746 := by
    simpa [prefixWord, tailWord_5446746, baseEnd_5446746] using wordTrace_append hprefix tailTrace_5446746
  have hstable : (prefixWord ++ tailWord_5446746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446746).length < 2 ^ (prefixWord ++ tailWord_5446746).sum := by decide
  have hdescent : baseEnd_5446746 < baseStart_5446746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446753 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_5446753 : Nat := 118140960795 + 5446753 * 2 ^ 59
def prefixEnd_5446753 : Nat := 4983230072969 + 3 ^ 40 * 5446753 * 2
def baseEnd_5446753 : Nat := 2796802295318633287538345

theorem tailTrace_5446753 : CollatzResearch.WordTrace tailWord_5446753 prefixEnd_5446753 2796802295318633287538345 := by
  unfold tailWord_5446753
  simp only [CollatzResearch.WordTrace]
  refine ⟨198659402436351587198008913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132439601624234391465339275 198659402436351587198008913)
  ·
    refine ⟨148994551827263690398506685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198659402436351587198008913 148994551827263690398506685)
    ·
      refine ⟨55872956935223883899440007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148994551827263690398506685 55872956935223883899440007)
      ·
        refine ⟨83809435402835825849160011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55872956935223883899440007 83809435402835825849160011)
        ·
          refine ⟨125714153104253738773740017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83809435402835825849160011 125714153104253738773740017)
          ·
            refine ⟨94285614828190304080305013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125714153104253738773740017 94285614828190304080305013)
            ·
              refine ⟨8839276390142841007528595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94285614828190304080305013 8839276390142841007528595)
              ·
                refine ⟨13258914585214261511292893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8839276390142841007528595 13258914585214261511292893)
                ·
                  refine ⟨4972092969455348066734835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13258914585214261511292893 4972092969455348066734835)
                  ·
                    refine ⟨7458139454183022100102253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4972092969455348066734835 7458139454183022100102253)
                    ·
                      refine ⟨2796802295318633287538345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7458139454183022100102253 2796802295318633287538345)
                      ·
                        rfl

theorem cell23_5446753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_5446753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446753 prefixEnd_5446753 := by exact prefixLift 5446753
  have htrace : WordTrace (prefixWord ++ tailWord_5446753) baseStart_5446753 baseEnd_5446753 := by
    simpa [prefixWord, tailWord_5446753, baseEnd_5446753] using wordTrace_append hprefix tailTrace_5446753
  have hstable : (prefixWord ++ tailWord_5446753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446753).length < 2 ^ (prefixWord ++ tailWord_5446753).sum := by decide
  have hdescent : baseEnd_5446753 < baseStart_5446753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446776 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 2, 6, 2]
def baseStart_5446776 : Nat := 118140960795 + 5446776 * 2 ^ 59
def prefixEnd_5446776 : Nat := 4983230072969 + 3 ^ 40 * 5446776 * 2
def baseEnd_5446776 : Nat := 2796814105373686697550739

theorem tailTrace_5446776 : CollatzResearch.WordTrace tailWord_5446776 prefixEnd_5446776 2796814105373686697550739 := by
  unfold tailWord_5446776
  simp only [CollatzResearch.WordTrace]
  refine ⟨99330120657634131063048091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132440160876845508084064121 99330120657634131063048091)
  ·
    refine ⟨148995180986451196594572137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99330120657634131063048091 148995180986451196594572137)
    ·
      refine ⟨111746385739838397445929103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148995180986451196594572137 111746385739838397445929103)
      ·
        refine ⟨167619578609757596168893655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111746385739838397445929103 167619578609757596168893655)
        ·
          refine ⟨251429367914636394253340483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167619578609757596168893655 251429367914636394253340483)
          ·
            refine ⟨377144051871954591380010725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251429367914636394253340483 377144051871954591380010725)
            ·
              refine ⟨70714509725991485883752011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 377144051871954591380010725 70714509725991485883752011)
              ·
                refine ⟨106071764588987228825628017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70714509725991485883752011 106071764588987228825628017)
                ·
                  refine ⟨79553823441740421619221013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106071764588987228825628017 79553823441740421619221013)
                  ·
                    refine ⟨3729085473831582263400985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79553823441740421619221013 3729085473831582263400985)
                    ·
                      refine ⟨2796814105373686697550739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729085473831582263400985 2796814105373686697550739)
                      ·
                        rfl

theorem cell23_5446776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_5446776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446776 prefixEnd_5446776 := by exact prefixLift 5446776
  have htrace : WordTrace (prefixWord ++ tailWord_5446776) baseStart_5446776 baseEnd_5446776 := by
    simpa [prefixWord, tailWord_5446776, baseEnd_5446776] using wordTrace_append hprefix tailTrace_5446776
  have hstable : (prefixWord ++ tailWord_5446776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446776).length < 2 ^ (prefixWord ++ tailWord_5446776).sum := by decide
  have hdescent : baseEnd_5446776 < baseStart_5446776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446779 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 5]
def baseStart_5446779 : Nat := 118140960795 + 5446779 * 2 ^ 59
def prefixEnd_5446779 : Nat := 4983230072969 + 3 ^ 40 * 5446779 * 2
def baseEnd_5446779 : Nat := 2796815645815650185813225

theorem tailTrace_5446779 : CollatzResearch.WordTrace tailWord_5446779 prefixEnd_5446779 2796815645815650185813225 := by
  unfold tailWord_5446779
  simp only [CollatzResearch.WordTrace]
  refine ⟨198660350734257393638455391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132440233822838262425636927 198660350734257393638455391)
  ·
    refine ⟨297990526101386090457683087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198660350734257393638455391 297990526101386090457683087)
    ·
      refine ⟨446985789152079135686524631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297990526101386090457683087 446985789152079135686524631)
      ·
        refine ⟨670478683728118703529786947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446985789152079135686524631 670478683728118703529786947)
        ·
          refine ⟨1005718025592178055294680421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670478683728118703529786947 1005718025592178055294680421)
          ·
            refine ⟨188572129798533385367752579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1005718025592178055294680421 188572129798533385367752579)
            ·
              refine ⟨282858194697800078051628869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188572129798533385367752579 282858194697800078051628869)
              ·
                refine ⟨53035911505837514634680413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282858194697800078051628869 53035911505837514634680413)
                ·
                  refine ⟨19888466814689067988005155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53035911505837514634680413 19888466814689067988005155)
                  ·
                    refine ⟨29832700222033601982007733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19888466814689067988005155 29832700222033601982007733)
                    ·
                      refine ⟨2796815645815650185813225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29832700222033601982007733 2796815645815650185813225)
                      ·
                        rfl

theorem cell23_5446779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 5].length) (baseStart_5446779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446779 prefixEnd_5446779 := by exact prefixLift 5446779
  have htrace : WordTrace (prefixWord ++ tailWord_5446779) baseStart_5446779 baseEnd_5446779 := by
    simpa [prefixWord, tailWord_5446779, baseEnd_5446779] using wordTrace_append hprefix tailTrace_5446779
  have hstable : (prefixWord ++ tailWord_5446779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446779).length < 2 ^ (prefixWord ++ tailWord_5446779).sum := by decide
  have hdescent : baseEnd_5446779 < baseStart_5446779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446819 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 6]
def baseStart_5446819 : Nat := 118140960795 + 5446819 * 2 ^ 59
def prefixEnd_5446819 : Nat := 4983230072969 + 3 ^ 40 * 5446819 * 2
def baseEnd_5446819 : Nat := 2796836185041830029313041

theorem tailTrace_5446819 : CollatzResearch.WordTrace tailWord_5446819 prefixEnd_5446819 2796836185041830029313041 := by
  unfold tailWord_5446819
  simp only [CollatzResearch.WordTrace]
  refine ⟨198661809654112480469911511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132441206436074986979941007 198661809654112480469911511)
  ·
    refine ⟨297992714481168720704867267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198661809654112480469911511 297992714481168720704867267)
    ·
      refine ⟨446989071721753081057300901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297992714481168720704867267 446989071721753081057300901)
      ·
        refine ⟨83810450947828702698243919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 446989071721753081057300901 83810450947828702698243919)
        ·
          refine ⟨125715676421743054047365879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83810450947828702698243919 125715676421743054047365879)
          ·
            refine ⟨188573514632614581071048819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125715676421743054047365879 188573514632614581071048819)
            ·
              refine ⟨282860271948921871606573229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188573514632614581071048819 282860271948921871606573229)
              ·
                refine ⟨106072601980845701852464961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282860271948921871606573229 106072601980845701852464961)
                ·
                  refine ⟨79554451485634276389348721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106072601980845701852464961 79554451485634276389348721)
                  ·
                    refine ⟨59665838614225707292011541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79554451485634276389348721 59665838614225707292011541)
                    ·
                      refine ⟨2796836185041830029313041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59665838614225707292011541 2796836185041830029313041)
                      ·
                        rfl

theorem cell23_5446819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_5446819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446819 prefixEnd_5446819 := by exact prefixLift 5446819
  have htrace : WordTrace (prefixWord ++ tailWord_5446819) baseStart_5446819 baseEnd_5446819 := by
    simpa [prefixWord, tailWord_5446819, baseEnd_5446819] using wordTrace_append hprefix tailTrace_5446819
  have hstable : (prefixWord ++ tailWord_5446819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446819).length < 2 ^ (prefixWord ++ tailWord_5446819).sum := by decide
  have hdescent : baseEnd_5446819 < baseStart_5446819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446823 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_5446823 : Nat := 118140960795 + 5446823 * 2 ^ 59
def prefixEnd_5446823 : Nat := 4983230072969 + 3 ^ 40 * 5446823 * 2
def baseEnd_5446823 : Nat := 2796838238964448013663023

theorem tailTrace_5446823 : CollatzResearch.WordTrace tailWord_5446823 prefixEnd_5446823 2796838238964448013663023 := by
  unfold tailWord_5446823
  simp only [CollatzResearch.WordTrace]
  refine ⟨198661955546097989153057123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132441303697398659435371415 198661955546097989153057123)
  ·
    refine ⟨297992933319146983729585685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198661955546097989153057123 297992933319146983729585685)
    ·
      refine ⟨13968418749335014862324329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 297992933319146983729585685 13968418749335014862324329)
      ·
        refine ⟨10476314062001261146743247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13968418749335014862324329 10476314062001261146743247)
        ·
          refine ⟨15714471093001891720114871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10476314062001261146743247 15714471093001891720114871)
          ·
            refine ⟨23571706639502837580172307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15714471093001891720114871 23571706639502837580172307)
            ·
              refine ⟨35357559959254256370258461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23571706639502837580172307 35357559959254256370258461)
              ·
                refine ⟨13259084984720346138846923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35357559959254256370258461 13259084984720346138846923)
                ·
                  refine ⟨19888627477080519208270385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13259084984720346138846923 19888627477080519208270385)
                  ·
                    refine ⟨14916470607810389406202789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19888627477080519208270385 14916470607810389406202789)
                    ·
                      refine ⟨2796838238964448013663023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14916470607810389406202789 2796838238964448013663023)
                      ·
                        rfl

theorem cell23_5446823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_5446823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446823 prefixEnd_5446823 := by exact prefixLift 5446823
  have htrace : WordTrace (prefixWord ++ tailWord_5446823) baseStart_5446823 baseEnd_5446823 := by
    simpa [prefixWord, tailWord_5446823, baseEnd_5446823] using wordTrace_append hprefix tailTrace_5446823
  have hstable : (prefixWord ++ tailWord_5446823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446823).length < 2 ^ (prefixWord ++ tailWord_5446823).sum := by decide
  have hdescent : baseEnd_5446823 < baseStart_5446823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446833 : List Nat := [1, 2, 2, 5, 1, 2, 3, 7]
def baseStart_5446833 : Nat := 118140960795 + 5446833 * 2 ^ 59
def prefixEnd_5446833 : Nat := 4983230072969 + 3 ^ 40 * 5446833 * 2
def baseEnd_5446833 : Nat := 103586791621147887945851

theorem tailTrace_5446833 : CollatzResearch.WordTrace tailWord_5446833 prefixEnd_5446833 103586791621147887945851 := by
  unfold tailWord_5446833
  simp only [CollatzResearch.WordTrace]
  refine ⟨198662320276061760860921153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132441546850707840573947435 198662320276061760860921153)
  ·
    refine ⟨148996740207046320645690865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198662320276061760860921153 148996740207046320645690865)
    ·
      refine ⟨111747555155284740484268149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148996740207046320645690865 111747555155284740484268149)
      ·
        refine ⟨10476333295807944420400139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111747555155284740484268149 10476333295807944420400139)
        ·
          refine ⟨15714499943711916630600209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10476333295807944420400139 15714499943711916630600209)
          ·
            refine ⟨11785874957783937472950157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15714499943711916630600209 11785874957783937472950157)
            ·
              refine ⟨4419703109168976552356309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11785874957783937472950157 4419703109168976552356309)
              ·
                refine ⟨103586791621147887945851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4419703109168976552356309 103586791621147887945851)
                ·
                  rfl

theorem cell23_5446833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 7].length) (baseStart_5446833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446833 prefixEnd_5446833 := by exact prefixLift 5446833
  have htrace : WordTrace (prefixWord ++ tailWord_5446833) baseStart_5446833 baseEnd_5446833 := by
    simpa [prefixWord, tailWord_5446833, baseEnd_5446833] using wordTrace_append hprefix tailTrace_5446833
  have hstable : (prefixWord ++ tailWord_5446833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446833).length < 2 ^ (prefixWord ++ tailWord_5446833).sum := by decide
  have hdescent : baseEnd_5446833 < baseStart_5446833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446844 : List Nat := [2, 2, 2, 3, 2, 2, 2, 3, 1, 2, 2]
def baseStart_5446844 : Nat := 118140960795 + 5446844 * 2 ^ 59
def prefixEnd_5446844 : Nat := 4983230072969 + 3 ^ 40 * 5446844 * 2
def baseEnd_5446844 : Nat := 2796849022058192431500427

theorem tailTrace_5446844 : CollatzResearch.WordTrace tailWord_5446844 prefixEnd_5446844 2796849022058192431500427 := by
  unfold tailWord_5446844
  simp only [CollatzResearch.WordTrace]
  refine ⟨99331360739510954869785793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132441814319347939826381057 99331360739510954869785793)
  ·
    refine ⟨74498520554633216152339345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99331360739510954869785793 74498520554633216152339345)
    ·
      refine ⟨55873890415974912114254509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74498520554633216152339345 55873890415974912114254509)
      ·
        refine ⟨20952708905990592042845441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55873890415974912114254509 20952708905990592042845441)
        ·
          refine ⟨15714531679492944032134081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20952708905990592042845441 15714531679492944032134081)
          ·
            refine ⟨11785898759619708024100561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15714531679492944032134081 11785898759619708024100561)
            ·
              refine ⟨8839424069714781018075421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11785898759619708024100561 8839424069714781018075421)
              ·
                refine ⟨3314784026143042881778283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8839424069714781018075421 3314784026143042881778283)
                ·
                  refine ⟨4972176039214564322667425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314784026143042881778283 4972176039214564322667425)
                  ·
                    refine ⟨3729132029410923242000569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4972176039214564322667425 3729132029410923242000569)
                    ·
                      refine ⟨2796849022058192431500427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729132029410923242000569 2796849022058192431500427)
                      ·
                        rfl

theorem cell23_5446844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_5446844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446844 prefixEnd_5446844 := by exact prefixLift 5446844
  have htrace : WordTrace (prefixWord ++ tailWord_5446844) baseStart_5446844 baseEnd_5446844 := by
    simpa [prefixWord, tailWord_5446844, baseEnd_5446844] using wordTrace_append hprefix tailTrace_5446844
  have hstable : (prefixWord ++ tailWord_5446844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446844).length < 2 ^ (prefixWord ++ tailWord_5446844).sum := by decide
  have hdescent : baseEnd_5446844 < baseStart_5446844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446850 : List Nat := [3, 5, 1, 1, 2, 1, 10]
def baseStart_5446850 : Nat := 118140960795 + 5446850 * 2 ^ 59
def prefixEnd_5446850 : Nat := 4983230072969 + 3 ^ 40 * 5446850 * 2
def baseEnd_5446850 : Nat := 34529038307927400099079

theorem tailTrace_5446850 : CollatzResearch.WordTrace tailWord_5446850 prefixEnd_5446850 34529038307927400099079 := by
  unfold tailWord_5446850
  simp only [CollatzResearch.WordTrace]
  refine ⟨49665735079250043191072501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132441960211333448509526669 49665735079250043191072501)
  ·
    refine ⟨4656162663679691549163047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49665735079250043191072501 4656162663679691549163047)
    ·
      refine ⟨6984243995519537323744571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4656162663679691549163047 6984243995519537323744571)
      ·
        refine ⟨10476365993279305985616857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6984243995519537323744571 10476365993279305985616857)
        ·
          refine ⟨7857274494959479489212643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10476365993279305985616857 7857274494959479489212643)
          ·
            refine ⟨11785911742439219233818965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7857274494959479489212643 11785911742439219233818965)
            ·
              refine ⟨34529038307927400099079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11785911742439219233818965 34529038307927400099079)
              ·
                rfl

theorem cell23_5446850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 10].length) (baseStart_5446850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446850 prefixEnd_5446850 := by exact prefixLift 5446850
  have htrace : WordTrace (prefixWord ++ tailWord_5446850) baseStart_5446850 baseEnd_5446850 := by
    simpa [prefixWord, tailWord_5446850, baseEnd_5446850] using wordTrace_append hprefix tailTrace_5446850
  have hstable : (prefixWord ++ tailWord_5446850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446850).length < 2 ^ (prefixWord ++ tailWord_5446850).sum := by decide
  have hdescent : baseEnd_5446850 < baseStart_5446850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446854 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_5446854 : Nat := 118140960795 + 5446854 * 2 ^ 59
def prefixEnd_5446854 : Nat := 4983230072969 + 3 ^ 40 * 5446854 * 2
def baseEnd_5446854 : Nat := 932284718954912464125127

theorem tailTrace_5446854 : CollatzResearch.WordTrace tailWord_5446854 prefixEnd_5446854 932284718954912464125127 := by
  unfold tailWord_5446854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208221444030802545232363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132442057472657120964957077 6208221444030802545232363)
  ·
    refine ⟨9312332166046203817848545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6208221444030802545232363 9312332166046203817848545)
    ·
      refine ⟨6984249124534652863386409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9312332166046203817848545 6984249124534652863386409)
      ·
        refine ⟨5238186843400989647539807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6984249124534652863386409 5238186843400989647539807)
        ·
          refine ⟨7857280265101484471309711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5238186843400989647539807 7857280265101484471309711)
          ·
            refine ⟨11785920397652226706964567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7857280265101484471309711 11785920397652226706964567)
            ·
              refine ⟨17678880596478340060446851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11785920397652226706964567 17678880596478340060446851)
              ·
                refine ⟨26518320894717510090670277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17678880596478340060446851 26518320894717510090670277)
                ·
                  refine ⟨4972185167759533142000677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26518320894717510090670277 4972185167759533142000677)
                  ·
                    refine ⟨932284718954912464125127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4972185167759533142000677 932284718954912464125127)
                    ·
                      rfl

theorem cell23_5446854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_5446854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446854 prefixEnd_5446854 := by exact prefixLift 5446854
  have htrace : WordTrace (prefixWord ++ tailWord_5446854) baseStart_5446854 baseEnd_5446854 := by
    simpa [prefixWord, tailWord_5446854, baseEnd_5446854] using wordTrace_append hprefix tailTrace_5446854
  have hstable : (prefixWord ++ tailWord_5446854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446854).length < 2 ^ (prefixWord ++ tailWord_5446854).sum := by decide
  have hdescent : baseEnd_5446854 < baseStart_5446854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446861 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5446861 : Nat := 118140960795 + 5446861 * 2 ^ 59
def prefixEnd_5446861 : Nat := 4983230072969 + 3 ^ 40 * 5446861 * 2
def baseEnd_5446861 : Nat := 2796857751229318864987849

theorem tailTrace_5446861 : CollatzResearch.WordTrace tailWord_5446861 prefixEnd_5446861 2796857751229318864987849 := by
  unfold tailWord_5446861
  simp only [CollatzResearch.WordTrace]
  refine ⟨198663341519960321642940437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132442227679973547761960291 198663341519960321642940437)
  ·
    refine ⟨9312344133748140077012833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198663341519960321642940437 9312344133748140077012833)
    ·
      refine ⟨6984258100311105057759625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9312344133748140077012833 6984258100311105057759625)
      ·
        refine ⟨5238193575233328793319719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6984258100311105057759625 5238193575233328793319719)
        ·
          refine ⟨7857290362849993189979579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5238193575233328793319719 7857290362849993189979579)
          ·
            refine ⟨11785935544274989784969369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7857290362849993189979579 11785935544274989784969369)
            ·
              refine ⟨8839451658206242338727027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11785935544274989784969369 8839451658206242338727027)
              ·
                refine ⟨13259177487309363508090541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8839451658206242338727027 13259177487309363508090541)
                ·
                  refine ⟨4972191557741011315533953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13259177487309363508090541 4972191557741011315533953)
                  ·
                    refine ⟨3729143668305758486650465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4972191557741011315533953 3729143668305758486650465)
                    ·
                      refine ⟨2796857751229318864987849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729143668305758486650465 2796857751229318864987849)
                      ·
                        rfl

theorem cell23_5446861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5446861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446861 prefixEnd_5446861 := by exact prefixLift 5446861
  have htrace : WordTrace (prefixWord ++ tailWord_5446861) baseStart_5446861 baseEnd_5446861 := by
    simpa [prefixWord, tailWord_5446861, baseEnd_5446861] using wordTrace_append hprefix tailTrace_5446861
  have hstable : (prefixWord ++ tailWord_5446861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446861).length < 2 ^ (prefixWord ++ tailWord_5446861).sum := by decide
  have hdescent : baseEnd_5446861 < baseStart_5446861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446877 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_5446877 : Nat := 118140960795 + 5446877 * 2 ^ 59
def prefixEnd_5446877 : Nat := 4983230072969 + 3 ^ 40 * 5446877 * 2
def baseEnd_5446877 : Nat := 2796865966919790802387775

theorem tailTrace_5446877 : CollatzResearch.WordTrace tailWord_5446877 prefixEnd_5446877 2796865966919790802387775 := by
  unfold tailWord_5446877
  simp only [CollatzResearch.WordTrace]
  refine ⟨198663925087902356375522885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132442616725268237583681923 198663925087902356375522885)
  ·
    refine ⟨37249485953981691820410541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198663925087902356375522885 37249485953981691820410541)
    ·
      refine ⟨13968557232743134432653953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37249485953981691820410541 13968557232743134432653953)
      ·
        refine ⟨10476417924557350824490465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13968557232743134432653953 10476417924557350824490465)
        ·
          refine ⟨7857313443418013118367849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10476417924557350824490465 7857313443418013118367849)
          ·
            refine ⟨5892985082563509838775887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7857313443418013118367849 5892985082563509838775887)
            ·
              refine ⟨8839477623845264758163831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5892985082563509838775887 8839477623845264758163831)
              ·
                refine ⟨13259216435767897137245747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8839477623845264758163831 13259216435767897137245747)
                ·
                  refine ⟨19888824653651845705868621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13259216435767897137245747 19888824653651845705868621)
                  ·
                    refine ⟨7458309245119442139700733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19888824653651845705868621 7458309245119442139700733)
                    ·
                      refine ⟨2796865966919790802387775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7458309245119442139700733 2796865966919790802387775)
                      ·
                        rfl

theorem cell23_5446877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_5446877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446877 prefixEnd_5446877 := by exact prefixLift 5446877
  have htrace : WordTrace (prefixWord ++ tailWord_5446877) baseStart_5446877 baseEnd_5446877 := by
    simpa [prefixWord, tailWord_5446877, baseEnd_5446877] using wordTrace_append hprefix tailTrace_5446877
  have hstable : (prefixWord ++ tailWord_5446877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446877).length < 2 ^ (prefixWord ++ tailWord_5446877).sum := by decide
  have hdescent : baseEnd_5446877 < baseStart_5446877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446923 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 7]
def baseStart_5446923 : Nat := 118140960795 + 5446923 * 2 ^ 59
def prefixEnd_5446923 : Nat := 4983230072969 + 3 ^ 40 * 5446923 * 2
def baseEnd_5446923 : Nat := 310765509669988624712507

theorem tailTrace_5446923 : CollatzResearch.WordTrace tailWord_5446923 prefixEnd_5446923 310765509669988624712507 := by
  unfold tailWord_5446923
  simp only [CollatzResearch.WordTrace]
  refine ⟨198665602845735706231697423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132443735230490470821131615 198665602845735706231697423)
  ·
    refine ⟨297998404268603559347546135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198665602845735706231697423 297998404268603559347546135)
    ·
      refine ⟨446997606402905339021319203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297998404268603559347546135 446997606402905339021319203)
      ·
        refine ⟨670496409604358008531978805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446997606402905339021319203 670496409604358008531978805)
        ·
          refine ⟨62859038400408563299873013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 670496409604358008531978805 62859038400408563299873013)
          ·
            refine ⟨5893034850038302809363095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62859038400408563299873013 5893034850038302809363095)
            ·
              refine ⟨8839552275057454214044643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893034850038302809363095 8839552275057454214044643)
              ·
                refine ⟨13259328412586181321066965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8839552275057454214044643 13259328412586181321066965)
                ·
                  refine ⟨310765509669988624712507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13259328412586181321066965 310765509669988624712507)
                  ·
                    rfl

theorem cell23_5446923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 7].length) (baseStart_5446923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446923 prefixEnd_5446923 := by exact prefixLift 5446923
  have htrace : WordTrace (prefixWord ++ tailWord_5446923) baseStart_5446923 baseEnd_5446923 := by
    simpa [prefixWord, tailWord_5446923, baseEnd_5446923] using wordTrace_append hprefix tailTrace_5446923
  have hstable : (prefixWord ++ tailWord_5446923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446923).length < 2 ^ (prefixWord ++ tailWord_5446923).sum := by decide
  have hdescent : baseEnd_5446923 < baseStart_5446923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446976 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_5446976 : Nat := 118140960795 + 5446976 * 2 ^ 59
def prefixEnd_5446976 : Nat := 4983230072969 + 3 ^ 40 * 5446976 * 2
def baseEnd_5446976 : Nat := 2796916801504585915049819

theorem tailTrace_5446976 : CollatzResearch.WordTrace tailWord_5446976 prefixEnd_5446976 2796916801504585915049819 := by
  unfold tailWord_5446976
  simp only [CollatzResearch.WordTrace]
  refine ⟨99333767957271848141688391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132445023943029130855584521 99333767957271848141688391)
  ·
    refine ⟨149000651935907772212532587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99333767957271848141688391 149000651935907772212532587)
    ·
      refine ⟨223500977903861658318798881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149000651935907772212532587 223500977903861658318798881)
      ·
        refine ⟨167625733427896243739099161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223500977903861658318798881 167625733427896243739099161)
        ·
          refine ⟨125719300070922182804324371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167625733427896243739099161 125719300070922182804324371)
          ·
            refine ⟨188578950106383274206486557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125719300070922182804324371 188578950106383274206486557)
            ·
              refine ⟨70717106289893727827432459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188578950106383274206486557 70717106289893727827432459)
              ·
                refine ⟨106075659434840591741148689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70717106289893727827432459 106075659434840591741148689)
                ·
                  refine ⟨79556744576130443805861517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106075659434840591741148689 79556744576130443805861517)
                  ·
                    refine ⟨29833779216048916427198069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79556744576130443805861517 29833779216048916427198069)
                    ·
                      refine ⟨2796916801504585915049819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29833779216048916427198069 2796916801504585915049819)
                      ·
                        rfl

theorem cell23_5446976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_5446976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446976 prefixEnd_5446976 := by exact prefixLift 5446976
  have htrace : WordTrace (prefixWord ++ tailWord_5446976) baseStart_5446976 baseEnd_5446976 := by
    simpa [prefixWord, tailWord_5446976, baseEnd_5446976] using wordTrace_append hprefix tailTrace_5446976
  have hstable : (prefixWord ++ tailWord_5446976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446976).length < 2 ^ (prefixWord ++ tailWord_5446976).sum := by decide
  have hdescent : baseEnd_5446976 < baseStart_5446976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446980 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5446980 : Nat := 118140960795 + 5446980 * 2 ^ 59
def prefixEnd_5446980 : Nat := 4983230072969 + 3 ^ 40 * 5446980 * 2
def baseEnd_5446980 : Nat := 2796918855427203899399801

theorem tailTrace_5446980 : CollatzResearch.WordTrace tailWord_5446980 prefixEnd_5446980 2796918855427203899399801 := by
  unfold tailWord_5446980
  simp only [CollatzResearch.WordTrace]
  refine ⟨99333840903264602483261197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132445121204352803311014929 99333840903264602483261197)
  ·
    refine ⟨37250190338724225931222949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99333840903264602483261197 37250190338724225931222949)
    ·
      refine ⟨6984410688510792362104303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37250190338724225931222949 6984410688510792362104303)
      ·
        refine ⟨10476616032766188543156455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6984410688510792362104303 10476616032766188543156455)
        ·
          refine ⟨15714924049149282814734683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10476616032766188543156455 15714924049149282814734683)
          ·
            refine ⟨23572386073723924222102025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15714924049149282814734683 23572386073723924222102025)
            ·
              refine ⟨17679289555292943166576519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23572386073723924222102025 17679289555292943166576519)
              ·
                refine ⟨26518934332939414749864779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17679289555292943166576519 26518934332939414749864779)
                ·
                  refine ⟨39778401499409122124797169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26518934332939414749864779 39778401499409122124797169)
                  ·
                    refine ⟨29833801124556841593597877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39778401499409122124797169 29833801124556841593597877)
                    ·
                      refine ⟨2796918855427203899399801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29833801124556841593597877 2796918855427203899399801)
                      ·
                        rfl

theorem cell23_5446980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5446980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446980 prefixEnd_5446980 := by exact prefixLift 5446980
  have htrace : WordTrace (prefixWord ++ tailWord_5446980) baseStart_5446980 baseEnd_5446980 := by
    simpa [prefixWord, tailWord_5446980, baseEnd_5446980] using wordTrace_append hprefix tailTrace_5446980
  have hstable : (prefixWord ++ tailWord_5446980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446980).length < 2 ^ (prefixWord ++ tailWord_5446980).sum := by decide
  have hdescent : baseEnd_5446980 < baseStart_5446980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446990 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_5446990 : Nat := 118140960795 + 5446990 * 2 ^ 59
def prefixEnd_5446990 : Nat := 4983230072969 + 3 ^ 40 * 5446990 * 2
def baseEnd_5446990 : Nat := 2796923990233748860274755

theorem tailTrace_5446990 : CollatzResearch.WordTrace tailWord_5446990 prefixEnd_5446990 2796923990233748860274755 := by
  unfold tailWord_5446990
  simp only [CollatzResearch.WordTrace]
  refine ⟨24833505817061622084298303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132445364357661984449590949 24833505817061622084298303)
  ·
    refine ⟨37250258725592433126447455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24833505817061622084298303 37250258725592433126447455)
    ·
      refine ⟨55875388088388649689671183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37250258725592433126447455 55875388088388649689671183)
      ·
        refine ⟨83813082132582974534506775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55875388088388649689671183 83813082132582974534506775)
        ·
          refine ⟨125719623198874461801760163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83813082132582974534506775 125719623198874461801760163)
          ·
            refine ⟨188579434798311692702640245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125719623198874461801760163 188579434798311692702640245)
            ·
              refine ⟨17679322012341721190872523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188579434798311692702640245 17679322012341721190872523)
              ·
                refine ⟨26518983018512581786308785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17679322012341721190872523 26518983018512581786308785)
                ·
                  refine ⟨19889237263884436339731589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26518983018512581786308785 19889237263884436339731589)
                  ·
                    refine ⟨3729231986978331813699673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19889237263884436339731589 3729231986978331813699673)
                    ·
                      refine ⟨2796923990233748860274755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729231986978331813699673 2796923990233748860274755)
                      ·
                        rfl

theorem cell23_5446990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_5446990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446990 prefixEnd_5446990 := by exact prefixLift 5446990
  have htrace : WordTrace (prefixWord ++ tailWord_5446990) baseStart_5446990 baseEnd_5446990 := by
    simpa [prefixWord, tailWord_5446990, baseEnd_5446990] using wordTrace_append hprefix tailTrace_5446990
  have hstable : (prefixWord ++ tailWord_5446990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446990).length < 2 ^ (prefixWord ++ tailWord_5446990).sum := by decide
  have hdescent : baseEnd_5446990 < baseStart_5446990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5446993 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_5446993 : Nat := 118140960795 + 5446993 * 2 ^ 59
def prefixEnd_5446993 : Nat := 4983230072969 + 3 ^ 40 * 5446993 * 2
def baseEnd_5446993 : Nat := 2796925530675712348537241

theorem tailTrace_5446993 : CollatzResearch.WordTrace tailWord_5446993 prefixEnd_5446993 2796925530675712348537241 := by
  unfold tailWord_5446993
  simp only [CollatzResearch.WordTrace]
  refine ⟨198668155955482108186745633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132445437303654738791163755 198668155955482108186745633)
  ·
    refine ⟨149001116966611581140059225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198668155955482108186745633 149001116966611581140059225)
    ·
      refine ⟨111750837724958685855044419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149001116966611581140059225 111750837724958685855044419)
      ·
        refine ⟨167626256587438028782566629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111750837724958685855044419 167626256587438028782566629)
        ·
          refine ⟨31429923110144630396731243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167626256587438028782566629 31429923110144630396731243)
          ·
            refine ⟨47144884665216945595096865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31429923110144630396731243 47144884665216945595096865)
            ·
              refine ⟨35358663498912709196322649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47144884665216945595096865 35358663498912709196322649)
              ·
                refine ⟨26518997624184531897241987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35358663498912709196322649 26518997624184531897241987)
                ·
                  refine ⟨39778496436276797845862981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26518997624184531897241987 39778496436276797845862981)
                  ·
                    refine ⟨7458468081801899596099309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39778496436276797845862981 7458468081801899596099309)
                    ·
                      refine ⟨2796925530675712348537241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7458468081801899596099309 2796925530675712348537241)
                      ·
                        rfl

theorem cell23_5446993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_5446993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5446993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5446993 prefixEnd_5446993 := by exact prefixLift 5446993
  have htrace : WordTrace (prefixWord ++ tailWord_5446993) baseStart_5446993 baseEnd_5446993 := by
    simpa [prefixWord, tailWord_5446993, baseEnd_5446993] using wordTrace_append hprefix tailTrace_5446993
  have hstable : (prefixWord ++ tailWord_5446993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5446993).length < 2 ^ (prefixWord ++ tailWord_5446993).sum := by decide
  have hdescent : baseEnd_5446993 < baseStart_5446993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5446993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447010 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_5447010 : Nat := 118140960795 + 5447010 * 2 ^ 59
def prefixEnd_5447010 : Nat := 4983230072969 + 3 ^ 40 * 5447010 * 2
def baseEnd_5447010 : Nat := 2796934259846838782024663

theorem tailTrace_5447010 : CollatzResearch.WordTrace tailWord_5447010 prefixEnd_5447010 2796934259846838782024663 := by
  unfold tailWord_5447010
  simp only [CollatzResearch.WordTrace]
  refine ⟨49667193999105130022528621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132445850664280346726742989 49667193999105130022528621)
  ·
    refine ⟨18625197749664423758448233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49667193999105130022528621 18625197749664423758448233)
    ·
      refine ⟨13968898312248317818836175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18625197749664423758448233 13968898312248317818836175)
      ·
        refine ⟨20953347468372476728254263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13968898312248317818836175 20953347468372476728254263)
        ·
          refine ⟨31430021202558715092381395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20953347468372476728254263 31430021202558715092381395)
          ·
            refine ⟨47145031803838072638572093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31430021202558715092381395 47145031803838072638572093)
            ·
              refine ⟨17679386926439277239464535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47145031803838072638572093 17679386926439277239464535)
              ·
                refine ⟨26519080389658915859196803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17679386926439277239464535 26519080389658915859196803)
                ·
                  refine ⟨39778620584488373788795205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26519080389658915859196803 39778620584488373788795205)
                  ·
                    refine ⟨7458491359591570085399101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39778620584488373788795205 7458491359591570085399101)
                    ·
                      refine ⟨2796934259846838782024663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7458491359591570085399101 2796934259846838782024663)
                      ·
                        rfl

theorem cell23_5447010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_5447010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447010 prefixEnd_5447010 := by exact prefixLift 5447010
  have htrace : WordTrace (prefixWord ++ tailWord_5447010) baseStart_5447010 baseEnd_5447010 := by
    simpa [prefixWord, tailWord_5447010, baseEnd_5447010] using wordTrace_append hprefix tailTrace_5447010
  have hstable : (prefixWord ++ tailWord_5447010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447010).length < 2 ^ (prefixWord ++ tailWord_5447010).sum := by decide
  have hdescent : baseEnd_5447010 < baseStart_5447010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447068 : List Nat := [2, 2, 3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_5447068 : Nat := 118140960795 + 5447068 * 2 ^ 59
def prefixEnd_5447068 : Nat := 4983230072969 + 3 ^ 40 * 5447068 * 2
def baseEnd_5447068 : Nat := 932321347241599851699799

theorem tailTrace_5447068 : CollatzResearch.WordTrace tailWord_5447068 prefixEnd_5447068 932321347241599851699799 := by
  unfold tailWord_5447068
  simp only [CollatzResearch.WordTrace]
  refine ⟨99335445715105197997862929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132447260953473597330483905 99335445715105197997862929)
  ·
    refine ⟨74501584286328898498397197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99335445715105197997862929 74501584286328898498397197)
    ·
      refine ⟨27938094107373336936898949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74501584286328898498397197 27938094107373336936898949)
      ·
        refine ⟨5238392645132500675668553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27938094107373336936898949 5238392645132500675668553)
        ·
          refine ⟨3928794483849375506751415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5238392645132500675668553 3928794483849375506751415)
          ·
            refine ⟨5893191725774063260127123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928794483849375506751415 5893191725774063260127123)
            ·
              refine ⟨8839787588661094890190685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893191725774063260127123 8839787588661094890190685)
              ·
                refine ⟨3314920345747910583821507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8839787588661094890190685 3314920345747910583821507)
                ·
                  refine ⟨4972380518621865875732261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314920345747910583821507 4972380518621865875732261)
                  ·
                    refine ⟨932321347241599851699799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4972380518621865875732261 932321347241599851699799)
                    ·
                      rfl

theorem cell23_5447068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_5447068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447068 prefixEnd_5447068 := by exact prefixLift 5447068
  have htrace : WordTrace (prefixWord ++ tailWord_5447068) baseStart_5447068 baseEnd_5447068 := by
    simpa [prefixWord, tailWord_5447068, baseEnd_5447068] using wordTrace_append hprefix tailTrace_5447068
  have hstable : (prefixWord ++ tailWord_5447068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447068).length < 2 ^ (prefixWord ++ tailWord_5447068).sum := by decide
  have hdescent : baseEnd_5447068 < baseStart_5447068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447107 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 2, 4]
def baseStart_5447107 : Nat := 118140960795 + 5447107 * 2 ^ 59
def prefixEnd_5447107 : Nat := 4983230072969 + 3 ^ 40 * 5447107 * 2
def baseEnd_5447107 : Nat := 932328022490108300837239

theorem tailTrace_5447107 : CollatzResearch.WordTrace tailWord_5447107 prefixEnd_5447107 932328022490108300837239 := by
  unfold tailWord_5447107
  simp only [CollatzResearch.WordTrace]
  refine ⟨198672313877069105656395575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132448209251379403770930383 198672313877069105656395575)
  ·
    refine ⟨298008470815603658484593363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198672313877069105656395575 298008470815603658484593363)
    ·
      refine ⟨447012706223405487726890045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298008470815603658484593363 447012706223405487726890045)
      ·
        refine ⟨167629764833777057897583767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447012706223405487726890045 167629764833777057897583767)
        ·
          refine ⟨251444647250665586846375651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167629764833777057897583767 251444647250665586846375651)
          ·
            refine ⟨377166970875998380269563477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251444647250665586846375651 377166970875998380269563477)
            ·
              refine ⟨4419925439953106018783947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 377166970875998380269563477 4419925439953106018783947)
              ·
                refine ⟨6629888159929659028175921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4419925439953106018783947 6629888159929659028175921)
                ·
                  refine ⟨4972416119947244271131941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6629888159929659028175921 4972416119947244271131941)
                  ·
                    refine ⟨932328022490108300837239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4972416119947244271131941 932328022490108300837239)
                    ·
                      rfl

theorem cell23_5447107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 4].length) (baseStart_5447107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447107 prefixEnd_5447107 := by exact prefixLift 5447107
  have htrace : WordTrace (prefixWord ++ tailWord_5447107) baseStart_5447107 baseEnd_5447107 := by
    simpa [prefixWord, tailWord_5447107, baseEnd_5447107] using wordTrace_append hprefix tailTrace_5447107
  have hstable : (prefixWord ++ tailWord_5447107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447107).length < 2 ^ (prefixWord ++ tailWord_5447107).sum := by decide
  have hdescent : baseEnd_5447107 < baseStart_5447107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447130 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_5447130 : Nat := 118140960795 + 5447130 * 2 ^ 59
def prefixEnd_5447130 : Nat := 4983230072969 + 3 ^ 40 * 5447130 * 2
def baseEnd_5447130 : Nat := 2796995877525378312524111

theorem tailTrace_5447130 : CollatzResearch.WordTrace tailWord_5447130 prefixEnd_5447130 2796995877525378312524111 := by
  unfold tailWord_5447130
  simp only [CollatzResearch.WordTrace]
  refine ⟨49668288188996445146120711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132448768503990520389655229 49668288188996445146120711)
  ·
    refine ⟨74502432283494667719181067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49668288188996445146120711 74502432283494667719181067)
    ·
      refine ⟨111753648425242001578771601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74502432283494667719181067 111753648425242001578771601)
      ·
        refine ⟨83815236318931501184078701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111753648425242001578771601 83815236318931501184078701)
        ·
          refine ⟨31430713619599312944029513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83815236318931501184078701 31430713619599312944029513)
          ·
            refine ⟨23573035214699484708022135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31430713619599312944029513 23573035214699484708022135)
            ·
              refine ⟨35359552822049227062033203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23573035214699484708022135 35359552822049227062033203)
              ·
                refine ⟨53039329233073840593049805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35359552822049227062033203 53039329233073840593049805)
                ·
                  refine ⟨19889748462402690222393677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53039329233073840593049805 19889748462402690222393677)
                  ·
                    refine ⟨7458655673401008833397629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19889748462402690222393677 7458655673401008833397629)
                    ·
                      refine ⟨2796995877525378312524111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7458655673401008833397629 2796995877525378312524111)
                      ·
                        rfl

theorem cell23_5447130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_5447130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447130 prefixEnd_5447130 := by exact prefixLift 5447130
  have htrace : WordTrace (prefixWord ++ tailWord_5447130) baseStart_5447130 baseEnd_5447130 := by
    simpa [prefixWord, tailWord_5447130, baseEnd_5447130] using wordTrace_append hprefix tailTrace_5447130
  have hstable : (prefixWord ++ tailWord_5447130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447130).length < 2 ^ (prefixWord ++ tailWord_5447130).sum := by decide
  have hdescent : baseEnd_5447130 < baseStart_5447130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447163 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 2, 6]
def baseStart_5447163 : Nat := 118140960795 + 5447163 * 2 ^ 59
def prefixEnd_5447163 : Nat := 4983230072969 + 3 ^ 40 * 5447163 * 2
def baseEnd_5447163 : Nat := 932337607462325561137153

theorem tailTrace_5447163 : CollatzResearch.WordTrace tailWord_5447163 prefixEnd_5447163 932337607462325561137153 := by
  unfold tailWord_5447163
  simp only [CollatzResearch.WordTrace]
  refine ⟨198674356364866227220434143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132449570909910818146956095 198674356364866227220434143)
  ·
    refine ⟨298011534547299340830651215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198674356364866227220434143 298011534547299340830651215)
    ·
      refine ⟨447017301820949011245976823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298011534547299340830651215 447017301820949011245976823)
      ·
        refine ⟨670525952731423516868965235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447017301820949011245976823 670525952731423516868965235)
        ·
          refine ⟨1005788929097135275303447853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670525952731423516868965235 1005788929097135275303447853)
          ·
            refine ⟨377170848411425728238792945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1005788929097135275303447853 377170848411425728238792945)
            ·
              refine ⟨282878136308569296179094709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377170848411425728238792945 282878136308569296179094709)
              ·
                refine ⟨26519825278928371516790129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282878136308569296179094709 26519825278928371516790129)
                ·
                  refine ⟨19889868959196278637592597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26519825278928371516790129 19889868959196278637592597)
                  ·
                    refine ⟨932337607462325561137153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19889868959196278637592597 932337607462325561137153)
                    ·
                      rfl

theorem cell23_5447163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 6].length) (baseStart_5447163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447163 prefixEnd_5447163 := by exact prefixLift 5447163
  have htrace : WordTrace (prefixWord ++ tailWord_5447163) baseStart_5447163 baseEnd_5447163 := by
    simpa [prefixWord, tailWord_5447163, baseEnd_5447163] using wordTrace_append hprefix tailTrace_5447163
  have hstable : (prefixWord ++ tailWord_5447163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447163).length < 2 ^ (prefixWord ++ tailWord_5447163).sum := by decide
  have hdescent : baseEnd_5447163 < baseStart_5447163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447187 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 1, 4, 2]
def baseStart_5447187 : Nat := 118140960795 + 5447187 * 2 ^ 59
def prefixEnd_5447187 : Nat := 4983230072969 + 3 ^ 40 * 5447187 * 2
def baseEnd_5447187 : Nat := 2797025145922684589511349

theorem tailTrace_5447187 : CollatzResearch.WordTrace tailWord_5447187 prefixEnd_5447187 2797025145922684589511349 := by
  unfold tailWord_5447187
  simp only [CollatzResearch.WordTrace]
  refine ⟨198675231716779279319307815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132450154477852852879538543 198675231716779279319307815)
  ·
    refine ⟨298012847575168918978961723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198675231716779279319307815 298012847575168918978961723)
    ·
      refine ⟨447019271362753378468442585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298012847575168918978961723 447019271362753378468442585)
      ·
        refine ⟨335264453522065033851331939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447019271362753378468442585 335264453522065033851331939)
        ·
          refine ⟨502896680283097550776997909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335264453522065033851331939 502896680283097550776997909)
          ·
            refine ⟨23573281888270197692671777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 502896680283097550776997909 23573281888270197692671777)
            ·
              refine ⟨17679961416202648269503833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23573281888270197692671777 17679961416202648269503833)
              ·
                refine ⟨13259971062151986202127875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17679961416202648269503833 13259971062151986202127875)
                ·
                  refine ⟨19889956593227979303191813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13259971062151986202127875 19889956593227979303191813)
                  ·
                    refine ⟨3729366861230246119348465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19889956593227979303191813 3729366861230246119348465)
                    ·
                      refine ⟨2797025145922684589511349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729366861230246119348465 2797025145922684589511349)
                      ·
                        rfl

theorem cell23_5447187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 4, 2].length) (baseStart_5447187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447187 prefixEnd_5447187 := by exact prefixLift 5447187
  have htrace : WordTrace (prefixWord ++ tailWord_5447187) baseStart_5447187 baseEnd_5447187 := by
    simpa [prefixWord, tailWord_5447187, baseEnd_5447187] using wordTrace_append hprefix tailTrace_5447187
  have hstable : (prefixWord ++ tailWord_5447187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447187).length < 2 ^ (prefixWord ++ tailWord_5447187).sum := by decide
  have hdescent : baseEnd_5447187 < baseStart_5447187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447244 : List Nat := [2, 2, 1, 3, 1, 5, 1, 3, 5]
def baseStart_5447244 : Nat := 118140960795 + 5447244 * 2 ^ 59
def prefixEnd_5447244 : Nat := 4983230072969 + 3 ^ 40 * 5447244 * 2
def baseEnd_5447244 : Nat := 310783823813332318499843

theorem tailTrace_5447244 : CollatzResearch.WordTrace tailWord_5447244 prefixEnd_5447244 310783823813332318499843 := by
  unfold tailWord_5447244
  simp only [CollatzResearch.WordTrace]
  refine ⟨99338655338786389027066393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132451540451715185369421857 99338655338786389027066393)
  ·
    refine ⟨74503991504089791770299795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99338655338786389027066393 74503991504089791770299795)
    ·
      refine ⟨111755987256134687655449693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74503991504089791770299795 111755987256134687655449693)
      ·
        refine ⟨41908495221050507870793635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111755987256134687655449693 41908495221050507870793635)
        ·
          refine ⟨62862742831575761806190453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41908495221050507870793635 62862742831575761806190453)
          ·
            refine ⟨5893382140460227669330355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62862742831575761806190453 5893382140460227669330355)
            ·
              refine ⟨8840073210690341503995533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893382140460227669330355 8840073210690341503995533)
              ·
                refine ⟨3315027454008878063998325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8840073210690341503995533 3315027454008878063998325)
                ·
                  refine ⟨310783823813332318499843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3315027454008878063998325 310783823813332318499843)
                  ·
                    rfl

theorem cell23_5447244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_5447244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447244 prefixEnd_5447244 := by exact prefixLift 5447244
  have htrace : WordTrace (prefixWord ++ tailWord_5447244) baseStart_5447244 baseEnd_5447244 := by
    simpa [prefixWord, tailWord_5447244, baseEnd_5447244] using wordTrace_append hprefix tailTrace_5447244
  have hstable : (prefixWord ++ tailWord_5447244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447244).length < 2 ^ (prefixWord ++ tailWord_5447244).sum := by decide
  have hdescent : baseEnd_5447244 < baseStart_5447244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447261 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 7]
def baseStart_5447261 : Nat := 118140960795 + 5447261 * 2 ^ 59
def prefixEnd_5447261 : Nat := 4983230072969 + 3 ^ 40 * 5447261 * 2
def baseEnd_5447261 : Nat := 310784793721235255554001

theorem tailTrace_5447261 : CollatzResearch.WordTrace tailWord_5447261 prefixEnd_5447261 310784793721235255554001 := by
  unfold tailWord_5447261
  simp only [CollatzResearch.WordTrace]
  refine ⟨198677930718511189957501637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132451953812340793305001091 198677930718511189957501637)
  ·
    refine ⟨37252112009720848117031557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198677930718511189957501637 37252112009720848117031557)
    ·
      refine ⟨6984771001822659021943417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37252112009720848117031557 6984771001822659021943417)
      ·
        refine ⟨5238578251366994266457563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6984771001822659021943417 5238578251366994266457563)
        ·
          refine ⟨7857867377050491399686345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5238578251366994266457563 7857867377050491399686345)
          ·
            refine ⟨5893400532787868549764759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7857867377050491399686345 5893400532787868549764759)
            ·
              refine ⟨8840100799181802824647139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893400532787868549764759 8840100799181802824647139)
              ·
                refine ⟨13260151198772704236970709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8840100799181802824647139 13260151198772704236970709)
                ·
                  refine ⟨310784793721235255554001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13260151198772704236970709 310784793721235255554001)
                  ·
                    rfl

theorem cell23_5447261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_5447261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447261 prefixEnd_5447261 := by exact prefixLift 5447261
  have htrace : WordTrace (prefixWord ++ tailWord_5447261) baseStart_5447261 baseEnd_5447261 := by
    simpa [prefixWord, tailWord_5447261, baseEnd_5447261] using wordTrace_append hprefix tailTrace_5447261
  have hstable : (prefixWord ++ tailWord_5447261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447261).length < 2 ^ (prefixWord ++ tailWord_5447261).sum := by decide
  have hdescent : baseEnd_5447261 < baseStart_5447261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447347 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 1, 5]
def baseStart_5447347 : Nat := 118140960795 + 5447347 * 2 ^ 59
def prefixEnd_5447347 : Nat := 4983230072969 + 3 ^ 40 * 5447347 * 2
def baseEnd_5447347 : Nat := 932369100942467987836871

theorem tailTrace_5447347 : CollatzResearch.WordTrace tailWord_5447347 prefixEnd_5447347 932369100942467987836871 := by
  unfold tailWord_5447347
  simp only [CollatzResearch.WordTrace]
  refine ⟨198681067396199626645132295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132454044930799751096754863 198681067396199626645132295)
  ·
    refine ⟨298021601094299439967698443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198681067396199626645132295 298021601094299439967698443)
    ·
      refine ⟨447032401641449159951547665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298021601094299439967698443 447032401641449159951547665)
      ·
        refine ⟨335274301231086869963660749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447032401641449159951547665 335274301231086869963660749)
        ·
          refine ⟨125727862961657576236372781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335274301231086869963660749 125727862961657576236372781)
          ·
            refine ⟨47147948610621591088639793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125727862961657576236372781 47147948610621591088639793)
            ·
              refine ⟨35360961457966193316479845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47147948610621591088639793 35360961457966193316479845)
              ·
                refine ⟨6630180273368661246839971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35360961457966193316479845 6630180273368661246839971)
                ·
                  refine ⟨9945270410052991870259957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6630180273368661246839971 9945270410052991870259957)
                  ·
                    refine ⟨932369100942467987836871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9945270410052991870259957 932369100942467987836871)
                    ·
                      rfl

theorem cell23_5447347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 5].length) (baseStart_5447347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447347 prefixEnd_5447347 := by exact prefixLift 5447347
  have htrace : WordTrace (prefixWord ++ tailWord_5447347) baseStart_5447347 baseEnd_5447347 := by
    simpa [prefixWord, tailWord_5447347, baseEnd_5447347] using wordTrace_append hprefix tailTrace_5447347
  have hstable : (prefixWord ++ tailWord_5447347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447347).length < 2 ^ (prefixWord ++ tailWord_5447347).sum := by decide
  have hdescent : baseEnd_5447347 < baseStart_5447347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447354 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2]
def baseStart_5447354 : Nat := 118140960795 + 5447354 * 2 ^ 59
def prefixEnd_5447354 : Nat := 4983230072969 + 3 ^ 40 * 5447354 * 2
def baseEnd_5447354 : Nat := 2797110897191985436123081

theorem tailTrace_5447354 : CollatzResearch.WordTrace tailWord_5447354 prefixEnd_5447354 2797110897191985436123081 := by
  unfold tailWord_5447354
  simp only [CollatzResearch.WordTrace]
  refine ⟨49670330676793566710159279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132454215138116177893758077 49670330676793566710159279)
  ·
    refine ⟨74505496015190350065238919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49670330676793566710159279 74505496015190350065238919)
    ·
      refine ⟨111758244022785525097858379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74505496015190350065238919 111758244022785525097858379)
      ·
        refine ⟨167637366034178287646787569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111758244022785525097858379 167637366034178287646787569)
        ·
          refine ⟨125728024525633715735090677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167637366034178287646787569 125728024525633715735090677)
          ·
            refine ⟨11787002299278160850164751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125728024525633715735090677 11787002299278160850164751)
            ·
              refine ⟨17680503448917241275247127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11787002299278160850164751 17680503448917241275247127)
              ·
                refine ⟨26520755173375861912870691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17680503448917241275247127 26520755173375861912870691)
                ·
                  refine ⟨39781132760063792869306037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26520755173375861912870691 39781132760063792869306037)
                  ·
                    refine ⟨3729481196255980581497441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39781132760063792869306037 3729481196255980581497441)
                    ·
                      refine ⟨2797110897191985436123081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729481196255980581497441 2797110897191985436123081)
                      ·
                        rfl

theorem cell23_5447354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_5447354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447354 prefixEnd_5447354 := by exact prefixLift 5447354
  have htrace : WordTrace (prefixWord ++ tailWord_5447354) baseStart_5447354 baseEnd_5447354 := by
    simpa [prefixWord, tailWord_5447354, baseEnd_5447354] using wordTrace_append hprefix tailTrace_5447354
  have hstable : (prefixWord ++ tailWord_5447354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447354).length < 2 ^ (prefixWord ++ tailWord_5447354).sum := by decide
  have hdescent : baseEnd_5447354 < baseStart_5447354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447364 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_5447364 : Nat := 118140960795 + 5447364 * 2 ^ 59
def prefixEnd_5447364 : Nat := 4983230072969 + 3 ^ 40 * 5447364 * 2
def baseEnd_5447364 : Nat := 932372010666176798999345

theorem tailTrace_5447364 : CollatzResearch.WordTrace tailWord_5447364 prefixEnd_5447364 932372010666176798999345 := by
  unfold tailWord_5447364
  simp only [CollatzResearch.WordTrace]
  refine ⟨99340843718569019274250573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132454458291425359032334097 99340843718569019274250573)
  ·
    refine ⟨37252816394463382227843965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99340843718569019274250573 37252816394463382227843965)
    ·
      refine ⟨13969806147923768335441487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37252816394463382227843965 13969806147923768335441487)
      ·
        refine ⟨20954709221885652503162231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13969806147923768335441487 20954709221885652503162231)
        ·
          refine ⟨31432063832828478754743347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20954709221885652503162231 31432063832828478754743347)
          ·
            refine ⟨47148095749242718132115021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31432063832828478754743347 47148095749242718132115021)
            ·
              refine ⟨17680535905966019299543133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47148095749242718132115021 17680535905966019299543133)
              ·
                refine ⟨6630200964737257237328675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17680535905966019299543133 6630200964737257237328675)
                ·
                  refine ⟨9945301447105885855993013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6630200964737257237328675 9945301447105885855993013)
                  ·
                    refine ⟨932372010666176798999345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9945301447105885855993013 932372010666176798999345)
                    ·
                      rfl

theorem cell23_5447364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_5447364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447364 prefixEnd_5447364 := by exact prefixLift 5447364
  have htrace : WordTrace (prefixWord ++ tailWord_5447364) baseStart_5447364 baseEnd_5447364 := by
    simpa [prefixWord, tailWord_5447364, baseEnd_5447364] using wordTrace_append hprefix tailTrace_5447364
  have hstable : (prefixWord ++ tailWord_5447364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447364).length < 2 ^ (prefixWord ++ tailWord_5447364).sum := by decide
  have hdescent : baseEnd_5447364 < baseStart_5447364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447378 : List Nat := [3, 2, 2, 2, 2, 1, 2, 4, 1, 1, 3]
def baseStart_5447378 : Nat := 118140960795 + 5447378 * 2 ^ 59
def prefixEnd_5447378 : Nat := 4983230072969 + 3 ^ 40 * 5447378 * 2
def baseEnd_5447378 : Nat := 2797123220727693342222971

theorem tailTrace_5447378 : CollatzResearch.WordTrace tailWord_5447378 prefixEnd_5447378 2797123220727693342222971 := by
  unfold tailWord_5447378
  simp only [CollatzResearch.WordTrace]
  refine ⟨49670549514771829734877697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132454798706058212626340525 49670549514771829734877697)
  ·
    refine ⟨37252912136078872301158273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49670549514771829734877697 37252912136078872301158273)
    ·
      refine ⟨27939684102059154225868705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37252912136078872301158273 27939684102059154225868705)
      ·
        refine ⟨20954763076544365669401529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27939684102059154225868705 20954763076544365669401529)
        ·
          refine ⟨15716072307408274252051147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20954763076544365669401529 15716072307408274252051147)
          ·
            refine ⟨23574108461112411378076721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15716072307408274252051147 23574108461112411378076721)
            ·
              refine ⟨17680581345834308533557541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23574108461112411378076721 17680581345834308533557541)
              ·
                refine ⟨3315109002343932850042039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17680581345834308533557541 3315109002343932850042039)
                ·
                  refine ⟨4972663503515899275063059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3315109002343932850042039 4972663503515899275063059)
                  ·
                    refine ⟨7458995255273848912594589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4972663503515899275063059 7458995255273848912594589)
                    ·
                      refine ⟨2797123220727693342222971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7458995255273848912594589 2797123220727693342222971)
                      ·
                        rfl

theorem cell23_5447378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_5447378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447378 prefixEnd_5447378 := by exact prefixLift 5447378
  have htrace : WordTrace (prefixWord ++ tailWord_5447378) baseStart_5447378 baseEnd_5447378 := by
    simpa [prefixWord, tailWord_5447378, baseEnd_5447378] using wordTrace_append hprefix tailTrace_5447378
  have hstable : (prefixWord ++ tailWord_5447378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447378).length < 2 ^ (prefixWord ++ tailWord_5447378).sum := by decide
  have hdescent : baseEnd_5447378 < baseStart_5447378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447397 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_5447397 : Nat := 118140960795 + 5447397 * 2 ^ 59
def prefixEnd_5447397 : Nat := 4983230072969 + 3 ^ 40 * 5447397 * 2
def baseEnd_5447397 : Nat := 2797132976860128767885383

theorem tailTrace_5447397 : CollatzResearch.WordTrace tailWord_5447397 prefixEnd_5447397 2797132976860128767885383 := by
  unfold tailWord_5447397
  simp only [CollatzResearch.WordTrace]
  refine ⟨198682891046018485184452445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132455260697345656789634963 198682891046018485184452445)
  ·
    refine ⟨74506084142256931944169667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198682891046018485184452445 74506084142256931944169667)
    ·
      refine ⟨111759126213385397916254501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74506084142256931944169667 111759126213385397916254501)
      ·
        refine ⟨20954836165009762109297719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111759126213385397916254501 20954836165009762109297719)
        ·
          refine ⟨31432254247514643163946579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20954836165009762109297719 31432254247514643163946579)
          ·
            refine ⟨47148381371271964745919869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31432254247514643163946579 47148381371271964745919869)
            ·
              refine ⟨17680643014226986779719951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47148381371271964745919869 17680643014226986779719951)
              ·
                refine ⟨26520964521340480169579927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17680643014226986779719951 26520964521340480169579927)
                ·
                  refine ⟨39781446782010720254369891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26520964521340480169579927 39781446782010720254369891)
                  ·
                    refine ⟨59672170173016080381554837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39781446782010720254369891 59672170173016080381554837)
                    ·
                      refine ⟨2797132976860128767885383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59672170173016080381554837 2797132976860128767885383)
                      ·
                        rfl

theorem cell23_5447397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_5447397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447397 prefixEnd_5447397 := by exact prefixLift 5447397
  have htrace : WordTrace (prefixWord ++ tailWord_5447397) baseStart_5447397 baseEnd_5447397 := by
    simpa [prefixWord, tailWord_5447397, baseEnd_5447397] using wordTrace_append hprefix tailTrace_5447397
  have hstable : (prefixWord ++ tailWord_5447397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447397).length < 2 ^ (prefixWord ++ tailWord_5447397).sum := by decide
  have hdescent : baseEnd_5447397 < baseStart_5447397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447404 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 3]
def baseStart_5447404 : Nat := 118140960795 + 5447404 * 2 ^ 59
def prefixEnd_5447404 : Nat := 4983230072969 + 3 ^ 40 * 5447404 * 2
def baseEnd_5447404 : Nat := 2797136571224710240497851

theorem tailTrace_5447404 : CollatzResearch.WordTrace tailWord_5447404 prefixEnd_5447404 2797136571224710240497851 := by
  unfold tailWord_5447404
  simp only [CollatzResearch.WordTrace]
  refine ⟨99341573178496562689978633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132455430904662083586638177 99341573178496562689978633)
  ·
    refine ⟨74506179883872422017483975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99341573178496562689978633 74506179883872422017483975)
    ·
      refine ⟨111759269825808633026225963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74506179883872422017483975 111759269825808633026225963)
      ·
        refine ⟨167638904738712949539338945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111759269825808633026225963 167638904738712949539338945)
        ·
          refine ⟨125729178554034712154504209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167638904738712949539338945 125729178554034712154504209)
          ·
            refine ⟨94296883915526034115878157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125729178554034712154504209 94296883915526034115878157)
            ·
              refine ⟨35361331468322262793454309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94296883915526034115878157 35361331468322262793454309)
              ·
                refine ⟨6630249650310424273772683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35361331468322262793454309 6630249650310424273772683)
                ·
                  refine ⟨9945374475465636410659025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6630249650310424273772683 9945374475465636410659025)
                  ·
                    refine ⟨7459030856599227307994269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9945374475465636410659025 7459030856599227307994269)
                    ·
                      refine ⟨2797136571224710240497851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459030856599227307994269 2797136571224710240497851)
                      ·
                        rfl

theorem cell23_5447404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_5447404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447404 prefixEnd_5447404 := by exact prefixLift 5447404
  have htrace : WordTrace (prefixWord ++ tailWord_5447404) baseStart_5447404 baseEnd_5447404 := by
    simpa [prefixWord, tailWord_5447404, baseEnd_5447404] using wordTrace_append hprefix tailTrace_5447404
  have hstable : (prefixWord ++ tailWord_5447404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447404).length < 2 ^ (prefixWord ++ tailWord_5447404).sum := by decide
  have hdescent : baseEnd_5447404 < baseStart_5447404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447412 : List Nat := [2, 6, 1, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5447412 : Nat := 118140960795 + 5447412 * 2 ^ 59
def prefixEnd_5447412 : Nat := 4983230072969 + 3 ^ 40 * 5447412 * 2
def baseEnd_5447412 : Nat := 2797140679069946209197815

theorem tailTrace_5447412 : CollatzResearch.WordTrace tailWord_5447412 prefixEnd_5447412 2797140679069946209197815 := by
  unfold tailWord_5447412
  simp only [CollatzResearch.WordTrace]
  refine ⟨99341719070482071373124245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132455625427309428497498993 99341719070482071373124245)
  ·
    refine ⟨4656643081428847095615199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99341719070482071373124245 4656643081428847095615199)
    ·
      refine ⟨6984964622143270643422799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4656643081428847095615199 6984964622143270643422799)
      ·
        refine ⟨10477446933214905965134199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6984964622143270643422799 10477446933214905965134199)
        ·
          refine ⟨15716170399822358947701299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10477446933214905965134199 15716170399822358947701299)
          ·
            refine ⟨23574255599733538421551949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15716170399822358947701299 23574255599733538421551949)
            ·
              refine ⟨8840345849900076908081981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23574255599733538421551949 8840345849900076908081981)
              ·
                refine ⟨3315129693712528840530743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8840345849900076908081981 3315129693712528840530743)
                ·
                  refine ⟨4972694540568793260796115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3315129693712528840530743 4972694540568793260796115)
                  ·
                    refine ⟨7459041810853189891194173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4972694540568793260796115 7459041810853189891194173)
                    ·
                      refine ⟨2797140679069946209197815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459041810853189891194173 2797140679069946209197815)
                      ·
                        rfl

theorem cell23_5447412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5447412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447412 prefixEnd_5447412 := by exact prefixLift 5447412
  have htrace : WordTrace (prefixWord ++ tailWord_5447412) baseStart_5447412 baseEnd_5447412 := by
    simpa [prefixWord, tailWord_5447412, baseEnd_5447412] using wordTrace_append hprefix tailTrace_5447412
  have hstable : (prefixWord ++ tailWord_5447412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447412).length < 2 ^ (prefixWord ++ tailWord_5447412).sum := by decide
  have hdescent : baseEnd_5447412 < baseStart_5447412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447461 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 3, 3, 2]
def baseStart_5447461 : Nat := 118140960795 + 5447461 * 2 ^ 59
def prefixEnd_5447461 : Nat := 4983230072969 + 3 ^ 40 * 5447461 * 2
def baseEnd_5447461 : Nat := 2797165839622016517485089

theorem tailTrace_5447461 : CollatzResearch.WordTrace tailWord_5447461 prefixEnd_5447461 2797165839622016517485089 := by
  unfold tailWord_5447461
  simp only [CollatzResearch.WordTrace]
  refine ⟨198685225317786624114782237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132456816878524416076521491 198685225317786624114782237)
  ·
    refine ⟨74506959494169984043043339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198685225317786624114782237 74506959494169984043043339)
    ·
      refine ⟨111760439241254976064565009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74506959494169984043043339 111760439241254976064565009)
      ·
        refine ⟨83820329430941232048423757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111760439241254976064565009 83820329430941232048423757)
        ·
          refine ⟨31432623536602962018158909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83820329430941232048423757 31432623536602962018158909)
          ·
            refine ⟨11787233826226110756809591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31432623536602962018158909 11787233826226110756809591)
            ·
              refine ⟨17680850739339166135214387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11787233826226110756809591 17680850739339166135214387)
              ·
                refine ⟨26521276109008749202821581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17680850739339166135214387 26521276109008749202821581)
                ·
                  refine ⟨9945478540878280951058093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26521276109008749202821581 9945478540878280951058093)
                  ·
                    refine ⟨3729554452829355356646785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9945478540878280951058093 3729554452829355356646785)
                    ·
                      refine ⟨2797165839622016517485089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729554452829355356646785 2797165839622016517485089)
                      ·
                        rfl

theorem cell23_5447461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_5447461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447461 prefixEnd_5447461 := by exact prefixLift 5447461
  have htrace : WordTrace (prefixWord ++ tailWord_5447461) baseStart_5447461 baseEnd_5447461 := by
    simpa [prefixWord, tailWord_5447461, baseEnd_5447461] using wordTrace_append hprefix tailTrace_5447461
  have hstable : (prefixWord ++ tailWord_5447461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447461).length < 2 ^ (prefixWord ++ tailWord_5447461).sum := by decide
  have hdescent : baseEnd_5447461 < baseStart_5447461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447497 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 7]
def baseStart_5447497 : Nat := 118140960795 + 5447497 * 2 ^ 59
def prefixEnd_5447497 : Nat := 4983230072969 + 3 ^ 40 * 5447497 * 2
def baseEnd_5447497 : Nat := 310798258325064264070547

theorem tailTrace_5447497 : CollatzResearch.WordTrace tailWord_5447497 prefixEnd_5447497 310798258325064264070547 := by
  unfold tailWord_5447497
  simp only [CollatzResearch.WordTrace]
  refine ⟨198686538345656202263092745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132457692230437468175395163 198686538345656202263092745)
  ·
    refine ⟨149014903759242151697319559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198686538345656202263092745 149014903759242151697319559)
    ·
      refine ⟨223522355638863227545979339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149014903759242151697319559 223522355638863227545979339)
      ·
        refine ⟨335283533458294841318969009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223522355638863227545979339 335283533458294841318969009)
        ·
          refine ⟨251462650093721130989226757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335283533458294841318969009 251462650093721130989226757)
          ·
            refine ⟨47149246892572712060480017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251462650093721130989226757 47149246892572712060480017)
            ·
              refine ⟨35361935169429534045360013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47149246892572712060480017 35361935169429534045360013)
              ·
                refine ⟨13260725688536075267010005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35361935169429534045360013 13260725688536075267010005)
                ·
                  refine ⟨310798258325064264070547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13260725688536075267010005 310798258325064264070547)
                  ·
                    rfl

theorem cell23_5447497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 7].length) (baseStart_5447497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447497 prefixEnd_5447497 := by exact prefixLift 5447497
  have htrace : WordTrace (prefixWord ++ tailWord_5447497) baseStart_5447497 baseEnd_5447497 := by
    simpa [prefixWord, tailWord_5447497, baseEnd_5447497] using wordTrace_append hprefix tailTrace_5447497
  have hstable : (prefixWord ++ tailWord_5447497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447497).length < 2 ^ (prefixWord ++ tailWord_5447497).sum := by decide
  have hdescent : baseEnd_5447497 < baseStart_5447497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447501 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_5447501 : Nat := 118140960795 + 5447501 * 2 ^ 59
def prefixEnd_5447501 : Nat := 4983230072969 + 3 ^ 40 * 5447501 * 2
def baseEnd_5447501 : Nat := 932395459616065453661635

theorem tailTrace_5447501 : CollatzResearch.WordTrace tailWord_5447501 prefixEnd_5447501 932395459616065453661635 := by
  unfold tailWord_5447501
  simp only [CollatzResearch.WordTrace]
  refine ⟨198686684237641710946238357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132457789491761140630825571 198686684237641710946238357)
  ·
    refine ⟨9313438323639455200604923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198686684237641710946238357 9313438323639455200604923)
    ·
      refine ⟨13970157485459182800907385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9313438323639455200604923 13970157485459182800907385)
      ·
        refine ⟨10477618114094387100680539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13970157485459182800907385 10477618114094387100680539)
        ·
          refine ⟨15716427171141580651020809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10477618114094387100680539 15716427171141580651020809)
          ·
            refine ⟨11787320378356185488265607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15716427171141580651020809 11787320378356185488265607)
            ·
              refine ⟨17680980567534278232398411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11787320378356185488265607 17680980567534278232398411)
              ·
                refine ⟨26521470851301417348597617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17680980567534278232398411 26521470851301417348597617)
                ·
                  refine ⟨19891103138476063011448213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26521470851301417348597617 19891103138476063011448213)
                  ·
                    refine ⟨932395459616065453661635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19891103138476063011448213 932395459616065453661635)
                    ·
                      rfl

theorem cell23_5447501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_5447501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447501 prefixEnd_5447501 := by exact prefixLift 5447501
  have htrace : WordTrace (prefixWord ++ tailWord_5447501) baseStart_5447501 baseEnd_5447501 := by
    simpa [prefixWord, tailWord_5447501, baseEnd_5447501] using wordTrace_append hprefix tailTrace_5447501
  have hstable : (prefixWord ++ tailWord_5447501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447501).length < 2 ^ (prefixWord ++ tailWord_5447501).sum := by decide
  have hdescent : baseEnd_5447501 < baseStart_5447501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447508 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_5447508 : Nat := 118140960795 + 5447508 * 2 ^ 59
def prefixEnd_5447508 : Nat := 4983230072969 + 3 ^ 40 * 5447508 * 2
def baseEnd_5447508 : Nat := 2797189973212777833597373

theorem tailTrace_5447508 : CollatzResearch.WordTrace tailWord_5447508 prefixEnd_5447508 2797189973212777833597373 := by
  unfold tailWord_5447508
  simp only [CollatzResearch.WordTrace]
  refine ⟨99343469774308175570871589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132457959699077567427828785 99343469774308175570871589)
  ·
    refine ⟨18626900582682782919538423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99343469774308175570871589 18626900582682782919538423)
    ·
      refine ⟨27940350874024174379307635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18626900582682782919538423 27940350874024174379307635)
      ·
        refine ⟨41910526311036261568961453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27940350874024174379307635 41910526311036261568961453)
        ·
          refine ⟨15716447366638598088360545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41910526311036261568961453 15716447366638598088360545)
          ·
            refine ⟨11787335524978948566270409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15716447366638598088360545 11787335524978948566270409)
            ·
              refine ⟨8840501643734211424702807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11787335524978948566270409 8840501643734211424702807)
              ·
                refine ⟨13260752465601317137054211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8840501643734211424702807 13260752465601317137054211)
                ·
                  refine ⟨19891128698401975705581317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13260752465601317137054211 19891128698401975705581317)
                  ·
                    refine ⟨3729586630950370444796497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19891128698401975705581317 3729586630950370444796497)
                    ·
                      refine ⟨2797189973212777833597373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729586630950370444796497 2797189973212777833597373)
                      ·
                        rfl

theorem cell23_5447508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_5447508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447508 prefixEnd_5447508 := by exact prefixLift 5447508
  have htrace : WordTrace (prefixWord ++ tailWord_5447508) baseStart_5447508 baseEnd_5447508 := by
    simpa [prefixWord, tailWord_5447508, baseEnd_5447508] using wordTrace_append hprefix tailTrace_5447508
  have hstable : (prefixWord ++ tailWord_5447508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447508).length < 2 ^ (prefixWord ++ tailWord_5447508).sum := by decide
  have hdescent : baseEnd_5447508 < baseStart_5447508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447567 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_5447567 : Nat := 118140960795 + 5447567 * 2 ^ 59
def prefixEnd_5447567 : Nat := 4983230072969 + 3 ^ 40 * 5447567 * 2
def baseEnd_5447567 : Nat := 2797220268571393102759601

theorem tailTrace_5447567 : CollatzResearch.WordTrace tailWord_5447567 prefixEnd_5447567 2797220268571393102759601 := by
  unfold tailWord_5447567
  simp only [CollatzResearch.WordTrace]
  refine ⟨198689091455402604218140955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132459394303601736145427303 198689091455402604218140955)
  ·
    refine ⟨298033637183103906327211433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198689091455402604218140955 298033637183103906327211433)
    ·
      refine ⟨223525227887327929745408575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298033637183103906327211433 223525227887327929745408575)
      ·
        refine ⟨335287841830991894618112863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223525227887327929745408575 335287841830991894618112863)
        ·
          refine ⟨502931762746487841927169295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335287841830991894618112863 502931762746487841927169295)
          ·
            refine ⟨754397644119731762890753943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502931762746487841927169295 754397644119731762890753943)
            ·
              refine ⟨1131596466179597644336130915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754397644119731762890753943 1131596466179597644336130915)
              ·
                refine ⟨1697394699269396466504196373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131596466179597644336130915 1697394699269396466504196373)
                ·
                  refine ⟨79565376528252959367384205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1697394699269396466504196373 79565376528252959367384205)
                  ·
                    refine ⟨29837016198094859762769077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79565376528252959367384205 29837016198094859762769077)
                    ·
                      refine ⟨2797220268571393102759601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29837016198094859762769077 2797220268571393102759601)
                      ·
                        rfl

theorem cell23_5447567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_5447567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447567 prefixEnd_5447567 := by exact prefixLift 5447567
  have htrace : WordTrace (prefixWord ++ tailWord_5447567) baseStart_5447567 baseEnd_5447567 := by
    simpa [prefixWord, tailWord_5447567, baseEnd_5447567] using wordTrace_append hprefix tailTrace_5447567
  have hstable : (prefixWord ++ tailWord_5447567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447567).length < 2 ^ (prefixWord ++ tailWord_5447567).sum := by decide
  have hdescent : baseEnd_5447567 < baseStart_5447567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447582 : List Nat := [4, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_5447582 : Nat := 118140960795 + 5447582 * 2 ^ 59
def prefixEnd_5447582 : Nat := 4983230072969 + 3 ^ 40 * 5447582 * 2
def baseEnd_5447582 : Nat := 310803107864578949341337

theorem tailTrace_5447582 : CollatzResearch.WordTrace tailWord_5447582 prefixEnd_5447582 310803107864578949341337 := by
  unfold tailWord_5447582
  simp only [CollatzResearch.WordTrace]
  refine ⟨24836204818793532722492125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132459759033565507853291333 24836204818793532722492125)
  ·
    refine ⟨9313576807047574770934547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24836204818793532722492125 9313576807047574770934547)
    ·
      refine ⟨13970365210571362156401821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9313576807047574770934547 13970365210571362156401821)
      ·
        refine ⟨5238886953964260808650683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13970365210571362156401821 5238886953964260808650683)
        ·
          refine ⟨7858330430946391212976025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5238886953964260808650683 7858330430946391212976025)
          ·
            refine ⟨5893747823209793409732019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7858330430946391212976025 5893747823209793409732019)
            ·
              refine ⟨8840621734814690114598029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893747823209793409732019 8840621734814690114598029)
              ·
                refine ⟨3315233150555508792974261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8840621734814690114598029 3315233150555508792974261)
                ·
                  refine ⟨310803107864578949341337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3315233150555508792974261 310803107864578949341337)
                  ·
                    rfl

theorem cell23_5447582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_5447582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447582 prefixEnd_5447582 := by exact prefixLift 5447582
  have htrace : WordTrace (prefixWord ++ tailWord_5447582) baseStart_5447582 baseEnd_5447582 := by
    simpa [prefixWord, tailWord_5447582, baseEnd_5447582] using wordTrace_append hprefix tailTrace_5447582
  have hstable : (prefixWord ++ tailWord_5447582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447582).length < 2 ^ (prefixWord ++ tailWord_5447582).sum := by decide
  have hdescent : baseEnd_5447582 < baseStart_5447582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447601 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_5447601 : Nat := 118140960795 + 5447601 * 2 ^ 59
def prefixEnd_5447601 : Nat := 4983230072969 + 3 ^ 40 * 5447601 * 2
def baseEnd_5447601 : Nat := 2797237726913645969734445

theorem tailTrace_5447601 : CollatzResearch.WordTrace tailWord_5447601 prefixEnd_5447601 2797237726913645969734445 := by
  unfold tailWord_5447601
  simp only [CollatzResearch.WordTrace]
  refine ⟨198690331537279428024878657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132460221024852952016585771 198690331537279428024878657)
  ·
    refine ⟨149017748652959571018658993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198690331537279428024878657 149017748652959571018658993)
    ·
      refine ⟨111763311489719678263994245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149017748652959571018658993 111763311489719678263994245)
      ·
        refine ⟨20955620904322439674498921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111763311489719678263994245 20955620904322439674498921)
        ·
          refine ⟨15716715678241829755874191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20955620904322439674498921 15716715678241829755874191)
          ·
            refine ⟨23575073517362744633811287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15716715678241829755874191 23575073517362744633811287)
            ·
              refine ⟨35362610276044116950716931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23575073517362744633811287 35362610276044116950716931)
              ·
                refine ⟨53043915414066175426075397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35362610276044116950716931 53043915414066175426075397)
                ·
                  refine ⟨9945734140137407892389137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53043915414066175426075397 9945734140137407892389137)
                  ·
                    refine ⟨7459300605103055919291853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9945734140137407892389137 7459300605103055919291853)
                    ·
                      refine ⟨2797237726913645969734445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459300605103055919291853 2797237726913645969734445)
                      ·
                        rfl

theorem cell23_5447601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_5447601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447601 prefixEnd_5447601 := by exact prefixLift 5447601
  have htrace : WordTrace (prefixWord ++ tailWord_5447601) baseStart_5447601 baseEnd_5447601 := by
    simpa [prefixWord, tailWord_5447601, baseEnd_5447601] using wordTrace_append hprefix tailTrace_5447601
  have hstable : (prefixWord ++ tailWord_5447601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447601).length < 2 ^ (prefixWord ++ tailWord_5447601).sum := by decide
  have hdescent : baseEnd_5447601 < baseStart_5447601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447631 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 3]
def baseStart_5447631 : Nat := 118140960795 + 5447631 * 2 ^ 59
def prefixEnd_5447631 : Nat := 4983230072969 + 3 ^ 40 * 5447631 * 2
def baseEnd_5447631 : Nat := 2797253131333280852359307

theorem tailTrace_5447631 : CollatzResearch.WordTrace tailWord_5447631 prefixEnd_5447631 2797253131333280852359307 := by
  unfold tailWord_5447631
  simp only [CollatzResearch.WordTrace]
  refine ⟨198691425727170743148470747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132460950484780495432313831 198691425727170743148470747)
  ·
    refine ⟨298037138590756114722706121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198691425727170743148470747 298037138590756114722706121)
    ·
      refine ⟨223527853943067086042029591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298037138590756114722706121 223527853943067086042029591)
      ·
        refine ⟨335291780914600629063044387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223527853943067086042029591 335291780914600629063044387)
        ·
          refine ⟨502937671371900943594566581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335291780914600629063044387 502937671371900943594566581)
          ·
            refine ⟨47150406691115713461990617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 502937671371900943594566581 47150406691115713461990617)
            ·
              refine ⟨35362805018336785096492963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47150406691115713461990617 35362805018336785096492963)
              ·
                refine ⟨53044207527505177644739445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35362805018336785096492963 53044207527505177644739445)
                ·
                  refine ⟨4972894455703610404194323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53044207527505177644739445 4972894455703610404194323)
                  ·
                    refine ⟨7459341683555415606291485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4972894455703610404194323 7459341683555415606291485)
                    ·
                      refine ⟨2797253131333280852359307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459341683555415606291485 2797253131333280852359307)
                      ·
                        rfl

theorem cell23_5447631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 3].length) (baseStart_5447631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447631 prefixEnd_5447631 := by exact prefixLift 5447631
  have htrace : WordTrace (prefixWord ++ tailWord_5447631) baseStart_5447631 baseEnd_5447631 := by
    simpa [prefixWord, tailWord_5447631, baseEnd_5447631] using wordTrace_append hprefix tailTrace_5447631
  have hstable : (prefixWord ++ tailWord_5447631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447631).length < 2 ^ (prefixWord ++ tailWord_5447631).sum := by decide
  have hdescent : baseEnd_5447631 < baseStart_5447631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447658 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_5447658 : Nat := 118140960795 + 5447658 * 2 ^ 59
def prefixEnd_5447658 : Nat := 4983230072969 + 3 ^ 40 * 5447658 * 2
def baseEnd_5447658 : Nat := 2797266995310952246721683

theorem tailTrace_5447658 : CollatzResearch.WordTrace tailWord_5447658 prefixEnd_5447658 2797266995310952246721683 := by
  unfold tailWord_5447658
  simp only [CollatzResearch.WordTrace]
  refine ⟨49673102624518231689925907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132461606998715284506469085 49673102624518231689925907)
  ·
    refine ⟨74509653936777347534888861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49673102624518231689925907 74509653936777347534888861)
    ·
      refine ⟨27941120226291505325583323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74509653936777347534888861 27941120226291505325583323)
      ·
        refine ⟨41911680339437257988374985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27941120226291505325583323 41911680339437257988374985)
        ·
          refine ⟨31433760254577943491281239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41911680339437257988374985 31433760254577943491281239)
          ·
            refine ⟨47150640381866915236921859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31433760254577943491281239 47150640381866915236921859)
            ·
              refine ⟨70725960572800372855382789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47150640381866915236921859 70725960572800372855382789)
              ·
                refine ⟨13261117607400069910384273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70725960572800372855382789 13261117607400069910384273)
                ·
                  refine ⟨9945838205550052432788205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13261117607400069910384273 9945838205550052432788205)
                  ·
                    refine ⟨3729689327081269662295577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9945838205550052432788205 3729689327081269662295577)
                    ·
                      refine ⟨2797266995310952246721683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729689327081269662295577 2797266995310952246721683)
                      ·
                        rfl

theorem cell23_5447658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_5447658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447658 prefixEnd_5447658 := by exact prefixLift 5447658
  have htrace : WordTrace (prefixWord ++ tailWord_5447658) baseStart_5447658 baseEnd_5447658 := by
    simpa [prefixWord, tailWord_5447658, baseEnd_5447658] using wordTrace_append hprefix tailTrace_5447658
  have hstable : (prefixWord ++ tailWord_5447658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447658).length < 2 ^ (prefixWord ++ tailWord_5447658).sum := by decide
  have hdescent : baseEnd_5447658 < baseStart_5447658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447681 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 1, 6]
def baseStart_5447681 : Nat := 118140960795 + 5447681 * 2 ^ 59
def prefixEnd_5447681 : Nat := 4983230072969 + 3 ^ 40 * 5447681 * 2
def baseEnd_5447681 : Nat := 932426268455335218911359

theorem tailTrace_5447681 : CollatzResearch.WordTrace tailWord_5447681 prefixEnd_5447681 932426268455335218911359 := by
  unfold tailWord_5447681
  simp only [CollatzResearch.WordTrace]
  refine ⟨198693249376989601687790897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132462166251326401125193931 198693249376989601687790897)
  ·
    refine ⟨149019937032742201265843173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198693249376989601687790897 149019937032742201265843173)
    ·
      refine ⟨27941238193639162737345595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149019937032742201265843173 27941238193639162737345595)
      ·
        refine ⟨41911857290458744106018393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27941238193639162737345595 41911857290458744106018393)
        ·
          refine ⟨31433892967844058079513795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41911857290458744106018393 31433892967844058079513795)
          ·
            refine ⟨47150839451766087119270693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31433892967844058079513795 47150839451766087119270693)
            ·
              refine ⟨8840782397206141334863255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47150839451766087119270693 8840782397206141334863255)
              ·
                refine ⟨13261173595809212002294883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8840782397206141334863255 13261173595809212002294883)
                ·
                  refine ⟨19891760393713818003442325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13261173595809212002294883 19891760393713818003442325)
                  ·
                    refine ⟨932426268455335218911359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19891760393713818003442325 932426268455335218911359)
                    ·
                      rfl

theorem cell23_5447681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_5447681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447681 prefixEnd_5447681 := by exact prefixLift 5447681
  have htrace : WordTrace (prefixWord ++ tailWord_5447681) baseStart_5447681 baseEnd_5447681 := by
    simpa [prefixWord, tailWord_5447681, baseEnd_5447681] using wordTrace_append hprefix tailTrace_5447681
  have hstable : (prefixWord ++ tailWord_5447681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447681).length < 2 ^ (prefixWord ++ tailWord_5447681).sum := by decide
  have hdescent : baseEnd_5447681 < baseStart_5447681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447686 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5447686 : Nat := 118140960795 + 5447686 * 2 ^ 59
def prefixEnd_5447686 : Nat := 4983230072969 + 3 ^ 40 * 5447686 * 2
def baseEnd_5447686 : Nat := 2797281372769278137171555

theorem tailTrace_5447686 : CollatzResearch.WordTrace tailWord_5447686 prefixEnd_5447686 2797281372769278137171555 := by
  unfold tailWord_5447686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6209169741936608985678841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132462287827980991694481941 6209169741936608985678841)
  ·
    refine ⟨4656877306452456739259131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6209169741936608985678841 4656877306452456739259131)
    ·
      refine ⟨6985315959678685108888697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4656877306452456739259131 6985315959678685108888697)
      ·
        refine ⟨5238986969759013831666523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6985315959678685108888697 5238986969759013831666523)
        ·
          refine ⟨7858480454638520747499785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5238986969759013831666523 7858480454638520747499785)
          ·
            refine ⟨5893860340978890560624839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7858480454638520747499785 5893860340978890560624839)
            ·
              refine ⟨8840790511468335840937259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893860340978890560624839 8840790511468335840937259)
              ·
                refine ⟨13261185767202503761405889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8840790511468335840937259 13261185767202503761405889)
                ·
                  refine ⟨9945889325401877821054417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13261185767202503761405889 9945889325401877821054417)
                  ·
                    refine ⟨7459416994051408365790813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9945889325401877821054417 7459416994051408365790813)
                    ·
                      refine ⟨2797281372769278137171555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459416994051408365790813 2797281372769278137171555)
                      ·
                        rfl

theorem cell23_5447686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5447686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447686 prefixEnd_5447686 := by exact prefixLift 5447686
  have htrace : WordTrace (prefixWord ++ tailWord_5447686) baseStart_5447686 baseEnd_5447686 := by
    simpa [prefixWord, tailWord_5447686, baseEnd_5447686] using wordTrace_append hprefix tailTrace_5447686
  have hstable : (prefixWord ++ tailWord_5447686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447686).length < 2 ^ (prefixWord ++ tailWord_5447686).sum := by decide
  have hdescent : baseEnd_5447686 < baseStart_5447686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447691 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 3]
def baseStart_5447691 : Nat := 118140960795 + 5447691 * 2 ^ 59
def prefixEnd_5447691 : Nat := 4983230072969 + 3 ^ 40 * 5447691 * 2
def baseEnd_5447691 : Nat := 2797283940172550617609031

theorem tailTrace_5447691 : CollatzResearch.WordTrace tailWord_5447691 prefixEnd_5447691 2797283940172550617609031 := by
  unfold tailWord_5447691
  simp only [CollatzResearch.WordTrace]
  refine ⟨198693614106953373395654927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132462409404635582263769951 198693614106953373395654927)
  ·
    refine ⟨298040421160430060093482391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198693614106953373395654927 298040421160430060093482391)
    ·
      refine ⟨447060631740645090140223587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298040421160430060093482391 447060631740645090140223587)
      ·
        refine ⟨670590947610967635210335381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447060631740645090140223587 670590947610967635210335381)
        ·
          refine ⟨31433950669264107900484471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 670590947610967635210335381 31433950669264107900484471)
          ·
            refine ⟨47150926003896161850726707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31433950669264107900484471 47150926003896161850726707)
            ·
              refine ⟨70726389005844242776090061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47150926003896161850726707 70726389005844242776090061)
              ·
                refine ⟨26522395877191591041033773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70726389005844242776090061 26522395877191591041033773)
                ·
                  refine ⟨9945898453946846640387665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26522395877191591041033773 9945898453946846640387665)
                  ·
                    refine ⟨7459423840460134980290749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9945898453946846640387665 7459423840460134980290749)
                    ·
                      refine ⟨2797283940172550617609031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459423840460134980290749 2797283940172550617609031)
                      ·
                        rfl

theorem cell23_5447691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 3].length) (baseStart_5447691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447691 prefixEnd_5447691 := by exact prefixLift 5447691
  have htrace : WordTrace (prefixWord ++ tailWord_5447691) baseStart_5447691 baseEnd_5447691 := by
    simpa [prefixWord, tailWord_5447691, baseEnd_5447691] using wordTrace_append hprefix tailTrace_5447691
  have hstable : (prefixWord ++ tailWord_5447691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447691).length < 2 ^ (prefixWord ++ tailWord_5447691).sum := by decide
  have hdescent : baseEnd_5447691 < baseStart_5447691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447722 : List Nat := [3, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_5447722 : Nat := 118140960795 + 5447722 * 2 ^ 59
def prefixEnd_5447722 : Nat := 4983230072969 + 3 ^ 40 * 5447722 * 2
def baseEnd_5447722 : Nat := 2797299858072839996321389

theorem tailTrace_5447722 : CollatzResearch.WordTrace tailWord_5447722 prefixEnd_5447722 2797299858072839996321389 := by
  unfold tailWord_5447722
  simp only [CollatzResearch.WordTrace]
  refine ⟨49673686192460266422508355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132463163179894043793355613 49673686192460266422508355)
  ·
    refine ⟨74510529288690399633762533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49673686192460266422508355 74510529288690399633762533)
    ·
      refine ⟨13970724241629449931330475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74510529288690399633762533 13970724241629449931330475)
      ·
        refine ⟨20956086362444174896995713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13970724241629449931330475 20956086362444174896995713)
        ·
          refine ⟨15717064771833131172746785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20956086362444174896995713 15717064771833131172746785)
          ·
            refine ⟨11787798578874848379560089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15717064771833131172746785 11787798578874848379560089)
            ·
              refine ⟨8840848934156136284670067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11787798578874848379560089 8840848934156136284670067)
              ·
                refine ⟨13261273401234204427005101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8840848934156136284670067 13261273401234204427005101)
                ·
                  refine ⟨4972977525462826660126913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13261273401234204427005101 4972977525462826660126913)
                  ·
                    refine ⟨3729733144097119995095185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4972977525462826660126913 3729733144097119995095185)
                    ·
                      refine ⟨2797299858072839996321389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729733144097119995095185 2797299858072839996321389)
                      ·
                        rfl

theorem cell23_5447722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_5447722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447722 prefixEnd_5447722 := by exact prefixLift 5447722
  have htrace : WordTrace (prefixWord ++ tailWord_5447722) baseStart_5447722 baseEnd_5447722 := by
    simpa [prefixWord, tailWord_5447722, baseEnd_5447722] using wordTrace_append hprefix tailTrace_5447722
  have hstable : (prefixWord ++ tailWord_5447722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447722).length < 2 ^ (prefixWord ++ tailWord_5447722).sum := by decide
  have hdescent : baseEnd_5447722 < baseStart_5447722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447724 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_5447724 : Nat := 118140960795 + 5447724 * 2 ^ 59
def prefixEnd_5447724 : Nat := 4983230072969 + 3 ^ 40 * 5447724 * 2
def baseEnd_5447724 : Nat := 932433628344716329498793

theorem tailTrace_5447724 : CollatzResearch.WordTrace tailWord_5447724 prefixEnd_5447724 932433628344716329498793 := by
  unfold tailWord_5447724
  simp only [CollatzResearch.WordTrace]
  refine ⟨99347408857916910015803113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132463211810555880021070817 99347408857916910015803113)
  ·
    refine ⟨74510556643437682511852335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99347408857916910015803113 74510556643437682511852335)
    ·
      refine ⟨111765834965156523767778503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74510556643437682511852335 111765834965156523767778503)
      ·
        refine ⟨167648752447734785651667755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111765834965156523767778503 167648752447734785651667755)
        ·
          refine ⟨251473128671602178477501633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167648752447734785651667755 251473128671602178477501633)
          ·
            refine ⟨188604846503701633858126225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251473128671602178477501633 188604846503701633858126225)
            ·
              refine ⟨141453634877776225393594669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188604846503701633858126225 141453634877776225393594669)
              ·
                refine ⟨53045113079166084522598001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141453634877776225393594669 53045113079166084522598001)
                ·
                  refine ⟨39783834809374563391948501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53045113079166084522598001 39783834809374563391948501)
                  ·
                    refine ⟨932433628344716329498793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39783834809374563391948501 932433628344716329498793)
                    ·
                      rfl

theorem cell23_5447724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_5447724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447724 prefixEnd_5447724 := by exact prefixLift 5447724
  have htrace : WordTrace (prefixWord ++ tailWord_5447724) baseStart_5447724 baseEnd_5447724 := by
    simpa [prefixWord, tailWord_5447724, baseEnd_5447724] using wordTrace_append hprefix tailTrace_5447724
  have hstable : (prefixWord ++ tailWord_5447724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447724).length < 2 ^ (prefixWord ++ tailWord_5447724).sum := by decide
  have hdescent : baseEnd_5447724 < baseStart_5447724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447732 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_5447732 : Nat := 118140960795 + 5447732 * 2 ^ 59
def prefixEnd_5447732 : Nat := 4983230072969 + 3 ^ 40 * 5447732 * 2
def baseEnd_5447732 : Nat := 932434997626461652398781

theorem tailTrace_5447732 : CollatzResearch.WordTrace tailWord_5447732 prefixEnd_5447732 932434997626461652398781 := by
  unfold tailWord_5447732
  simp only [CollatzResearch.WordTrace]
  refine ⟨99347554749902418698948725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132463406333203224931931633 99347554749902418698948725)
  ·
    refine ⟨9313833257803351753026443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99347554749902418698948725 9313833257803351753026443)
    ·
      refine ⟨13970749886705027629539665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9313833257803351753026443 13970749886705027629539665)
      ·
        refine ⟨10478062415028770722154749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13970749886705027629539665 10478062415028770722154749)
        ·
          refine ⟨3929273405635789020808031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10478062415028770722154749 3929273405635789020808031)
          ·
            refine ⟨5893910108453683531212047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929273405635789020808031 5893910108453683531212047)
            ·
              refine ⟨8840865162680525296818071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5893910108453683531212047 8840865162680525296818071)
              ·
                refine ⟨13261297744020787945227107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8840865162680525296818071 13261297744020787945227107)
                ·
                  refine ⟨19891946616031181917840661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13261297744020787945227107 19891946616031181917840661)
                  ·
                    refine ⟨932434997626461652398781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19891946616031181917840661 932434997626461652398781)
                    ·
                      rfl

theorem cell23_5447732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_5447732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447732 prefixEnd_5447732 := by exact prefixLift 5447732
  have htrace : WordTrace (prefixWord ++ tailWord_5447732) baseStart_5447732 baseEnd_5447732 := by
    simpa [prefixWord, tailWord_5447732, baseEnd_5447732] using wordTrace_append hprefix tailTrace_5447732
  have hstable : (prefixWord ++ tailWord_5447732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447732).length < 2 ^ (prefixWord ++ tailWord_5447732).sum := by decide
  have hdescent : baseEnd_5447732 < baseStart_5447732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447742 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_5447742 : Nat := 118140960795 + 5447742 * 2 ^ 59
def prefixEnd_5447742 : Nat := 4983230072969 + 3 ^ 40 * 5447742 * 2
def baseEnd_5447742 : Nat := 2797310127685929918071297

theorem tailTrace_5447742 : CollatzResearch.WordTrace tailWord_5447742 prefixEnd_5447742 2797310127685929918071297 := by
  unfold tailWord_5447742
  simp only [CollatzResearch.WordTrace]
  refine ⟨24836934278721076138220185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132463649486512406070507653 24836934278721076138220185)
  ·
    refine ⟨18627700709040807103665139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24836934278721076138220185 18627700709040807103665139)
    ·
      refine ⟨27941551063561210655497709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18627700709040807103665139 27941551063561210655497709)
      ·
        refine ⟨10478081648835453995811641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27941551063561210655497709 10478081648835453995811641)
        ·
          refine ⟨7858561236626590496858731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10478081648835453995811641 7858561236626590496858731)
          ·
            refine ⟨11787841854939885745288097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7858561236626590496858731 11787841854939885745288097)
            ·
              refine ⟨8840881391204914308966073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11787841854939885745288097 8840881391204914308966073)
              ·
                refine ⟨6630661043403685731724555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8840881391204914308966073 6630661043403685731724555)
                ·
                  refine ⟨9945991565105528597586833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6630661043403685731724555 9945991565105528597586833)
                  ·
                    refine ⟨7459493673829146448190125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9945991565105528597586833 7459493673829146448190125)
                    ·
                      refine ⟨2797310127685929918071297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459493673829146448190125 2797310127685929918071297)
                      ·
                        rfl

theorem cell23_5447742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_5447742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447742 prefixEnd_5447742 := by exact prefixLift 5447742
  have htrace : WordTrace (prefixWord ++ tailWord_5447742) baseStart_5447742 baseEnd_5447742 := by
    simpa [prefixWord, tailWord_5447742, baseEnd_5447742] using wordTrace_append hprefix tailTrace_5447742
  have hstable : (prefixWord ++ tailWord_5447742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447742).length < 2 ^ (prefixWord ++ tailWord_5447742).sum := by decide
  have hdescent : baseEnd_5447742 < baseStart_5447742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447765 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 1, 3, 2]
def baseStart_5447765 : Nat := 118140960795 + 5447765 * 2 ^ 59
def prefixEnd_5447765 : Nat := 4983230072969 + 3 ^ 40 * 5447765 * 2
def baseEnd_5447765 : Nat := 2797321937740983328083691

theorem tailTrace_5447765 : CollatzResearch.WordTrace tailWord_5447765 prefixEnd_5447765 2797321937740983328083691 := by
  unfold tailWord_5447765
  simp only [CollatzResearch.WordTrace]
  refine ⟨198696313108685284033848749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132464208739123522689232499 198696313108685284033848749)
  ·
    refine ⟨74511117415756981512693281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198696313108685284033848749 74511117415756981512693281)
    ·
      refine ⟨55883338061817736134519961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74511117415756981512693281 55883338061817736134519961)
      ·
        refine ⟨41912503546363302100889971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55883338061817736134519961 41912503546363302100889971)
        ·
          refine ⟨62868755319544953151334957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41912503546363302100889971 62868755319544953151334957)
          ·
            refine ⟨23575783244829357431750609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62868755319544953151334957 23575783244829357431750609)
            ·
              refine ⟨17681837433622018073812957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23575783244829357431750609 17681837433622018073812957)
              ·
                refine ⟨6630689037608256777679859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17681837433622018073812957 6630689037608256777679859)
                ·
                  refine ⟨9946033556412385166519789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6630689037608256777679859 9946033556412385166519789)
                  ·
                    refine ⟨3729762583654644437444921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9946033556412385166519789 3729762583654644437444921)
                    ·
                      refine ⟨2797321937740983328083691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729762583654644437444921 2797321937740983328083691)
                      ·
                        rfl

theorem cell23_5447765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_5447765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447765 prefixEnd_5447765 := by exact prefixLift 5447765
  have htrace : WordTrace (prefixWord ++ tailWord_5447765) baseStart_5447765 baseEnd_5447765 := by
    simpa [prefixWord, tailWord_5447765, baseEnd_5447765] using wordTrace_append hprefix tailTrace_5447765
  have hstable : (prefixWord ++ tailWord_5447765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447765).length < 2 ^ (prefixWord ++ tailWord_5447765).sum := by decide
  have hdescent : baseEnd_5447765 < baseStart_5447765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447798 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5447798 : Nat := 118140960795 + 5447798 * 2 ^ 59
def prefixEnd_5447798 : Nat := 4983230072969 + 3 ^ 40 * 5447798 * 2
def baseEnd_5447798 : Nat := 2797338882602581698971039

theorem tailTrace_5447798 : CollatzResearch.WordTrace tailWord_5447798 prefixEnd_5447798 2797338882602581698971039 := by
  unfold tailWord_5447798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12418594794847858166862503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132465011145043820446533365 12418594794847858166862503)
  ·
    refine ⟨18627892192271787250293755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12418594794847858166862503 18627892192271787250293755)
    ·
      refine ⟨27941838288407680875440633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18627892192271787250293755 27941838288407680875440633)
      ·
        refine ⟨20956378716305760656580475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27941838288407680875440633 20956378716305760656580475)
        ·
          refine ⟨31434568074458640984870713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20956378716305760656580475 31434568074458640984870713)
          ·
            refine ⟨23575926055843980738653035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31434568074458640984870713 23575926055843980738653035)
            ·
              refine ⟨35363889083765971107979553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23575926055843980738653035 35363889083765971107979553)
              ·
                refine ⟨26522916812824478330984665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35363889083765971107979553 26522916812824478330984665)
                ·
                  refine ⟨19892187609618358748238499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26522916812824478330984665 19892187609618358748238499)
                  ·
                    refine ⟨29838281414427538122357749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19892187609618358748238499 29838281414427538122357749)
                    ·
                      refine ⟨2797338882602581698971039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29838281414427538122357749 2797338882602581698971039)
                      ·
                        rfl

theorem cell23_5447798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5447798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447798 prefixEnd_5447798 := by exact prefixLift 5447798
  have htrace : WordTrace (prefixWord ++ tailWord_5447798) baseStart_5447798 baseEnd_5447798 := by
    simpa [prefixWord, tailWord_5447798, baseEnd_5447798] using wordTrace_append hprefix tailTrace_5447798
  have hstable : (prefixWord ++ tailWord_5447798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447798).length < 2 ^ (prefixWord ++ tailWord_5447798).sum := by decide
  have hdescent : baseEnd_5447798 < baseStart_5447798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447918 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_5447918 : Nat := 118140960795 + 5447918 * 2 ^ 59
def prefixEnd_5447918 : Nat := 4983230072969 + 3 ^ 40 * 5447918 * 2
def baseEnd_5447918 : Nat := 2797400500281121229470487

theorem tailTrace_5447918 : CollatzResearch.WordTrace tailWord_5447918 prefixEnd_5447918 2797400500281121229470487 := by
  unfold tailWord_5447918
  simp only [CollatzResearch.WordTrace]
  refine ⟨24837736684641373895521051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132467928984753994109445605 24837736684641373895521051)
  ·
    refine ⟨37256605026962060843281577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24837736684641373895521051 37256605026962060843281577)
    ·
      refine ⟨27942453770221545632461183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37256605026962060843281577 27942453770221545632461183)
      ·
        refine ⟨41913680655332318448691775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27942453770221545632461183 41913680655332318448691775)
        ·
          refine ⟨62870520982998477673037663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41913680655332318448691775 62870520982998477673037663)
          ·
            refine ⟨94305781474497716509556495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62870520982998477673037663 94305781474497716509556495)
            ·
              refine ⟨141458672211746574764334743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94305781474497716509556495 141458672211746574764334743)
              ·
                refine ⟨212188008317619862146502115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141458672211746574764334743 212188008317619862146502115)
                ·
                  refine ⟨318282012476429793219753173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212188008317619862146502115 318282012476429793219753173)
                  ·
                    refine ⟨7459734667416323278587965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 318282012476429793219753173 7459734667416323278587965)
                    ·
                      refine ⟨2797400500281121229470487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459734667416323278587965 2797400500281121229470487)
                      ·
                        rfl

theorem cell23_5447918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_5447918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447918 prefixEnd_5447918 := by exact prefixLift 5447918
  have htrace : WordTrace (prefixWord ++ tailWord_5447918) baseStart_5447918 baseEnd_5447918 := by
    simpa [prefixWord, tailWord_5447918, baseEnd_5447918] using wordTrace_append hprefix tailTrace_5447918
  have hstable : (prefixWord ++ tailWord_5447918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447918).length < 2 ^ (prefixWord ++ tailWord_5447918).sum := by decide
  have hdescent : baseEnd_5447918 < baseStart_5447918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447945 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 4, 3, 2]
def baseStart_5447945 : Nat := 118140960795 + 5447945 * 2 ^ 59
def prefixEnd_5447945 : Nat := 4983230072969 + 3 ^ 40 * 5447945 * 2
def baseEnd_5447945 : Nat := 2797414364258792623832863

theorem tailTrace_5447945 : CollatzResearch.WordTrace tailWord_5447945 prefixEnd_5447945 2797414364258792623832863 := by
  unfold tailWord_5447945
  simp only [CollatzResearch.WordTrace]
  refine ⟨198702878248033174775401289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132468585498688783183600859 198702878248033174775401289)
  ·
    refine ⟨149027158686024881081550967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198702878248033174775401289 149027158686024881081550967)
    ·
      refine ⟨223540738029037321622326451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149027158686024881081550967 223540738029037321622326451)
      ·
        refine ⟨335311107043555982433489677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223540738029037321622326451 335311107043555982433489677)
        ·
          refine ⟨125741665141333493412558629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335311107043555982433489677 125741665141333493412558629)
          ·
            refine ⟨23576562214000030014854743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125741665141333493412558629 23576562214000030014854743)
            ·
              refine ⟨35364843321000045022282115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23576562214000030014854743 35364843321000045022282115)
              ·
                refine ⟨53047264981500067533423173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35364843321000045022282115 53047264981500067533423173)
                ·
                  refine ⟨9946362184031262662516845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53047264981500067533423173 9946362184031262662516845)
                  ·
                    refine ⟨3729885819011723498443817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9946362184031262662516845 3729885819011723498443817)
                    ·
                      refine ⟨2797414364258792623832863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3729885819011723498443817 2797414364258792623832863)
                      ·
                        rfl

theorem cell23_5447945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 3, 2].length) (baseStart_5447945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447945 prefixEnd_5447945 := by exact prefixLift 5447945
  have htrace : WordTrace (prefixWord ++ tailWord_5447945) baseStart_5447945 baseEnd_5447945 := by
    simpa [prefixWord, tailWord_5447945, baseEnd_5447945] using wordTrace_append hprefix tailTrace_5447945
  have hstable : (prefixWord ++ tailWord_5447945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447945).length < 2 ^ (prefixWord ++ tailWord_5447945).sum := by decide
  have hdescent : baseEnd_5447945 < baseStart_5447945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447972 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_5447972 : Nat := 118140960795 + 5447972 * 2 ^ 59
def prefixEnd_5447972 : Nat := 4983230072969 + 3 ^ 40 * 5447972 * 2
def baseEnd_5447972 : Nat := 932476076078821339398413

theorem tailTrace_5447972 : CollatzResearch.WordTrace tailWord_5447972 prefixEnd_5447972 932476076078821339398413 := by
  unfold tailWord_5447972
  simp only [CollatzResearch.WordTrace]
  refine ⟨99351931509467679193317085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132469242012623572257756113 99351931509467679193317085)
  ·
    refine ⟨37256974316050379697493907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99351931509467679193317085 37256974316050379697493907)
    ·
      refine ⟨55885461474075569546240861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37256974316050379697493907 55885461474075569546240861)
      ·
        refine ⟨20957048052778338579840323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55885461474075569546240861 20957048052778338579840323)
        ·
          refine ⟨31435572079167507869760485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20957048052778338579840323 31435572079167507869760485)
          ·
            refine ⟨5894169764843907725580091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31435572079167507869760485 5894169764843907725580091)
            ·
              refine ⟨8841254647265861588370137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894169764843907725580091 8841254647265861588370137)
              ·
                refine ⟨6630940985449396191277603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8841254647265861588370137 6630940985449396191277603)
                ·
                  refine ⟨9946411478174094286916405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6630940985449396191277603 9946411478174094286916405)
                  ·
                    refine ⟨932476076078821339398413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9946411478174094286916405 932476076078821339398413)
                    ·
                      rfl

theorem cell23_5447972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_5447972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447972 prefixEnd_5447972 := by exact prefixLift 5447972
  have htrace : WordTrace (prefixWord ++ tailWord_5447972) baseStart_5447972 baseEnd_5447972 := by
    simpa [prefixWord, tailWord_5447972, baseEnd_5447972] using wordTrace_append hprefix tailTrace_5447972
  have hstable : (prefixWord ++ tailWord_5447972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447972).length < 2 ^ (prefixWord ++ tailWord_5447972).sum := by decide
  have hdescent : baseEnd_5447972 < baseStart_5447972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447985 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 1, 6]
def baseStart_5447985 : Nat := 118140960795 + 5447985 * 2 ^ 59
def prefixEnd_5447985 : Nat := 4983230072969 + 3 ^ 40 * 5447985 * 2
def baseEnd_5447985 : Nat := 932478301161657489110893

theorem tailTrace_5447985 : CollatzResearch.WordTrace tailWord_5447985 prefixEnd_5447985 932478301161657489110893 := by
  unfold tailWord_5447985
  simp only [CollatzResearch.WordTrace]
  refine ⟨198704337167888261606857409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132469558111925507737904939 198704337167888261606857409)
  ·
    refine ⟨149028252875916196205143057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198704337167888261606857409 149028252875916196205143057)
    ·
      refine ⟨111771189656937147153857293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149028252875916196205143057 111771189656937147153857293)
      ·
        refine ⟨41914196121351430182696485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111771189656937147153857293 41914196121351430182696485)
        ·
          refine ⟨7858911772753393159255591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41914196121351430182696485 7858911772753393159255591)
          ·
            refine ⟨11788367659130089738883387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7858911772753393159255591 11788367659130089738883387)
            ·
              refine ⟨17682551488695134608325081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11788367659130089738883387 17682551488695134608325081)
              ·
                refine ⟨13261913616521350956243811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17682551488695134608325081 13261913616521350956243811)
                ·
                  refine ⟨19892870424782026434365717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13261913616521350956243811 19892870424782026434365717)
                  ·
                    refine ⟨932478301161657489110893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19892870424782026434365717 932478301161657489110893)
                    ·
                      rfl

theorem cell23_5447985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_5447985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447985 prefixEnd_5447985 := by exact prefixLift 5447985
  have htrace : WordTrace (prefixWord ++ tailWord_5447985) baseStart_5447985 baseEnd_5447985 := by
    simpa [prefixWord, tailWord_5447985, baseEnd_5447985] using wordTrace_append hprefix tailTrace_5447985
  have hstable : (prefixWord ++ tailWord_5447985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447985).length < 2 ^ (prefixWord ++ tailWord_5447985).sum := by decide
  have hdescent : baseEnd_5447985 < baseStart_5447985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5447998 : List Nat := [4, 2, 1, 2, 1, 13]
def baseStart_5447998 : Nat := 118140960795 + 5447998 * 2 ^ 59
def prefixEnd_5447998 : Nat := 4983230072969 + 3 ^ 40 * 5447998 * 2
def baseEnd_5447998 : Nat := 11512105262277699244733

theorem tailTrace_5447998 : CollatzResearch.WordTrace tailWord_5447998 prefixEnd_5447998 11512105262277699244733 := by
  unfold tailWord_5447998
  simp only [CollatzResearch.WordTrace]
  refine ⟨24838101414605145603385081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132469874211227443218053765 24838101414605145603385081)
  ·
    refine ⟨18628576060953859202538811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24838101414605145603385081 18628576060953859202538811)
    ·
      refine ⟨27942864091430788803808217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18628576060953859202538811 27942864091430788803808217)
      ·
        refine ⟨20957148068573091602856163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27942864091430788803808217 20957148068573091602856163)
        ·
          refine ⟨31435722102859637404284245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20957148068573091602856163 31435722102859637404284245)
          ·
            refine ⟨11512105262277699244733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 31435722102859637404284245 11512105262277699244733)
            ·
              rfl

theorem cell23_5447998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 13].length) (baseStart_5447998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5447998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5447998 prefixEnd_5447998 := by exact prefixLift 5447998
  have htrace : WordTrace (prefixWord ++ tailWord_5447998) baseStart_5447998 baseEnd_5447998 := by
    simpa [prefixWord, tailWord_5447998, baseEnd_5447998] using wordTrace_append hprefix tailTrace_5447998
  have hstable : (prefixWord ++ tailWord_5447998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5447998).length < 2 ^ (prefixWord ++ tailWord_5447998).sum := by decide
  have hdescent : baseEnd_5447998 < baseStart_5447998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5447998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448018 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_5448018 : Nat := 118140960795 + 5448018 * 2 ^ 59
def prefixEnd_5448018 : Nat := 4983230072969 + 3 ^ 40 * 5448018 * 2
def baseEnd_5448018 : Nat := 2797451848346570838220027

theorem tailTrace_5448018 : CollatzResearch.WordTrace tailWord_5448018 prefixEnd_5448018 2797451848346570838220027 := by
  unfold tailWord_5448018
  simp only [CollatzResearch.WordTrace]
  refine ⟨49676385194192177060702177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132470360517845805495205805 49676385194192177060702177)
  ·
    refine ⟨37257288895644132795526633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49676385194192177060702177 37257288895644132795526633)
    ·
      refine ⟨27942966671733099596644975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37257288895644132795526633 27942966671733099596644975)
      ·
        refine ⟨41914450007599649394967463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27942966671733099596644975 41914450007599649394967463)
        ·
          refine ⟨62871675011399474092451195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41914450007599649394967463 62871675011399474092451195)
          ·
            refine ⟨94307512517099211138676793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62871675011399474092451195 94307512517099211138676793)
            ·
              refine ⟨70730634387824408354007595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94307512517099211138676793 70730634387824408354007595)
              ·
                refine ⟨106095951581736612531011393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70730634387824408354007595 106095951581736612531011393)
                ·
                  refine ⟨79571963686302459398258545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106095951581736612531011393 79571963686302459398258545)
                  ·
                    refine ⟨59678972764726844548693909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79571963686302459398258545 59678972764726844548693909)
                    ·
                      refine ⟨2797451848346570838220027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59678972764726844548693909 2797451848346570838220027)
                      ·
                        rfl

theorem cell23_5448018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_5448018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448018 prefixEnd_5448018 := by exact prefixLift 5448018
  have htrace : WordTrace (prefixWord ++ tailWord_5448018) baseStart_5448018 baseEnd_5448018 := by
    simpa [prefixWord, tailWord_5448018, baseEnd_5448018] using wordTrace_append hprefix tailTrace_5448018
  have hstable : (prefixWord ++ tailWord_5448018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448018).length < 2 ^ (prefixWord ++ tailWord_5448018).sum := by decide
  have hdescent : baseEnd_5448018 < baseStart_5448018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448025 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 3]
def baseStart_5448025 : Nat := 118140960795 + 5448025 * 2 ^ 59
def prefixEnd_5448025 : Nat := 4983230072969 + 3 ^ 40 * 5448025 * 2
def baseEnd_5448025 : Nat := 2797455442711152310832495

theorem tailTrace_5448025 : CollatzResearch.WordTrace tailWord_5448025 prefixEnd_5448025 2797455442711152310832495 := by
  unfold tailWord_5448025
  simp only [CollatzResearch.WordTrace]
  refine ⟨198705796087743348438313529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132470530725162232292209019 198705796087743348438313529)
  ·
    refine ⟨149029347065807511328735147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198705796087743348438313529 149029347065807511328735147)
    ·
      refine ⟨223544020598711266993102721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149029347065807511328735147 223544020598711266993102721)
      ·
        refine ⟨167658015449033450244827041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223544020598711266993102721 167658015449033450244827041)
        ·
          refine ⟨125743511586775087683620281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167658015449033450244827041 125743511586775087683620281)
          ·
            refine ⟨94307633690081315762715211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125743511586775087683620281 94307633690081315762715211)
            ·
              refine ⟨141461450535121973644072817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94307633690081315762715211 141461450535121973644072817)
              ·
                refine ⟨106096087901341480233054613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141461450535121973644072817 106096087901341480233054613)
                ·
                  refine ⟨4973254120375381885924435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106096087901341480233054613 4973254120375381885924435)
                  ·
                    refine ⟨7459881180563072828886653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4973254120375381885924435 7459881180563072828886653)
                    ·
                      refine ⟨2797455442711152310832495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459881180563072828886653 2797455442711152310832495)
                      ·
                        rfl

theorem cell23_5448025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_5448025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448025 prefixEnd_5448025 := by exact prefixLift 5448025
  have htrace : WordTrace (prefixWord ++ tailWord_5448025) baseStart_5448025 baseEnd_5448025 := by
    simpa [prefixWord, tailWord_5448025, baseEnd_5448025] using wordTrace_append hprefix tailTrace_5448025
  have hstable : (prefixWord ++ tailWord_5448025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448025).length < 2 ^ (prefixWord ++ tailWord_5448025).sum := by decide
  have hdescent : baseEnd_5448025 < baseStart_5448025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448042 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_5448042 : Nat := 118140960795 + 5448042 * 2 ^ 59
def prefixEnd_5448042 : Nat := 4983230072969 + 3 ^ 40 * 5448042 * 2
def baseEnd_5448042 : Nat := 2797464171882278744319917

theorem tailTrace_5448042 : CollatzResearch.WordTrace tailWord_5448042 prefixEnd_5448042 2797464171882278744319917 := by
  unfold tailWord_5448042
  simp only [CollatzResearch.WordTrace]
  refine ⟨49676604032170440085420595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132470944085787840227788253 49676604032170440085420595)
  ·
    refine ⟨74514906048255660128130893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49676604032170440085420595 74514906048255660128130893)
    ·
      refine ⟨27943089768095872548049085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74514906048255660128130893 27943089768095872548049085)
      ·
        refine ⟨10478658663035952205518407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27943089768095872548049085 10478658663035952205518407)
        ·
          refine ⟨15717987994553928308277611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10478658663035952205518407 15717987994553928308277611)
          ·
            refine ⟨23576981991830892462416417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15717987994553928308277611 23576981991830892462416417)
            ·
              refine ⟨17682736493873169346812313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23576981991830892462416417 17682736493873169346812313)
              ·
                refine ⟨13262052370404877010109235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17682736493873169346812313 13262052370404877010109235)
                ·
                  refine ⟨19893078555607315515163853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13262052370404877010109235 19893078555607315515163853)
                  ·
                    refine ⟨7459904458352743318186445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19893078555607315515163853 7459904458352743318186445)
                    ·
                      refine ⟨2797464171882278744319917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459904458352743318186445 2797464171882278744319917)
                      ·
                        rfl

theorem cell23_5448042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_5448042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448042 prefixEnd_5448042 := by exact prefixLift 5448042
  have htrace : WordTrace (prefixWord ++ tailWord_5448042) baseStart_5448042 baseEnd_5448042 := by
    simpa [prefixWord, tailWord_5448042, baseEnd_5448042] using wordTrace_append hprefix tailTrace_5448042
  have hstable : (prefixWord ++ tailWord_5448042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448042).length < 2 ^ (prefixWord ++ tailWord_5448042).sum := by decide
  have hdescent : baseEnd_5448042 < baseStart_5448042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448059 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 3]
def baseStart_5448059 : Nat := 118140960795 + 5448059 * 2 ^ 59
def prefixEnd_5448059 : Nat := 4983230072969 + 3 ^ 40 * 5448059 * 2
def baseEnd_5448059 : Nat := 2797472901053405177807339

theorem tailTrace_5448059 : CollatzResearch.WordTrace tailWord_5448059 prefixEnd_5448059 2797472901053405177807339 := by
  unfold tailWord_5448059
  simp only [CollatzResearch.WordTrace]
  refine ⟨198707036169620172245051231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132471357446413448163367487 198707036169620172245051231)
  ·
    refine ⟨298060554254430258367576847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198707036169620172245051231 298060554254430258367576847)
    ·
      refine ⟨447090831381645387551365271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298060554254430258367576847 447090831381645387551365271)
      ·
        refine ⟨670636247072468081327047907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447090831381645387551365271 670636247072468081327047907)
        ·
          refine ⟨1005954370608702121990571861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670636247072468081327047907 1005954370608702121990571861)
          ·
            refine ⟨5894263890285363996038507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1005954370608702121990571861 5894263890285363996038507)
            ·
              refine ⟨8841395835428045994057761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894263890285363996038507 8841395835428045994057761)
              ·
                refine ⟨6631046876571034495543321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8841395835428045994057761 6631046876571034495543321)
                ·
                  refine ⟨4973285157428275871657491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631046876571034495543321 4973285157428275871657491)
                  ·
                    refine ⟨7459927736142413807486237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4973285157428275871657491 7459927736142413807486237)
                    ·
                      refine ⟨2797472901053405177807339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7459927736142413807486237 2797472901053405177807339)
                      ·
                        rfl

theorem cell23_5448059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 3].length) (baseStart_5448059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448059 prefixEnd_5448059 := by exact prefixLift 5448059
  have htrace : WordTrace (prefixWord ++ tailWord_5448059) baseStart_5448059 baseEnd_5448059 := by
    simpa [prefixWord, tailWord_5448059, baseEnd_5448059] using wordTrace_append hprefix tailTrace_5448059
  have hstable : (prefixWord ++ tailWord_5448059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448059).length < 2 ^ (prefixWord ++ tailWord_5448059).sum := by decide
  have hdescent : baseEnd_5448059 < baseStart_5448059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448172 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 2, 4, 2]
def baseStart_5448172 : Nat := 118140960795 + 5448172 * 2 ^ 59
def prefixEnd_5448172 : Nat := 4983230072969 + 3 ^ 40 * 5448172 * 2
def baseEnd_5448172 : Nat := 2797530924367363235694319

theorem tailTrace_5448172 : CollatzResearch.WordTrace tailWord_5448172 prefixEnd_5448172 2797530924367363235694319 := by
  unfold tailWord_5448172
  simp only [CollatzResearch.WordTrace]
  refine ⟨99355578809105396271957385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132474105078807195029276513 99355578809105396271957385)
  ·
    refine ⟨74516684106829047203968039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99355578809105396271957385 74516684106829047203968039)
    ·
      refine ⟨111775026160243570805952059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74516684106829047203968039 111775026160243570805952059)
      ·
        refine ⟨167662539240365356208928089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111775026160243570805952059 167662539240365356208928089)
        ·
          refine ⟨125746904430274017156696067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167662539240365356208928089 125746904430274017156696067)
          ·
            refine ⟨188620356645411025735044101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125746904430274017156696067 188620356645411025735044101)
            ·
              refine ⟨35366316871014567325320769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188620356645411025735044101 35366316871014567325320769)
              ·
                refine ⟨26524737653260925493990577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35366316871014567325320769 26524737653260925493990577)
                ·
                  refine ⟨19893553239945694120492933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26524737653260925493990577 19893553239945694120492933)
                  ·
                    refine ⟨3730041232489817647592425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19893553239945694120492933 3730041232489817647592425)
                    ·
                      refine ⟨2797530924367363235694319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730041232489817647592425 2797530924367363235694319)
                      ·
                        rfl

theorem cell23_5448172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_5448172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448172 prefixEnd_5448172 := by exact prefixLift 5448172
  have htrace : WordTrace (prefixWord ++ tailWord_5448172) baseStart_5448172 baseEnd_5448172 := by
    simpa [prefixWord, tailWord_5448172, baseEnd_5448172] using wordTrace_append hprefix tailTrace_5448172
  have hstable : (prefixWord ++ tailWord_5448172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448172).length < 2 ^ (prefixWord ++ tailWord_5448172).sum := by decide
  have hdescent : baseEnd_5448172 < baseStart_5448172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448175 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 3]
def baseStart_5448175 : Nat := 118140960795 + 5448175 * 2 ^ 59
def prefixEnd_5448175 : Nat := 4983230072969 + 3 ^ 40 * 5448175 * 2
def baseEnd_5448175 : Nat := 2797532464809326723956805

theorem tailTrace_5448175 : CollatzResearch.WordTrace tailWord_5448175 prefixEnd_5448175 2797532464809326723956805 := by
  unfold tailWord_5448175
  simp only [CollatzResearch.WordTrace]
  refine ⟨198711267037199924056273979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132474178024799949370849319 198711267037199924056273979)
  ·
    refine ⟨298066900555799886084410969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198711267037199924056273979 298066900555799886084410969)
    ·
      refine ⟨223550175416849914563308227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298066900555799886084410969 223550175416849914563308227)
      ·
        refine ⟨335325263125274871844962341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223550175416849914563308227 335325263125274871844962341)
        ·
          refine ⟨62873486835989038470930439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335325263125274871844962341 62873486835989038470930439)
          ·
            refine ⟨94310230253983557706395659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62873486835989038470930439 94310230253983557706395659)
            ·
              refine ⟨141465345380975336559593489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94310230253983557706395659 141465345380975336559593489)
              ·
                refine ⟨106099009035731502419695117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141465345380975336559593489 106099009035731502419695117)
                ·
                  refine ⟨39787128388399313407385669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106099009035731502419695117 39787128388399313407385669)
                  ·
                    refine ⟨7460086572824871263884813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39787128388399313407385669 7460086572824871263884813)
                    ·
                      refine ⟨2797532464809326723956805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7460086572824871263884813 2797532464809326723956805)
                      ·
                        rfl

theorem cell23_5448175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_5448175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448175 prefixEnd_5448175 := by exact prefixLift 5448175
  have htrace : WordTrace (prefixWord ++ tailWord_5448175) baseStart_5448175 baseEnd_5448175 := by
    simpa [prefixWord, tailWord_5448175, baseEnd_5448175] using wordTrace_append hprefix tailTrace_5448175
  have hstable : (prefixWord ++ tailWord_5448175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448175).length < 2 ^ (prefixWord ++ tailWord_5448175).sum := by decide
  have hdescent : baseEnd_5448175 < baseStart_5448175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448195 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 6]
def baseStart_5448195 : Nat := 118140960795 + 5448195 * 2 ^ 59
def prefixEnd_5448195 : Nat := 4983230072969 + 3 ^ 40 * 5448195 * 2
def baseEnd_5448195 : Nat := 310838081602490738411857

theorem tailTrace_5448195 : CollatzResearch.WordTrace tailWord_5448195 prefixEnd_5448195 310838081602490738411857 := by
  unfold tailWord_5448195
  simp only [CollatzResearch.WordTrace]
  refine ⟨198711996497127467472002039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132474664331418311648001359 198711996497127467472002039)
  ·
    refine ⟨298067994745691201208003059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198711996497127467472002039 298067994745691201208003059)
    ·
      refine ⟨447101992118536801812004589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298067994745691201208003059 447101992118536801812004589)
      ·
        refine ⟨167663247044451300679501721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447101992118536801812004589 167663247044451300679501721)
        ·
          refine ⟨125747435283338475509626291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167663247044451300679501721 125747435283338475509626291)
          ·
            refine ⟨188621152925007713264439437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125747435283338475509626291 188621152925007713264439437)
            ·
              refine ⟨70732932346877892474164789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188621152925007713264439437 70732932346877892474164789)
              ·
                refine ⟨6631212407519802419452949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70732932346877892474164789 6631212407519802419452949)
                ·
                  refine ⟨310838081602490738411857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6631212407519802419452949 310838081602490738411857)
                  ·
                    rfl

theorem cell23_5448195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 6].length) (baseStart_5448195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448195 prefixEnd_5448195 := by exact prefixLift 5448195
  have htrace : WordTrace (prefixWord ++ tailWord_5448195) baseStart_5448195 baseEnd_5448195 := by
    simpa [prefixWord, tailWord_5448195, baseEnd_5448195] using wordTrace_append hprefix tailTrace_5448195
  have hstable : (prefixWord ++ tailWord_5448195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448195).length < 2 ^ (prefixWord ++ tailWord_5448195).sum := by decide
  have hdescent : baseEnd_5448195 < baseStart_5448195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448199 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 3, 4]
def baseStart_5448199 : Nat := 118140960795 + 5448199 * 2 ^ 59
def prefixEnd_5448199 : Nat := 4983230072969 + 3 ^ 40 * 5448199 * 2
def baseEnd_5448199 : Nat := 932514929448344876685565

theorem tailTrace_5448199 : CollatzResearch.WordTrace tailWord_5448199 prefixEnd_5448199 932514929448344876685565 := by
  unfold tailWord_5448199
  simp only [CollatzResearch.WordTrace]
  refine ⟨198712142389112976155147651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132474761592741984103431767 198712142389112976155147651)
  ·
    refine ⟨298068213583669464232721477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198712142389112976155147651 298068213583669464232721477)
    ·
      refine ⟨55887790046938024543635277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298068213583669464232721477 55887790046938024543635277)
      ·
        refine ⟨20957921267601759203863229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55887790046938024543635277 20957921267601759203863229)
        ·
          refine ⟨7859220475350659701448711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20957921267601759203863229 7859220475350659701448711)
          ·
            refine ⟨11788830713025989552173067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7859220475350659701448711 11788830713025989552173067)
            ·
              refine ⟨17683246069538984328259601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11788830713025989552173067 17683246069538984328259601)
              ·
                refine ⟨13262434552154238246194701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17683246069538984328259601 13262434552154238246194701)
                ·
                  refine ⟨4973412957057839342323013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13262434552154238246194701 4973412957057839342323013)
                  ·
                    refine ⟨932514929448344876685565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4973412957057839342323013 932514929448344876685565)
                    ·
                      rfl

theorem cell23_5448199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_5448199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448199 prefixEnd_5448199 := by exact prefixLift 5448199
  have htrace : WordTrace (prefixWord ++ tailWord_5448199) baseStart_5448199 baseEnd_5448199 := by
    simpa [prefixWord, tailWord_5448199, baseEnd_5448199] using wordTrace_append hprefix tailTrace_5448199
  have hstable : (prefixWord ++ tailWord_5448199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448199).length < 2 ^ (prefixWord ++ tailWord_5448199).sum := by decide
  have hdescent : baseEnd_5448199 < baseStart_5448199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448216 : List Nat := [2, 1, 2, 3, 3, 2, 2, 3, 1, 4]
def baseStart_5448216 : Nat := 118140960795 + 5448216 * 2 ^ 59
def prefixEnd_5448216 : Nat := 4983230072969 + 3 ^ 40 * 5448216 * 2
def baseEnd_5448216 : Nat := 932517839172053687848039

theorem tailTrace_5448216 : CollatzResearch.WordTrace tailWord_5448216 prefixEnd_5448216 932517839172053687848039 := by
  unfold tailWord_5448216
  simp only [CollatzResearch.WordTrace]
  refine ⟨99356381215025694029258251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132475174953367592039011001 99356381215025694029258251)
  ·
    refine ⟨149034571822538541043887377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99356381215025694029258251 149034571822538541043887377)
    ·
      refine ⟨111775928866903905782915533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149034571822538541043887377 111775928866903905782915533)
      ·
        refine ⟨41915973325088964668593325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111775928866903905782915533 41915973325088964668593325)
        ·
          refine ⟨15718489996908361750722497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41915973325088964668593325 15718489996908361750722497)
          ·
            refine ⟨11788867497681271313041873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15718489996908361750722497 11788867497681271313041873)
            ·
              refine ⟨8841650623260953484781405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11788867497681271313041873 8841650623260953484781405)
              ·
                refine ⟨3315618983722857556793027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8841650623260953484781405 3315618983722857556793027)
                ·
                  refine ⟨4973428475584286335189541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3315618983722857556793027 4973428475584286335189541)
                  ·
                    refine ⟨932517839172053687848039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4973428475584286335189541 932517839172053687848039)
                    ·
                      rfl

theorem cell23_5448216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_5448216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448216 prefixEnd_5448216 := by exact prefixLift 5448216
  have htrace : WordTrace (prefixWord ++ tailWord_5448216) baseStart_5448216 baseEnd_5448216 := by
    simpa [prefixWord, tailWord_5448216, baseEnd_5448216] using wordTrace_append hprefix tailTrace_5448216
  have hstable : (prefixWord ++ tailWord_5448216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448216).length < 2 ^ (prefixWord ++ tailWord_5448216).sum := by decide
  have hdescent : baseEnd_5448216 < baseStart_5448216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448232 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5448232 : Nat := 118140960795 + 5448232 * 2 ^ 59
def prefixEnd_5448232 : Nat := 4983230072969 + 3 ^ 40 * 5448232 * 2
def baseEnd_5448232 : Nat := 2797561733206633000944043

theorem tailTrace_5448232 : CollatzResearch.WordTrace tailWord_5448232 prefixEnd_5448232 2797561733206633000944043 := by
  unfold tailWord_5448232
  simp only [CollatzResearch.WordTrace]
  refine ⟨99356672998996711395549475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132475563998662281860732633 99356672998996711395549475)
  ·
    refine ⟨149035009498495067093324213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99356672998996711395549475 149035009498495067093324213)
    ·
      refine ⟨13972032140483912539999145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149035009498495067093324213 13972032140483912539999145)
      ·
        refine ⟨10479024105362934404999359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13972032140483912539999145 10479024105362934404999359)
        ·
          refine ⟨15718536158044401607499039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10479024105362934404999359 15718536158044401607499039)
          ·
            refine ⟨23577804237066602411248559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15718536158044401607499039 23577804237066602411248559)
            ·
              refine ⟨35366706355599903616872839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23577804237066602411248559 35366706355599903616872839)
              ·
                refine ⟨53050059533399855425309259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35366706355599903616872839 53050059533399855425309259)
                ·
                  refine ⟨79575089300099783137963889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53050059533399855425309259 79575089300099783137963889)
                  ·
                    refine ⟨59681316975074837353472917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79575089300099783137963889 59681316975074837353472917)
                    ·
                      refine ⟨2797561733206633000944043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59681316975074837353472917 2797561733206633000944043)
                      ·
                        rfl

theorem cell23_5448232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5448232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448232 prefixEnd_5448232 := by exact prefixLift 5448232
  have htrace : WordTrace (prefixWord ++ tailWord_5448232) baseStart_5448232 baseEnd_5448232 := by
    simpa [prefixWord, tailWord_5448232, baseEnd_5448232] using wordTrace_append hprefix tailTrace_5448232
  have hstable : (prefixWord ++ tailWord_5448232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448232).length < 2 ^ (prefixWord ++ tailWord_5448232).sum := by decide
  have hdescent : baseEnd_5448232 < baseStart_5448232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448246 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_5448246 : Nat := 118140960795 + 5448246 * 2 ^ 59
def prefixEnd_5448246 : Nat := 4983230072969 + 3 ^ 40 * 5448246 * 2
def baseEnd_5448246 : Nat := 310840991326199549574331

theorem tailTrace_5448246 : CollatzResearch.WordTrace tailWord_5448246 prefixEnd_5448246 310840991326199549574331 := by
  unfold tailWord_5448246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12419616038746418948881787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132475904413295135454739061 12419616038746418948881787)
  ·
    refine ⟨18629424058119628423322681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12419616038746418948881787 18629424058119628423322681)
    ·
      refine ⟨13972068043589721317492011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18629424058119628423322681 13972068043589721317492011)
      ·
        refine ⟨20958102065384581976238017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13972068043589721317492011 20958102065384581976238017)
        ·
          refine ⟨15718576549038436482178513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20958102065384581976238017 15718576549038436482178513)
          ·
            refine ⟨11788932411778827361633885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15718576549038436482178513 11788932411778827361633885)
            ·
              refine ⟨4420849654417060260612707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11788932411778827361633885 4420849654417060260612707)
              ·
                refine ⟨6631274481625590390919061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4420849654417060260612707 6631274481625590390919061)
                ·
                  refine ⟨310840991326199549574331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6631274481625590390919061 310840991326199549574331)
                  ·
                    rfl

theorem cell23_5448246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_5448246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448246 prefixEnd_5448246 := by exact prefixLift 5448246
  have htrace : WordTrace (prefixWord ++ tailWord_5448246) baseStart_5448246 baseEnd_5448246 := by
    simpa [prefixWord, tailWord_5448246, baseEnd_5448246] using wordTrace_append hprefix tailTrace_5448246
  have hstable : (prefixWord ++ tailWord_5448246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448246).length < 2 ^ (prefixWord ++ tailWord_5448246).sum := by decide
  have hdescent : baseEnd_5448246 < baseStart_5448246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448273 : List Nat := [1, 2, 2, 1, 3, 5, 1, 3, 1, 1, 3]
def baseStart_5448273 : Nat := 118140960795 + 5448273 * 2 ^ 59
def prefixEnd_5448273 : Nat := 4983230072969 + 3 ^ 40 * 5448273 * 2
def baseEnd_5448273 : Nat := 2797582785913467340531355

theorem tailTrace_5448273 : CollatzResearch.WordTrace tailWord_5448273 prefixEnd_5448273 2797582785913467340531355 := by
  unfold tailWord_5448273
  simp only [CollatzResearch.WordTrace]
  refine ⟨198714841390844886793341473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132476560927229924528894315 198714841390844886793341473)
  ·
    refine ⟨149036131043133665095006105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198714841390844886793341473 149036131043133665095006105)
    ·
      refine ⟨111777098282350248821254579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149036131043133665095006105 111777098282350248821254579)
      ·
        refine ⟨167665647423525373231881869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111777098282350248821254579 167665647423525373231881869)
        ·
          refine ⟨62874617783822014961955701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167665647423525373231881869 62874617783822014961955701)
          ·
            refine ⟨5894495417233313902683347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62874617783822014961955701 5894495417233313902683347)
            ·
              refine ⟨8841743125849970854025021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894495417233313902683347 8841743125849970854025021)
              ·
                refine ⟨3315653672193739070259383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8841743125849970854025021 3315653672193739070259383)
                ·
                  refine ⟨4973480508290608605389075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3315653672193739070259383 4973480508290608605389075)
                  ·
                    refine ⟨7460220762435912908083613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4973480508290608605389075 7460220762435912908083613)
                    ·
                      refine ⟨2797582785913467340531355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7460220762435912908083613 2797582785913467340531355)
                      ·
                        rfl

theorem cell23_5448273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 1, 3].length) (baseStart_5448273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448273 prefixEnd_5448273 := by exact prefixLift 5448273
  have htrace : WordTrace (prefixWord ++ tailWord_5448273) baseStart_5448273 baseEnd_5448273 := by
    simpa [prefixWord, tailWord_5448273, baseEnd_5448273] using wordTrace_append hprefix tailTrace_5448273
  have hstable : (prefixWord ++ tailWord_5448273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448273).length < 2 ^ (prefixWord ++ tailWord_5448273).sum := by decide
  have hdescent : baseEnd_5448273 < baseStart_5448273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448282 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_5448282 : Nat := 118140960795 + 5448282 * 2 ^ 59
def prefixEnd_5448282 : Nat := 4983230072969 + 3 ^ 40 * 5448282 * 2
def baseEnd_5448282 : Nat := 2797587407239357805318813

theorem tailTrace_5448282 : CollatzResearch.WordTrace tailWord_5448282 prefixEnd_5448282 2797587407239357805318813 := by
  unfold tailWord_5448282
  simp only [CollatzResearch.WordTrace]
  refine ⟨49678792411953070332604775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132476779765208187553612733 49678792411953070332604775)
  ·
    refine ⟨74518188617929605498907163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49678792411953070332604775 74518188617929605498907163)
    ·
      refine ⟨111777282926894408248360745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74518188617929605498907163 111777282926894408248360745)
      ·
        refine ⟨83832962195170806186270559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111777282926894408248360745 83832962195170806186270559)
        ·
          refine ⟨125749443292756209279405839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83832962195170806186270559 125749443292756209279405839)
          ·
            refine ⟨188624164939134313919108759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125749443292756209279405839 188624164939134313919108759)
            ·
              refine ⟨282936247408701470878663139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188624164939134313919108759 282936247408701470878663139)
              ·
                refine ⟨424404371113052206317994709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282936247408701470878663139 424404371113052206317994709)
                ·
                  refine ⟨9946977447962161085578001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 424404371113052206317994709 9946977447962161085578001)
                  ·
                    refine ⟨7460233085971620814183501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9946977447962161085578001 7460233085971620814183501)
                    ·
                      refine ⟨2797587407239357805318813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7460233085971620814183501 2797587407239357805318813)
                      ·
                        rfl

theorem cell23_5448282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_5448282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448282 prefixEnd_5448282 := by exact prefixLift 5448282
  have htrace : WordTrace (prefixWord ++ tailWord_5448282) baseStart_5448282 baseEnd_5448282 := by
    simpa [prefixWord, tailWord_5448282, baseEnd_5448282] using wordTrace_append hprefix tailTrace_5448282
  have hstable : (prefixWord ++ tailWord_5448282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448282).length < 2 ^ (prefixWord ++ tailWord_5448282).sum := by decide
  have hdescent : baseEnd_5448282 < baseStart_5448282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448290 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5448290 : Nat := 118140960795 + 5448290 * 2 ^ 59
def prefixEnd_5448290 : Nat := 4983230072969 + 3 ^ 40 * 5448290 * 2
def baseEnd_5448290 : Nat := 2797591515084593774018777

theorem tailTrace_5448290 : CollatzResearch.WordTrace tailWord_5448290 prefixEnd_5448290 2797591515084593774018777 := by
  unfold tailWord_5448290
  simp only [CollatzResearch.WordTrace]
  refine ⟨49678865357945824674177581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132476974287855532464473549 49678865357945824674177581)
  ·
    refine ⟨18629574509229684252816593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49678865357945824674177581 18629574509229684252816593)
    ·
      refine ⟨13972180881922263189612445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18629574509229684252816593 13972180881922263189612445)
      ·
        refine ⟨5239567830720848696104667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13972180881922263189612445 5239567830720848696104667)
        ·
          refine ⟨7859351746081273044157001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5239567830720848696104667 7859351746081273044157001)
          ·
            refine ⟨5894513809560954783117751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859351746081273044157001 5894513809560954783117751)
            ·
              refine ⟨8841770714341432174676627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894513809560954783117751 8841770714341432174676627)
              ·
                refine ⟨13262656071512148262014941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8841770714341432174676627 13262656071512148262014941)
                ·
                  refine ⟨4973496026817055598255603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13262656071512148262014941 4973496026817055598255603)
                  ·
                    refine ⟨7460244040225583397383405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4973496026817055598255603 7460244040225583397383405)
                    ·
                      refine ⟨2797591515084593774018777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7460244040225583397383405 2797591515084593774018777)
                      ·
                        rfl

theorem cell23_5448290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5448290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448290 prefixEnd_5448290 := by exact prefixLift 5448290
  have htrace : WordTrace (prefixWord ++ tailWord_5448290) baseStart_5448290 baseEnd_5448290 := by
    simpa [prefixWord, tailWord_5448290, baseEnd_5448290] using wordTrace_append hprefix tailTrace_5448290
  have hstable : (prefixWord ++ tailWord_5448290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448290).length < 2 ^ (prefixWord ++ tailWord_5448290).sum := by decide
  have hdescent : baseEnd_5448290 < baseStart_5448290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448302 : List Nat := [4, 1, 2, 2, 2, 1, 1, 10]
def baseStart_5448302 : Nat := 118140960795 + 5448302 * 2 ^ 59
def prefixEnd_5448302 : Nat := 4983230072969 + 3 ^ 40 * 5448302 * 2
def baseEnd_5448302 : Nat := 103614728772312878780323

theorem tailTrace_5448302 : CollatzResearch.WordTrace tailWord_5448302 prefixEnd_5448302 103614728772312878780323 := by
  unfold tailWord_5448302
  simp only [CollatzResearch.WordTrace]
  refine ⟨24839487388467478093268395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132477266071826549830764773 24839487388467478093268395)
  ·
    refine ⟨37259231082701217139902593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24839487388467478093268395 37259231082701217139902593)
    ·
      refine ⟨27944423312025912854926945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37259231082701217139902593 27944423312025912854926945)
      ·
        refine ⟨20958317484019434641195209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27944423312025912854926945 20958317484019434641195209)
        ·
          refine ⟨15718738113014575980896407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20958317484019434641195209 15718738113014575980896407)
          ·
            refine ⟨23578107169521863971344611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15718738113014575980896407 23578107169521863971344611)
            ·
              refine ⟨35367160754282795957016917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23578107169521863971344611 35367160754282795957016917)
              ·
                refine ⟨103614728772312878780323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35367160754282795957016917 103614728772312878780323)
                ·
                  rfl

theorem cell23_5448302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_5448302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448302 prefixEnd_5448302 := by exact prefixLift 5448302
  have htrace : WordTrace (prefixWord ++ tailWord_5448302) baseStart_5448302 baseEnd_5448302 := by
    simpa [prefixWord, tailWord_5448302, baseEnd_5448302] using wordTrace_append hprefix tailTrace_5448302
  have hstable : (prefixWord ++ tailWord_5448302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448302).length < 2 ^ (prefixWord ++ tailWord_5448302).sum := by decide
  have hdescent : baseEnd_5448302 < baseStart_5448302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448306 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_5448306 : Nat := 118140960795 + 5448306 * 2 ^ 59
def prefixEnd_5448306 : Nat := 4983230072969 + 3 ^ 40 * 5448306 * 2
def baseEnd_5448306 : Nat := 932533243591688570472901

theorem tailTrace_5448306 : CollatzResearch.WordTrace tailWord_5448306 prefixEnd_5448306 932533243591688570472901 := by
  unfold tailWord_5448306
  simp only [CollatzResearch.WordTrace]
  refine ⟨49679011249931333357323193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132477363333150222286195181 49679011249931333357323193)
  ·
    refine ⟨37259258437448500017992395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49679011249931333357323193 37259258437448500017992395)
    ·
      refine ⟨55888887656172750026988593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37259258437448500017992395 55888887656172750026988593)
      ·
        refine ⟨41916665742129562520241445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55888887656172750026988593 41916665742129562520241445)
        ·
          refine ⟨7859374826649292972545271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41916665742129562520241445 7859374826649292972545271)
          ·
            refine ⟨11789062239973939458817907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7859374826649292972545271 11789062239973939458817907)
            ·
              refine ⟨17683593359960909188226861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11789062239973939458817907 17683593359960909188226861)
              ·
                refine ⟨6631347509985340945585073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17683593359960909188226861 6631347509985340945585073)
                ·
                  refine ⟨4973510632489005709188805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631347509985340945585073 4973510632489005709188805)
                  ·
                    refine ⟨932533243591688570472901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4973510632489005709188805 932533243591688570472901)
                    ·
                      rfl

theorem cell23_5448306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_5448306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448306 prefixEnd_5448306 := by exact prefixLift 5448306
  have htrace : WordTrace (prefixWord ++ tailWord_5448306) baseStart_5448306 baseEnd_5448306 := by
    simpa [prefixWord, tailWord_5448306, baseEnd_5448306] using wordTrace_append hprefix tailTrace_5448306
  have hstable : (prefixWord ++ tailWord_5448306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448306).length < 2 ^ (prefixWord ++ tailWord_5448306).sum := by decide
  have hdescent : baseEnd_5448306 < baseStart_5448306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448315 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 4, 7]
def baseStart_5448315 : Nat := 118140960795 + 5448315 * 2 ^ 59
def prefixEnd_5448315 : Nat := 4983230072969 + 3 ^ 40 * 5448315 * 2
def baseEnd_5448315 : Nat := 932534784033652058735387

theorem tailTrace_5448315 : CollatzResearch.WordTrace tailWord_5448315 prefixEnd_5448315 932534784033652058735387 := by
  unfold tailWord_5448315
  simp only [CollatzResearch.WordTrace]
  refine ⟨198716373256692727966370399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132477582171128485310913599 198716373256692727966370399)
  ·
    refine ⟨298074559885039091949555599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198716373256692727966370399 298074559885039091949555599)
    ·
      refine ⟨447111839827558637924333399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298074559885039091949555599 447111839827558637924333399)
      ·
        refine ⟨670667759741337956886500099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447111839827558637924333399 670667759741337956886500099)
        ·
          refine ⟨1006001639612006935329750149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670667759741337956886500099 1006001639612006935329750149)
          ·
            refine ⟨188625307427251300374328153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1006001639612006935329750149 188625307427251300374328153)
            ·
              refine ⟨141468980570438475280746115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188625307427251300374328153 141468980570438475280746115)
              ·
                refine ⟨212203470855657712921119173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141468980570438475280746115 212203470855657712921119173)
                ·
                  refine ⟨39788150785435821172709845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212203470855657712921119173 39788150785435821172709845)
                  ·
                    refine ⟨932534784033652058735387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39788150785435821172709845 932534784033652058735387)
                    ·
                      rfl

theorem cell23_5448315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 7].length) (baseStart_5448315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448315 prefixEnd_5448315 := by exact prefixLift 5448315
  have htrace : WordTrace (prefixWord ++ tailWord_5448315) baseStart_5448315 baseEnd_5448315 := by
    simpa [prefixWord, tailWord_5448315, baseEnd_5448315] using wordTrace_append hprefix tailTrace_5448315
  have hstable : (prefixWord ++ tailWord_5448315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448315).length < 2 ^ (prefixWord ++ tailWord_5448315).sum := by decide
  have hdescent : baseEnd_5448315 < baseStart_5448315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448335 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_5448335 : Nat := 118140960795 + 5448335 * 2 ^ 59
def prefixEnd_5448335 : Nat := 4983230072969 + 3 ^ 40 * 5448335 * 2
def baseEnd_5448335 : Nat := 2797614621714046097956069

theorem tailTrace_5448335 : CollatzResearch.WordTrace tailWord_5448335 prefixEnd_5448335 2797614621714046097956069 := by
  unfold tailWord_5448335
  simp only [CollatzResearch.WordTrace]
  refine ⟨198717102716620271382098459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132478068477746847588065639 198717102716620271382098459)
  ·
    refine ⟨298075654074930407073147689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198717102716620271382098459 298075654074930407073147689)
    ·
      refine ⟨223556740556197805304860767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298075654074930407073147689 223556740556197805304860767)
      ·
        refine ⟨335335110834296707957291151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223556740556197805304860767 335335110834296707957291151)
        ·
          refine ⟨503002666251445061935936727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335335110834296707957291151 503002666251445061935936727)
          ·
            refine ⟨754503999377167592903905091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503002666251445061935936727 754503999377167592903905091)
            ·
              refine ⟨1131755999065751389355857637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754503999377167592903905091 1131755999065751389355857637)
              ·
                refine ⟨212204249824828385504223307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1131755999065751389355857637 212204249824828385504223307)
                ·
                  refine ⟨318306374737242578256334961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212204249824828385504223307 318306374737242578256334961)
                  ·
                    refine ⟨238729781052931933692251221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 318306374737242578256334961 238729781052931933692251221)
                    ·
                      refine ⟨2797614621714046097956069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 238729781052931933692251221 2797614621714046097956069)
                      ·
                        rfl

theorem cell23_5448335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_5448335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448335 prefixEnd_5448335 := by exact prefixLift 5448335
  have htrace : WordTrace (prefixWord ++ tailWord_5448335) baseStart_5448335 baseEnd_5448335 := by
    simpa [prefixWord, tailWord_5448335, baseEnd_5448335] using wordTrace_append hprefix tailTrace_5448335
  have hstable : (prefixWord ++ tailWord_5448335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448335).length < 2 ^ (prefixWord ++ tailWord_5448335).sum := by decide
  have hdescent : baseEnd_5448335 < baseStart_5448335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448397 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_5448397 : Nat := 118140960795 + 5448397 * 2 ^ 59
def prefixEnd_5448397 : Nat := 4983230072969 + 3 ^ 40 * 5448397 * 2
def baseEnd_5448397 : Nat := 2797646457514624855380785

theorem tailTrace_5448397 : CollatzResearch.WordTrace tailWord_5448397 prefixEnd_5448397 2797646457514624855380785 := by
  unfold tailWord_5448397
  simp only [CollatzResearch.WordTrace]
  refine ⟨198719364042395655970855445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132479576028263770647236963 198719364042395655970855445)
  ·
    refine ⟨9314970189487296373633849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198719364042395655970855445 9314970189487296373633849)
    ·
      refine ⟨6986227642115472280225387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9314970189487296373633849 6986227642115472280225387)
      ·
        refine ⟨10479341463173208420338081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6986227642115472280225387 10479341463173208420338081)
        ·
          refine ⟨7859506097379906315253561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10479341463173208420338081 7859506097379906315253561)
          ·
            refine ⟨5894629573034929736440171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859506097379906315253561 5894629573034929736440171)
            ·
              refine ⟨8841944359552394604660257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894629573034929736440171 8841944359552394604660257)
              ·
                refine ⟨6631458269664295953495193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8841944359552394604660257 6631458269664295953495193)
                ·
                  refine ⟨4973593702248221965121395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631458269664295953495193 4973593702248221965121395)
                  ·
                    refine ⟨7460390553372332947682093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4973593702248221965121395 7460390553372332947682093)
                    ·
                      refine ⟨2797646457514624855380785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7460390553372332947682093 2797646457514624855380785)
                      ·
                        rfl

theorem cell23_5448397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_5448397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448397 prefixEnd_5448397 := by exact prefixLift 5448397
  have htrace : WordTrace (prefixWord ++ tailWord_5448397) baseStart_5448397 baseEnd_5448397 := by
    simpa [prefixWord, tailWord_5448397, baseEnd_5448397] using wordTrace_append hprefix tailTrace_5448397
  have hstable : (prefixWord ++ tailWord_5448397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448397).length < 2 ^ (prefixWord ++ tailWord_5448397).sum := by decide
  have hdescent : baseEnd_5448397 < baseStart_5448397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448409 : List Nat := [1, 2, 1, 2, 3, 2, 1, 6, 5]
def baseStart_5448409 : Nat := 118140960795 + 5448409 * 2 ^ 59
def prefixEnd_5448409 : Nat := 4983230072969 + 3 ^ 40 * 5448409 * 2
def baseEnd_5448409 : Nat := 310850291031386534270081

theorem tailTrace_5448409 : CollatzResearch.WordTrace tailWord_5448409 prefixEnd_5448409 310850291031386534270081 := by
  unfold tailWord_5448409
  simp only [CollatzResearch.WordTrace]
  refine ⟨198719801718352182020292281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132479867812234788013528187 198719801718352182020292281)
  ·
    refine ⟨149039851288764136515219211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198719801718352182020292281 149039851288764136515219211)
    ·
      refine ⟨223559776933146204772828817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149039851288764136515219211 223559776933146204772828817)
      ·
        refine ⟨167669832699859653579621613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223559776933146204772828817 167669832699859653579621613)
        ·
          refine ⟨62876187262447370092358105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167669832699859653579621613 62876187262447370092358105)
          ·
            refine ⟨47157140446835527569268579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62876187262447370092358105 47157140446835527569268579)
            ·
              refine ⟨70735710670253291353902869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47157140446835527569268579 70735710670253291353902869)
              ·
                refine ⟨3315736437668123032214197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70735710670253291353902869 3315736437668123032214197)
                ·
                  refine ⟨310850291031386534270081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3315736437668123032214197 310850291031386534270081)
                  ·
                    rfl

theorem cell23_5448409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 6, 5].length) (baseStart_5448409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448409 prefixEnd_5448409 := by exact prefixLift 5448409
  have htrace : WordTrace (prefixWord ++ tailWord_5448409) baseStart_5448409 baseEnd_5448409 := by
    simpa [prefixWord, tailWord_5448409, baseEnd_5448409] using wordTrace_append hprefix tailTrace_5448409
  have hstable : (prefixWord ++ tailWord_5448409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448409).length < 2 ^ (prefixWord ++ tailWord_5448409).sum := by decide
  have hdescent : baseEnd_5448409 < baseStart_5448409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448420 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_5448420 : Nat := 118140960795 + 5448420 * 2 ^ 59
def prefixEnd_5448420 : Nat := 4983230072969 + 3 ^ 40 * 5448420 * 2
def baseEnd_5448420 : Nat := 2797658267569678265393179

theorem tailTrace_5448420 : CollatzResearch.WordTrace tailWord_5448420 prefixEnd_5448420 2797658267569678265393179 := by
  unfold tailWord_5448420
  simp only [CollatzResearch.WordTrace]
  refine ⟨99360101460656165449471357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132480135280874887265961809 99360101460656165449471357)
  ·
    refine ⟨37260038047746062043551759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99360101460656165449471357 37260038047746062043551759)
    ·
      refine ⟨55890057071619093065327639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37260038047746062043551759 55890057071619093065327639)
      ·
        refine ⟨83835085607428639597991459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55890057071619093065327639 83835085607428639597991459)
        ·
          refine ⟨125752628411142959396987189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83835085607428639597991459 125752628411142959396987189)
          ·
            refine ⟨11789308913544652443467549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125752628411142959396987189 11789308913544652443467549)
            ·
              refine ⟨4420990842579244666300331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11789308913544652443467549 4420990842579244666300331)
              ·
                refine ⟨6631486263868866999450497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4420990842579244666300331 6631486263868866999450497)
                ·
                  refine ⟨4973614697901650249587873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631486263868866999450497 4973614697901650249587873)
                  ·
                    refine ⟨3730211023426237687190905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4973614697901650249587873 3730211023426237687190905)
                    ·
                      refine ⟨2797658267569678265393179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730211023426237687190905 2797658267569678265393179)
                      ·
                        rfl

theorem cell23_5448420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_5448420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448420 prefixEnd_5448420 := by exact prefixLift 5448420
  have htrace : WordTrace (prefixWord ++ tailWord_5448420) baseStart_5448420 baseEnd_5448420 := by
    simpa [prefixWord, tailWord_5448420, baseEnd_5448420] using wordTrace_append hprefix tailTrace_5448420
  have hstable : (prefixWord ++ tailWord_5448420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448420).length < 2 ^ (prefixWord ++ tailWord_5448420).sum := by decide
  have hdescent : baseEnd_5448420 < baseStart_5448420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448526 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3]
def baseStart_5448526 : Nat := 118140960795 + 5448526 * 2 ^ 59
def prefixEnd_5448526 : Nat := 4983230072969 + 3 ^ 40 * 5448526 * 2
def baseEnd_5448526 : Nat := 2797712696519054850667691

theorem tailTrace_5448526 : CollatzResearch.WordTrace tailWord_5448526 prefixEnd_5448526 2797712696519054850667691 := by
  unfold tailWord_5448526
  simp only [CollatzResearch.WordTrace]
  refine ⟨24840508632366038875287679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132482712705952207334867621 24840508632366038875287679)
  ·
    refine ⟨37260762948549058312931519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24840508632366038875287679 37260762948549058312931519)
    ·
      refine ⟨55891144422823587469397279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37260762948549058312931519 55891144422823587469397279)
      ·
        refine ⟨83836716634235381204095919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55891144422823587469397279 83836716634235381204095919)
        ·
          refine ⟨125755074951353071806143879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83836716634235381204095919 125755074951353071806143879)
          ·
            refine ⟨188632612427029607709215819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125755074951353071806143879 188632612427029607709215819)
            ·
              refine ⟨282948918640544411563823729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188632612427029607709215819 282948918640544411563823729)
              ·
                refine ⟨212211688980408308672867797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282948918640544411563823729 212211688980408308672867797)
                ·
                  refine ⟨4973711460478319734520339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 212211688980408308672867797 4973711460478319734520339)
                  ·
                    refine ⟨7460567190717479601780509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4973711460478319734520339 7460567190717479601780509)
                    ·
                      refine ⟨2797712696519054850667691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7460567190717479601780509 2797712696519054850667691)
                      ·
                        rfl

theorem cell23_5448526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_5448526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448526 prefixEnd_5448526 := by exact prefixLift 5448526
  have htrace : WordTrace (prefixWord ++ tailWord_5448526) baseStart_5448526 baseEnd_5448526 := by
    simpa [prefixWord, tailWord_5448526, baseEnd_5448526] using wordTrace_append hprefix tailTrace_5448526
  have hstable : (prefixWord ++ tailWord_5448526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448526).length < 2 ^ (prefixWord ++ tailWord_5448526).sum := by decide
  have hdescent : baseEnd_5448526 < baseStart_5448526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448536 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 4, 3, 2]
def baseStart_5448536 : Nat := 118140960795 + 5448536 * 2 ^ 59
def prefixEnd_5448536 : Nat := 4983230072969 + 3 ^ 40 * 5448536 * 2
def baseEnd_5448536 : Nat := 2797717831325599811542645

theorem tailTrace_5448536 : CollatzResearch.WordTrace tailWord_5448536 prefixEnd_5448536 2797717831325599811542645 := by
  unfold tailWord_5448536
  simp only [CollatzResearch.WordTrace]
  refine ⟨99362216894446041355082731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132482955859261388473443641 99362216894446041355082731)
  ·
    refine ⟨149043325341669062032624097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99362216894446041355082731 149043325341669062032624097)
    ·
      refine ⟨111782494006251796524468073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149043325341669062032624097 111782494006251796524468073)
      ·
        refine ⟨83836870504688847393351055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111782494006251796524468073 83836870504688847393351055)
        ·
          refine ⟨125755305757033271090026583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83836870504688847393351055 125755305757033271090026583)
          ·
            refine ⟨188632958635549906635039875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125755305757033271090026583 188632958635549906635039875)
            ·
              refine ⟨282949437953324859952559813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188632958635549906635039875 282949437953324859952559813)
              ·
                refine ⟨53053019616248411241104965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282949437953324859952559813 53053019616248411241104965)
                ·
                  refine ⟨9947441178046577107707181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53053019616248411241104965 9947441178046577107707181)
                  ·
                    refine ⟨3730290441767466415390193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9947441178046577107707181 3730290441767466415390193)
                    ·
                      refine ⟨2797717831325599811542645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730290441767466415390193 2797717831325599811542645)
                      ·
                        rfl

theorem cell23_5448536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_5448536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448536 prefixEnd_5448536 := by exact prefixLift 5448536
  have htrace : WordTrace (prefixWord ++ tailWord_5448536) baseStart_5448536 baseEnd_5448536 := by
    simpa [prefixWord, tailWord_5448536, baseEnd_5448536] using wordTrace_append hprefix tailTrace_5448536
  have hstable : (prefixWord ++ tailWord_5448536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448536).length < 2 ^ (prefixWord ++ tailWord_5448536).sum := by decide
  have hdescent : baseEnd_5448536 < baseStart_5448536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448576 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 2, 4]
def baseStart_5448576 : Nat := 118140960795 + 5448576 * 2 ^ 59
def prefixEnd_5448576 : Nat := 4983230072969 + 3 ^ 40 * 5448576 * 2
def baseEnd_5448576 : Nat := 932579456850593218347487

theorem tailTrace_5448576 : CollatzResearch.WordTrace tailWord_5448576 prefixEnd_5448576 932579456850593218347487 := by
  unfold tailWord_5448576
  simp only [CollatzResearch.WordTrace]
  refine ⟨99362946354373584770810791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132483928472498113027747721 99362946354373584770810791)
  ·
    refine ⟨149044419531560377156216187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99362946354373584770810791 149044419531560377156216187)
    ·
      refine ⟨223566629297340565734324281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149044419531560377156216187 223566629297340565734324281)
      ·
        refine ⟨167674971973005424300743211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223566629297340565734324281 167674971973005424300743211)
        ·
          refine ⟨251512457959508136451114817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167674971973005424300743211 251512457959508136451114817)
          ·
            refine ⟨188634343469631102338336113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251512457959508136451114817 188634343469631102338336113)
            ·
              refine ⟨141475757602223326753752085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188634343469631102338336113 141475757602223326753752085)
              ·
                refine ⟨6631676137604218441582129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141475757602223326753752085 6631676137604218441582129)
                ·
                  refine ⟨4973757103203163831186597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631676137604218441582129 4973757103203163831186597)
                  ·
                    refine ⟨932579456850593218347487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4973757103203163831186597 932579456850593218347487)
                    ·
                      rfl

theorem cell23_5448576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 4].length) (baseStart_5448576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448576 prefixEnd_5448576 := by exact prefixLift 5448576
  have htrace : WordTrace (prefixWord ++ tailWord_5448576) baseStart_5448576 baseEnd_5448576 := by
    simpa [prefixWord, tailWord_5448576, baseEnd_5448576] using wordTrace_append hprefix tailTrace_5448576
  have hstable : (prefixWord ++ tailWord_5448576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448576).length < 2 ^ (prefixWord ++ tailWord_5448576).sum := by decide
  have hdescent : baseEnd_5448576 < baseStart_5448576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448579 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 6]
def baseStart_5448579 : Nat := 118140960795 + 5448579 * 2 ^ 59
def prefixEnd_5448579 : Nat := 4983230072969 + 3 ^ 40 * 5448579 * 2
def baseEnd_5448579 : Nat := 2797739910993743143304947

theorem tailTrace_5448579 : CollatzResearch.WordTrace tailWord_5448579 prefixEnd_5448579 2797739910993743143304947 := by
  unfold tailWord_5448579
  simp only [CollatzResearch.WordTrace]
  refine ⟨198726002127736301053980791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132484001418490867369320527 198726002127736301053980791)
  ·
    refine ⟨298089003191604451580971187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198726002127736301053980791 298089003191604451580971187)
    ·
      refine ⟨447133504787406677371456781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298089003191604451580971187 447133504787406677371456781)
      ·
        refine ⟨167675064295277504014296293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447133504787406677371456781 167675064295277504014296293)
        ·
          refine ⟨31439074555364532002680555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167675064295277504014296293 31439074555364532002680555)
          ·
            refine ⟨47158611833046798004020833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31439074555364532002680555 47158611833046798004020833)
            ·
              refine ⟨35368958874785098503015625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47158611833046798004020833 35368958874785098503015625)
              ·
                refine ⟨26526719156088823877261719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35368958874785098503015625 26526719156088823877261719)
                ·
                  refine ⟨39790078734133235815892579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26526719156088823877261719 39790078734133235815892579)
                  ·
                    refine ⟨59685118101199853723838869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39790078734133235815892579 59685118101199853723838869)
                    ·
                      refine ⟨2797739910993743143304947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59685118101199853723838869 2797739910993743143304947)
                      ·
                        rfl

theorem cell23_5448579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_5448579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448579 prefixEnd_5448579 := by exact prefixLift 5448579
  have htrace : WordTrace (prefixWord ++ tailWord_5448579) baseStart_5448579 baseEnd_5448579 := by
    simpa [prefixWord, tailWord_5448579, baseEnd_5448579] using wordTrace_append hprefix tailTrace_5448579
  have hstable : (prefixWord ++ tailWord_5448579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448579).length < 2 ^ (prefixWord ++ tailWord_5448579).sum := by decide
  have hdescent : baseEnd_5448579 < baseStart_5448579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448586 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5448586 : Nat := 118140960795 + 5448586 * 2 ^ 59
def prefixEnd_5448586 : Nat := 4983230072969 + 3 ^ 40 * 5448586 * 2
def baseEnd_5448586 : Nat := 2797743505358324615917415

theorem tailTrace_5448586 : CollatzResearch.WordTrace tailWord_5448586 prefixEnd_5448586 2797743505358324615917415 := by
  unfold tailWord_5448586
  simp only [CollatzResearch.WordTrace]
  refine ⟨49681564359677735312371403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132484171625807294166323741 49681564359677735312371403)
  ·
    refine ⟨74522346539516602968557105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49681564359677735312371403 74522346539516602968557105)
    ·
      refine ⟨55891759904637452226417829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74522346539516602968557105 55891759904637452226417829)
      ·
        refine ⟨10479704982119522292453343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55891759904637452226417829 10479704982119522292453343)
        ·
          refine ⟨15719557473179283438680015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10479704982119522292453343 15719557473179283438680015)
          ·
            refine ⟨23579336209768925158020023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15719557473179283438680015 23579336209768925158020023)
            ·
              refine ⟨35369004314653387737030035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23579336209768925158020023 35369004314653387737030035)
              ·
                refine ⟨53053506471980081605545053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35369004314653387737030035 53053506471980081605545053)
                ·
                  refine ⟨19895064926992530602079395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53053506471980081605545053 19895064926992530602079395)
                  ·
                    refine ⟨29842597390488795903119093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19895064926992530602079395 29842597390488795903119093)
                    ·
                      refine ⟨2797743505358324615917415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29842597390488795903119093 2797743505358324615917415)
                      ·
                        rfl

theorem cell23_5448586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5448586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448586 prefixEnd_5448586 := by exact prefixLift 5448586
  have htrace : WordTrace (prefixWord ++ tailWord_5448586) baseStart_5448586 baseEnd_5448586 := by
    simpa [prefixWord, tailWord_5448586, baseEnd_5448586] using wordTrace_append hprefix tailTrace_5448586
  have hstable : (prefixWord ++ tailWord_5448586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448586).length < 2 ^ (prefixWord ++ tailWord_5448586).sum := by decide
  have hdescent : baseEnd_5448586 < baseStart_5448586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448596 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_5448596 : Nat := 118140960795 + 5448596 * 2 ^ 59
def prefixEnd_5448596 : Nat := 4983230072969 + 3 ^ 40 * 5448596 * 2
def baseEnd_5448596 : Nat := 2797748640164869576792369

theorem tailTrace_5448596 : CollatzResearch.WordTrace tailWord_5448596 prefixEnd_5448596 2797748640164869576792369 := by
  unfold tailWord_5448596
  simp only [CollatzResearch.WordTrace]
  refine ⟨99363311084337356478674821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132484414779116475304899761 99363311084337356478674821)
  ·
    refine ⟨18630620828313254339751529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99363311084337356478674821 18630620828313254339751529)
    ·
      refine ⟨13972965621234940754813647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18630620828313254339751529 13972965621234940754813647)
      ·
        refine ⟨20959448431852411132220471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13972965621234940754813647 20959448431852411132220471)
        ·
          refine ⟨31439172647778616698330707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20959448431852411132220471 31439172647778616698330707)
          ·
            refine ⟨47158758971667925047496061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31439172647778616698330707 47158758971667925047496061)
            ·
              refine ⟨17684534614375471892811023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47158758971667925047496061 17684534614375471892811023)
              ·
                refine ⟨26526801921563207839216535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17684534614375471892811023 26526801921563207839216535)
                ·
                  refine ⟨39790202882344811758824803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26526801921563207839216535 39790202882344811758824803)
                  ·
                    refine ⟨59685304323517217638237205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39790202882344811758824803 59685304323517217638237205)
                    ·
                      refine ⟨2797748640164869576792369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59685304323517217638237205 2797748640164869576792369)
                      ·
                        rfl

theorem cell23_5448596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_5448596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448596 prefixEnd_5448596 := by exact prefixLift 5448596
  have htrace : WordTrace (prefixWord ++ tailWord_5448596) baseStart_5448596 baseEnd_5448596 := by
    simpa [prefixWord, tailWord_5448596, baseEnd_5448596] using wordTrace_append hprefix tailTrace_5448596
  have hstable : (prefixWord ++ tailWord_5448596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448596).length < 2 ^ (prefixWord ++ tailWord_5448596).sum := by decide
  have hdescent : baseEnd_5448596 < baseStart_5448596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448633 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 3]
def baseStart_5448633 : Nat := 118140960795 + 5448633 * 2 ^ 59
def prefixEnd_5448633 : Nat := 4983230072969 + 3 ^ 40 * 5448633 * 2
def baseEnd_5448633 : Nat := 2797767638949085932029699

theorem tailTrace_5448633 : CollatzResearch.WordTrace tailWord_5448633 prefixEnd_5448633 2797767638949085932029699 := by
  unfold tailWord_5448633
  simp only [CollatzResearch.WordTrace]
  refine ⟨198727971669540668276446553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132485314446360445517631035 198727971669540668276446553)
  ·
    refine ⟨149045978752155501207334915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198727971669540668276446553 149045978752155501207334915)
    ·
      refine ⟨223568968128233251811002373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149045978752155501207334915 223568968128233251811002373)
      ·
        refine ⟨41919181524043734714562945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223568968128233251811002373 41919181524043734714562945)
        ·
          refine ⟨31439386143032801035922209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41919181524043734714562945 31439386143032801035922209)
          ·
            refine ⟨23579539607274600776941657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31439386143032801035922209 23579539607274600776941657)
            ·
              refine ⟨17684654705455950582706243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23579539607274600776941657 17684654705455950582706243)
              ·
                refine ⟨26526982058183925874059365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17684654705455950582706243 26526982058183925874059365)
                ·
                  refine ⟨4973809135909486101386131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26526982058183925874059365 4973809135909486101386131)
                  ·
                    refine ⟨7460713703864229152079197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4973809135909486101386131 7460713703864229152079197)
                    ·
                      refine ⟨2797767638949085932029699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7460713703864229152079197 2797767638949085932029699)
                      ·
                        rfl

theorem cell23_5448633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_5448633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448633 prefixEnd_5448633 := by exact prefixLift 5448633
  have htrace : WordTrace (prefixWord ++ tailWord_5448633) baseStart_5448633 baseEnd_5448633 := by
    simpa [prefixWord, tailWord_5448633, baseEnd_5448633] using wordTrace_append hprefix tailTrace_5448633
  have hstable : (prefixWord ++ tailWord_5448633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448633).length < 2 ^ (prefixWord ++ tailWord_5448633).sum := by decide
  have hdescent : baseEnd_5448633 < baseStart_5448633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448644 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_5448644 : Nat := 118140960795 + 5448644 * 2 ^ 59
def prefixEnd_5448644 : Nat := 4983230072969 + 3 ^ 40 * 5448644 * 2
def baseEnd_5448644 : Nat := 932591095745428462997383

theorem tailTrace_5448644 : CollatzResearch.WordTrace tailWord_5448644 prefixEnd_5448644 932591095745428462997383 := by
  unfold tailWord_5448644
  simp only [CollatzResearch.WordTrace]
  refine ⟨99364186436250408577548493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132485581915000544770064657 99364186436250408577548493)
  ·
    refine ⟨37261569913593903216580685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99364186436250408577548493 37261569913593903216580685)
    ·
      refine ⟨13973088717597713706217757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37261569913593903216580685 13973088717597713706217757)
      ·
        refine ⟨5239908269099142639831659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13973088717597713706217757 5239908269099142639831659)
        ·
          refine ⟨7859862403648713959747489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5239908269099142639831659 7859862403648713959747489)
          ·
            refine ⟨5894896802736535469810617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859862403648713959747489 5894896802736535469810617)
            ·
              refine ⟨4421172602052401602357963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5894896802736535469810617 4421172602052401602357963)
              ·
                refine ⟨6631758903078602403536945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421172602052401602357963 6631758903078602403536945)
                ·
                  refine ⟨4973819177308951802652709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631758903078602403536945 4973819177308951802652709)
                  ·
                    refine ⟨932591095745428462997383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4973819177308951802652709 932591095745428462997383)
                    ·
                      rfl

theorem cell23_5448644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_5448644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448644 prefixEnd_5448644 := by exact prefixLift 5448644
  have htrace : WordTrace (prefixWord ++ tailWord_5448644) baseStart_5448644 baseEnd_5448644 := by
    simpa [prefixWord, tailWord_5448644, baseEnd_5448644] using wordTrace_append hprefix tailTrace_5448644
  have hstable : (prefixWord ++ tailWord_5448644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448644).length < 2 ^ (prefixWord ++ tailWord_5448644).sum := by decide
  have hdescent : baseEnd_5448644 < baseStart_5448644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448660 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_5448660 : Nat := 118140960795 + 5448660 * 2 ^ 59
def prefixEnd_5448660 : Nat := 4983230072969 + 3 ^ 40 * 5448660 * 2
def baseEnd_5448660 : Nat := 2797781502926757326392075

theorem tailTrace_5448660 : CollatzResearch.WordTrace tailWord_5448660 prefixEnd_5448660 2797781502926757326392075 := by
  unfold tailWord_5448660
  simp only [CollatzResearch.WordTrace]
  refine ⟨99364478220221425943839717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132485970960295234591786289 99364478220221425943839717)
  ·
    refine ⟨18630839666291517364469947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99364478220221425943839717 18630839666291517364469947)
    ·
      refine ⟨27946259499437276046704921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18630839666291517364469947 27946259499437276046704921)
      ·
        refine ⟨20959694624577957035028691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27946259499437276046704921 20959694624577957035028691)
        ·
          refine ⟨31439541936866935552543037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20959694624577957035028691 31439541936866935552543037)
          ·
            refine ⟨11789828226325100832203639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31439541936866935552543037 11789828226325100832203639)
            ·
              refine ⟨17684742339487651248305459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11789828226325100832203639 17684742339487651248305459)
              ·
                refine ⟨26527113509231476872458189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17684742339487651248305459 26527113509231476872458189)
                ·
                  refine ⟨9947667565961803827171821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26527113509231476872458189 9947667565961803827171821)
                  ·
                    refine ⟨3730375337235676435189433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9947667565961803827171821 3730375337235676435189433)
                    ·
                      refine ⟨2797781502926757326392075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730375337235676435189433 2797781502926757326392075)
                      ·
                        rfl

theorem cell23_5448660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_5448660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448660 prefixEnd_5448660 := by exact prefixLift 5448660
  have htrace : WordTrace (prefixWord ++ tailWord_5448660) baseStart_5448660 baseEnd_5448660 := by
    simpa [prefixWord, tailWord_5448660, baseEnd_5448660] using wordTrace_append hprefix tailTrace_5448660
  have hstable : (prefixWord ++ tailWord_5448660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448660).length < 2 ^ (prefixWord ++ tailWord_5448660).sum := by decide
  have hdescent : baseEnd_5448660 < baseStart_5448660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448699 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 8]
def baseStart_5448699 : Nat := 118140960795 + 5448699 * 2 ^ 59
def prefixEnd_5448699 : Nat := 4983230072969 + 3 ^ 40 * 5448699 * 2
def baseEnd_5448699 : Nat := 2797801528672282673804395

theorem tailTrace_5448699 : CollatzResearch.WordTrace tailWord_5448699 prefixEnd_5448699 2797801528672282673804395 := by
  unfold tailWord_5448699
  simp only [CollatzResearch.WordTrace]
  refine ⟨198730378887301561548349151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132486919258201041032232767 198730378887301561548349151)
  ·
    refine ⟨298095568330952342322523727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198730378887301561548349151 298095568330952342322523727)
    ·
      refine ⟨447143352496428513483785591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298095568330952342322523727 447143352496428513483785591)
      ·
        refine ⟨670715028744642770225678387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447143352496428513483785591 670715028744642770225678387)
        ·
          refine ⟨1006072543116964155338517581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670715028744642770225678387 1006072543116964155338517581)
          ·
            refine ⟨377277203668861558251944093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1006072543116964155338517581 377277203668861558251944093)
            ·
              refine ⟨141478951375823084344479035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 377277203668861558251944093 141478951375823084344479035)
              ·
                refine ⟨212218427063734626516718553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141478951375823084344479035 212218427063734626516718553)
                ·
                  refine ⟨159163820297800969887538915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212218427063734626516718553 159163820297800969887538915)
                  ·
                    refine ⟨238745730446701454831308373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159163820297800969887538915 238745730446701454831308373)
                    ·
                      refine ⟨2797801528672282673804395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 238745730446701454831308373 2797801528672282673804395)
                      ·
                        rfl

theorem cell23_5448699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_5448699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448699 prefixEnd_5448699 := by exact prefixLift 5448699
  have htrace : WordTrace (prefixWord ++ tailWord_5448699) baseStart_5448699 baseEnd_5448699 := by
    simpa [prefixWord, tailWord_5448699, baseEnd_5448699] using wordTrace_append hprefix tailTrace_5448699
  have hstable : (prefixWord ++ tailWord_5448699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448699).length < 2 ^ (prefixWord ++ tailWord_5448699).sum := by decide
  have hdescent : baseEnd_5448699 < baseStart_5448699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448773 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_5448773 : Nat := 118140960795 + 5448773 * 2 ^ 59
def prefixEnd_5448773 : Nat := 4983230072969 + 3 ^ 40 * 5448773 * 2
def baseEnd_5448773 : Nat := 932613175413571794759685

theorem tailTrace_5448773 : CollatzResearch.WordTrace tailWord_5448773 prefixEnd_5448773 932613175413571794759685 := by
  unfold tailWord_5448773
  simp only [CollatzResearch.WordTrace]
  refine ⟨198733077889033472186542973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132488718592688981457695315 198733077889033472186542973)
  ·
    refine ⟨74524904208387552069953615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198733077889033472186542973 74524904208387552069953615)
    ·
      refine ⟨111787356312581328104930423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74524904208387552069953615 111787356312581328104930423)
      ·
        refine ⟨167681034468871992157395635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111787356312581328104930423 167681034468871992157395635)
        ·
          refine ⟨251521551703307988236093453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167681034468871992157395635 251521551703307988236093453)
          ·
            refine ⟨94320581888740495588535045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251521551703307988236093453 94320581888740495588535045)
            ·
              refine ⟨17685109104138842922850321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94320581888740495588535045 17685109104138842922850321)
              ·
                refine ⟨13263831828104132192137741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17685109104138842922850321 13263831828104132192137741)
                ·
                  refine ⟨4973936935539049572051653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13263831828104132192137741 4973936935539049572051653)
                  ·
                    refine ⟨932613175413571794759685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4973936935539049572051653 932613175413571794759685)
                    ·
                      rfl

theorem cell23_5448773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_5448773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448773 prefixEnd_5448773 := by exact prefixLift 5448773
  have htrace : WordTrace (prefixWord ++ tailWord_5448773) baseStart_5448773 baseEnd_5448773 := by
    simpa [prefixWord, tailWord_5448773, baseEnd_5448773] using wordTrace_append hprefix tailTrace_5448773
  have hstable : (prefixWord ++ tailWord_5448773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448773).length < 2 ^ (prefixWord ++ tailWord_5448773).sum := by decide
  have hdescent : baseEnd_5448773 < baseStart_5448773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448776 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_5448776 : Nat := 118140960795 + 5448776 * 2 ^ 59
def prefixEnd_5448776 : Nat := 4983230072969 + 3 ^ 40 * 5448776 * 2
def baseEnd_5448776 : Nat := 2797841066682678872541541

theorem tailTrace_5448776 : CollatzResearch.WordTrace tailWord_5448776 prefixEnd_5448776 2797841066682678872541541 := by
  unfold tailWord_5448776
  simp only [CollatzResearch.WordTrace]
  refine ⟨99366593654011301849451091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132488791538681735799268121 99366593654011301849451091)
  ·
    refine ⟨149049890481016952774176637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99366593654011301849451091 149049890481016952774176637)
    ·
      refine ⟨55893708930381357290316239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149049890481016952774176637 55893708930381357290316239)
      ·
        refine ⟨83840563395572035935474359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55893708930381357290316239 83840563395572035935474359)
        ·
          refine ⟨125760845093358053903211539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83840563395572035935474359 125760845093358053903211539)
          ·
            refine ⟨188641267640037080854817309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125760845093358053903211539 188641267640037080854817309)
            ·
              refine ⟨70740475365013905320556491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188641267640037080854817309 70740475365013905320556491)
              ·
                refine ⟨106110713047520857980834737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70740475365013905320556491 106110713047520857980834737)
                ·
                  refine ⟨79583034785640643485626053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106110713047520857980834737 79583034785640643485626053)
                  ·
                    refine ⟨14921819022307620653554885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79583034785640643485626053 14921819022307620653554885)
                    ·
                      refine ⟨2797841066682678872541541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14921819022307620653554885 2797841066682678872541541)
                      ·
                        rfl

theorem cell23_5448776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_5448776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448776 prefixEnd_5448776 := by exact prefixLift 5448776
  have htrace : WordTrace (prefixWord ++ tailWord_5448776) baseStart_5448776 baseEnd_5448776 := by
    simpa [prefixWord, tailWord_5448776, baseEnd_5448776] using wordTrace_append hprefix tailTrace_5448776
  have hstable : (prefixWord ++ tailWord_5448776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448776).length < 2 ^ (prefixWord ++ tailWord_5448776).sum := by decide
  have hdescent : baseEnd_5448776 < baseStart_5448776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448797 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5448797 : Nat := 118140960795 + 5448797 * 2 ^ 59
def prefixEnd_5448797 : Nat := 4983230072969 + 3 ^ 40 * 5448797 * 2
def baseEnd_5448797 : Nat := 2797851849776423290378945

theorem tailTrace_5448797 : CollatzResearch.WordTrace tailWord_5448797 prefixEnd_5448797 2797851849776423290378945 := by
  unfold tailWord_5448797
  simp only [CollatzResearch.WordTrace]
  refine ⟨198733953240946524285416645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132489302160631016190277763 198733953240946524285416645)
  ·
    refine ⟨37262616232677473303515621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198733953240946524285416645 37262616232677473303515621)
    ·
      refine ⟨6986740543627026244409179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37262616232677473303515621 6986740543627026244409179)
      ·
        refine ⟨10480110815440539366613769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6986740543627026244409179 10480110815440539366613769)
        ·
          refine ⟨7860083111580404524960327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10480110815440539366613769 7860083111580404524960327)
          ·
            refine ⟨11790124667370606787440491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7860083111580404524960327 11790124667370606787440491)
            ·
              refine ⟨17685187001055910181160737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11790124667370606787440491 17685187001055910181160737)
              ·
                refine ⟨13263890250791932635870553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17685187001055910181160737 13263890250791932635870553)
                ·
                  refine ⟨9947917688093949476902915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13263890250791932635870553 9947917688093949476902915)
                  ·
                    refine ⟨14921876532140924215354373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9947917688093949476902915 14921876532140924215354373)
                    ·
                      refine ⟨2797851849776423290378945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14921876532140924215354373 2797851849776423290378945)
                      ·
                        rfl

theorem cell23_5448797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5448797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448797 prefixEnd_5448797 := by exact prefixLift 5448797
  have htrace : WordTrace (prefixWord ++ tailWord_5448797) baseStart_5448797 baseEnd_5448797 := by
    simpa [prefixWord, tailWord_5448797, baseEnd_5448797] using wordTrace_append hprefix tailTrace_5448797
  have hstable : (prefixWord ++ tailWord_5448797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448797).length < 2 ^ (prefixWord ++ tailWord_5448797).sum := by decide
  have hdescent : baseEnd_5448797 < baseStart_5448797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448876 : List Nat := [2, 2, 1, 1, 1, 1, 1, 14]
def baseStart_5448876 : Nat := 118140960795 + 5448876 * 2 ^ 59
def prefixEnd_5448876 : Nat := 4983230072969 + 3 ^ 40 * 5448876 * 2
def baseEnd_5448876 : Nat := 103625644990671425233003

theorem tailTrace_5448876 : CollatzResearch.WordTrace tailWord_5448876 prefixEnd_5448876 103625644990671425233003 := by
  unfold tailWord_5448876
  simp only [CollatzResearch.WordTrace]
  refine ⟨99368417303830160388771241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132491223071773547185028321 99368417303830160388771241)
  ·
    refine ⟨74526312977872620291578431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99368417303830160388771241 74526312977872620291578431)
    ·
      refine ⟨111789469466808930437367647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74526312977872620291578431 111789469466808930437367647)
      ·
        refine ⟨167684204200213395656051471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111789469466808930437367647 167684204200213395656051471)
        ·
          refine ⟨251526306300320093484077207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167684204200213395656051471 251526306300320093484077207)
          ·
            refine ⟨377289459450480140226115811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251526306300320093484077207 377289459450480140226115811)
            ·
              refine ⟨565934189175720210339173717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377289459450480140226115811 565934189175720210339173717)
              ·
                refine ⟨103625644990671425233003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 565934189175720210339173717 103625644990671425233003)
                ·
                  rfl

theorem cell23_5448876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 14].length) (baseStart_5448876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448876 prefixEnd_5448876 := by exact prefixLift 5448876
  have htrace : WordTrace (prefixWord ++ tailWord_5448876) baseStart_5448876 baseEnd_5448876 := by
    simpa [prefixWord, tailWord_5448876, baseEnd_5448876] using wordTrace_append hprefix tailTrace_5448876
  have hstable : (prefixWord ++ tailWord_5448876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448876).length < 2 ^ (prefixWord ++ tailWord_5448876).sum := by decide
  have hdescent : baseEnd_5448876 < baseStart_5448876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448883 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 4]
def baseStart_5448883 : Nat := 118140960795 + 5448883 * 2 ^ 59
def prefixEnd_5448883 : Nat := 4983230072969 + 3 ^ 40 * 5448883 * 2
def baseEnd_5448883 : Nat := 2797896009112709953903549

theorem tailTrace_5448883 : CollatzResearch.WordTrace tailWord_5448883 prefixEnd_5448883 2797896009112709953903549 := by
  unfold tailWord_5448883
  simp only [CollatzResearch.WordTrace]
  refine ⟨198737089918634960973047303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132491393279089973982031535 198737089918634960973047303)
  ·
    refine ⟨298105634877952441459570955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198737089918634960973047303 298105634877952441459570955)
    ·
      refine ⟨447158452316928662189356433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298105634877952441459570955 447158452316928662189356433)
      ·
        refine ⟨335368839237696496642017325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447158452316928662189356433 335368839237696496642017325)
        ·
          refine ⟨125763314714136186240756497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335368839237696496642017325 125763314714136186240756497)
          ·
            refine ⟨94322486035602139680567373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125763314714136186240756497 94322486035602139680567373)
            ·
              refine ⟨35370932263350802380212765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94322486035602139680567373 35370932263350802380212765)
              ·
                refine ⟨13264099598756550892579787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35370932263350802380212765 13264099598756550892579787)
                ·
                  refine ⟨19896149398134826338869681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13264099598756550892579787 19896149398134826338869681)
                  ·
                    refine ⟨14922112048601119754152261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19896149398134826338869681 14922112048601119754152261)
                    ·
                      refine ⟨2797896009112709953903549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14922112048601119754152261 2797896009112709953903549)
                      ·
                        rfl

theorem cell23_5448883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_5448883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448883 prefixEnd_5448883 := by exact prefixLift 5448883
  have htrace : WordTrace (prefixWord ++ tailWord_5448883) baseStart_5448883 baseEnd_5448883 := by
    simpa [prefixWord, tailWord_5448883, baseEnd_5448883] using wordTrace_append hprefix tailTrace_5448883
  have hstable : (prefixWord ++ tailWord_5448883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448883).length < 2 ^ (prefixWord ++ tailWord_5448883).sum := by decide
  have hdescent : baseEnd_5448883 < baseStart_5448883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448887 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 3, 2, 2]
def baseStart_5448887 : Nat := 118140960795 + 5448887 * 2 ^ 59
def prefixEnd_5448887 : Nat := 4983230072969 + 3 ^ 40 * 5448887 * 2
def baseEnd_5448887 : Nat := 2797898063035327938253531

theorem tailTrace_5448887 : CollatzResearch.WordTrace tailWord_5448887 prefixEnd_5448887 2797898063035327938253531 := by
  unfold tailWord_5448887
  simp only [CollatzResearch.WordTrace]
  refine ⟨198737235810620469656192915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132491490540413646437461943 198737235810620469656192915)
  ·
    refine ⟨298105853715930704484289373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198737235810620469656192915 298105853715930704484289373)
    ·
      refine ⟨111789695143474014181608515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298105853715930704484289373 111789695143474014181608515)
      ·
        refine ⟨167684542715211021272412773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111789695143474014181608515 167684542715211021272412773)
        ·
          refine ⟨31440851759102066488577395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167684542715211021272412773 31440851759102066488577395)
          ·
            refine ⟨47161277638653099732866093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31440851759102066488577395 47161277638653099732866093)
            ·
              refine ⟨17685479114494912399824785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47161277638653099732866093 17685479114494912399824785)
              ·
                refine ⟨13264109335871184299868589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17685479114494912399824785 13264109335871184299868589)
                ·
                  refine ⟨4974041000951694112450721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13264109335871184299868589 4974041000951694112450721)
                  ·
                    refine ⟨3730530750713770584338041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4974041000951694112450721 3730530750713770584338041)
                    ·
                      refine ⟨2797898063035327938253531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730530750713770584338041 2797898063035327938253531)
                      ·
                        rfl

theorem cell23_5448887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_5448887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448887 prefixEnd_5448887 := by exact prefixLift 5448887
  have htrace : WordTrace (prefixWord ++ tailWord_5448887) baseStart_5448887 baseEnd_5448887 := by
    simpa [prefixWord, tailWord_5448887, baseEnd_5448887] using wordTrace_append hprefix tailTrace_5448887
  have hstable : (prefixWord ++ tailWord_5448887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448887).length < 2 ^ (prefixWord ++ tailWord_5448887).sum := by decide
  have hdescent : baseEnd_5448887 < baseStart_5448887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448890 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3]
def baseStart_5448890 : Nat := 118140960795 + 5448890 * 2 ^ 59
def prefixEnd_5448890 : Nat := 4983230072969 + 3 ^ 40 * 5448890 * 2
def baseEnd_5448890 : Nat := 2797899603477291426516017

theorem tailTrace_5448890 : CollatzResearch.WordTrace tailWord_5448890 prefixEnd_5448890 2797899603477291426516017 := by
  unfold tailWord_5448890
  simp only [CollatzResearch.WordTrace]
  refine ⟨49684336307402400292138031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132491563486406400779034749 49684336307402400292138031)
  ·
    refine ⟨74526504461103600438207047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49684336307402400292138031 74526504461103600438207047)
    ·
      refine ⟨111789756691655400657310571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74526504461103600438207047 111789756691655400657310571)
      ·
        refine ⟨167684635037483100985965857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111789756691655400657310571 167684635037483100985965857)
        ·
          refine ⟨125763476278112325739474393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167684635037483100985965857 125763476278112325739474393)
          ·
            refine ⟨94322607208584244304605795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125763476278112325739474393 94322607208584244304605795)
            ·
              refine ⟨141483910812876366456908693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94322607208584244304605795 141483910812876366456908693)
              ·
                refine ⟨6632058319353579677667595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141483910812876366456908693 6632058319353579677667595)
                ·
                  refine ⟨9948087479030369516501393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632058319353579677667595 9948087479030369516501393)
                  ·
                    refine ⟨7461065609272777137376045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9948087479030369516501393 7461065609272777137376045)
                    ·
                      refine ⟨2797899603477291426516017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7461065609272777137376045 2797899603477291426516017)
                      ·
                        rfl

theorem cell23_5448890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_5448890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448890 prefixEnd_5448890 := by exact prefixLift 5448890
  have htrace : WordTrace (prefixWord ++ tailWord_5448890) baseStart_5448890 baseEnd_5448890 := by
    simpa [prefixWord, tailWord_5448890, baseEnd_5448890] using wordTrace_append hprefix tailTrace_5448890
  have hstable : (prefixWord ++ tailWord_5448890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448890).length < 2 ^ (prefixWord ++ tailWord_5448890).sum := by decide
  have hdescent : baseEnd_5448890 < baseStart_5448890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448904 : List Nat := [2, 1, 3, 1, 2, 1, 3, 5, 1, 2, 2]
def baseStart_5448904 : Nat := 118140960795 + 5448904 * 2 ^ 59
def prefixEnd_5448904 : Nat := 4983230072969 + 3 ^ 40 * 5448904 * 2
def baseEnd_5448904 : Nat := 2797906792206454371740953

theorem tailTrace_5448904 : CollatzResearch.WordTrace tailWord_5448904 prefixEnd_5448904 2797906792206454371740953 := by
  unfold tailWord_5448904
  simp only [CollatzResearch.WordTrace]
  refine ⟨99368927925779440779780883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132491903901039254373041177 99368927925779440779780883)
  ·
    refine ⟨149053391888669161169671325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99368927925779440779780883 149053391888669161169671325)
    ·
      refine ⟨55895021958250935438626747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149053391888669161169671325 55895021958250935438626747)
      ·
        refine ⟨83842532937376403157940121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55895021958250935438626747 83842532937376403157940121)
        ·
          refine ⟨62881899703032302368455091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83842532937376403157940121 62881899703032302368455091)
          ·
            refine ⟨94322849554548453552682637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62881899703032302368455091 94322849554548453552682637)
            ·
              refine ⟨35371068582955670082255989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94322849554548453552682637 35371068582955670082255989)
              ·
                refine ⟨3316037679652094070211499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35371068582955670082255989 3316037679652094070211499)
                ·
                  refine ⟨4974056519478141105317249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316037679652094070211499 4974056519478141105317249)
                  ·
                    refine ⟨3730542389608605828987937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4974056519478141105317249 3730542389608605828987937)
                    ·
                      refine ⟨2797906792206454371740953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730542389608605828987937 2797906792206454371740953)
                      ·
                        rfl

theorem cell23_5448904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_5448904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448904 prefixEnd_5448904 := by exact prefixLift 5448904
  have htrace : WordTrace (prefixWord ++ tailWord_5448904) baseStart_5448904 baseEnd_5448904 := by
    simpa [prefixWord, tailWord_5448904, baseEnd_5448904] using wordTrace_append hprefix tailTrace_5448904
  have hstable : (prefixWord ++ tailWord_5448904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448904).length < 2 ^ (prefixWord ++ tailWord_5448904).sum := by decide
  have hdescent : baseEnd_5448904 < baseStart_5448904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448947 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 1, 3, 2]
def baseStart_5448947 : Nat := 118140960795 + 5448947 * 2 ^ 59
def prefixEnd_5448947 : Nat := 4983230072969 + 3 ^ 40 * 5448947 * 2
def baseEnd_5448947 : Nat := 2797928871874597703503255

theorem tailTrace_5448947 : CollatzResearch.WordTrace tailWord_5448947 prefixEnd_5448947 2797928871874597703503255 := by
  unfold tailWord_5448947
  simp only [CollatzResearch.WordTrace]
  refine ⟨198739424190403099903377095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132492949460268733268918063 198739424190403099903377095)
  ·
    refine ⟨298109136285604649855065643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198739424190403099903377095 298109136285604649855065643)
    ·
      refine ⟨447163704428406974782598465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298109136285604649855065643 447163704428406974782598465)
      ·
        refine ⟨335372778321305231086948849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447163704428406974782598465 335372778321305231086948849)
        ·
          refine ⟨251529583740978923315211637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335372778321305231086948849 251529583740978923315211637)
          ·
            refine ⟨23580898475716774060801091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 251529583740978923315211637 23580898475716774060801091)
            ·
              refine ⟨35371347713575161091201637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23580898475716774060801091 35371347713575161091201637)
              ·
                refine ⟨6632127696295342704600307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35371347713575161091201637 6632127696295342704600307)
                ·
                  refine ⟨9948191544443014056900461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632127696295342704600307 9948191544443014056900461)
                  ·
                    refine ⟨3730571829166130271337673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9948191544443014056900461 3730571829166130271337673)
                    ·
                      refine ⟨2797928871874597703503255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730571829166130271337673 2797928871874597703503255)
                      ·
                        rfl

theorem cell23_5448947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 3, 2].length) (baseStart_5448947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448947 prefixEnd_5448947 := by exact prefixLift 5448947
  have htrace : WordTrace (prefixWord ++ tailWord_5448947) baseStart_5448947 baseEnd_5448947 := by
    simpa [prefixWord, tailWord_5448947, baseEnd_5448947] using wordTrace_append hprefix tailTrace_5448947
  have hstable : (prefixWord ++ tailWord_5448947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448947).length < 2 ^ (prefixWord ++ tailWord_5448947).sum := by decide
  have hdescent : baseEnd_5448947 < baseStart_5448947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448960 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 3, 4, 2]
def baseStart_5448960 : Nat := 118140960795 + 5448960 * 2 ^ 59
def prefixEnd_5448960 : Nat := 4983230072969 + 3 ^ 40 * 5448960 * 2
def baseEnd_5448960 : Nat := 2797935547123106152640695

theorem tailTrace_5448960 : CollatzResearch.WordTrace tailWord_5448960 prefixEnd_5448960 2797935547123106152640695 := by
  unfold tailWord_5448960
  simp only [CollatzResearch.WordTrace]
  refine ⟨99369949169678001561800167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132493265559570668749066889 99369949169678001561800167)
  ·
    refine ⟨149054923754517002342700251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99369949169678001561800167 149054923754517002342700251)
    ·
      refine ⟨223582385631775503514050377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149054923754517002342700251 223582385631775503514050377)
      ·
        refine ⟨167686789223831627635537783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223582385631775503514050377 167686789223831627635537783)
        ·
          refine ⟨251530183835747441453306675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167686789223831627635537783 251530183835747441453306675)
          ·
            refine ⟨377295275753621162179960013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251530183835747441453306675 377295275753621162179960013)
            ·
              refine ⟨141485728407607935817485005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 377295275753621162179960013 141485728407607935817485005)
              ·
                refine ⟨53057148152852975931556877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141485728407607935817485005 53057148152852975931556877)
                ·
                  refine ⟨19896430557319865974333829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53057148152852975931556877 19896430557319865974333829)
                  ·
                    refine ⟨3730580729497474870187593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19896430557319865974333829 3730580729497474870187593)
                    ·
                      refine ⟨2797935547123106152640695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730580729497474870187593 2797935547123106152640695)
                      ·
                        rfl

theorem cell23_5448960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_5448960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448960 prefixEnd_5448960 := by exact prefixLift 5448960
  have htrace : WordTrace (prefixWord ++ tailWord_5448960) baseStart_5448960 baseEnd_5448960 := by
    simpa [prefixWord, tailWord_5448960, baseEnd_5448960] using wordTrace_append hprefix tailTrace_5448960
  have hstable : (prefixWord ++ tailWord_5448960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448960).length < 2 ^ (prefixWord ++ tailWord_5448960).sum := by decide
  have hdescent : baseEnd_5448960 < baseStart_5448960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448963 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 5]
def baseStart_5448963 : Nat := 118140960795 + 5448963 * 2 ^ 59
def prefixEnd_5448963 : Nat := 4983230072969 + 3 ^ 40 * 5448963 * 2
def baseEnd_5448963 : Nat := 2797937087565069640903181

theorem tailTrace_5448963 : CollatzResearch.WordTrace tailWord_5448963 prefixEnd_5448963 2797937087565069640903181 := by
  unfold tailWord_5448963
  simp only [CollatzResearch.WordTrace]
  refine ⟨198740007758345134635959543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132493338505563423090639695 198740007758345134635959543)
  ·
    refine ⟨298110011637517701953939315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198740007758345134635959543 298110011637517701953939315)
    ·
      refine ⟨447165017456276552930908973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298110011637517701953939315 447165017456276552930908973)
      ·
        refine ⟨167686881546103707349090865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447165017456276552930908973 167686881546103707349090865)
        ·
          refine ⟨125765161159577780511818149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167686881546103707349090865 125765161159577780511818149)
          ·
            refine ⟨23580967717420833845965903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125765161159577780511818149 23580967717420833845965903)
            ·
              refine ⟨35371451576131250768948855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23580967717420833845965903 35371451576131250768948855)
              ·
                refine ⟨53057177364196876153423283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35371451576131250768948855 53057177364196876153423283)
                ·
                  refine ⟨79585766046295314230134925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53057177364196876153423283 79585766046295314230134925)
                  ·
                    refine ⟨29844662267360742836300597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79585766046295314230134925 29844662267360742836300597)
                    ·
                      refine ⟨2797937087565069640903181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29844662267360742836300597 2797937087565069640903181)
                      ·
                        rfl

theorem cell23_5448963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_5448963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448963 prefixEnd_5448963 := by exact prefixLift 5448963
  have htrace : WordTrace (prefixWord ++ tailWord_5448963) baseStart_5448963 baseEnd_5448963 := by
    simpa [prefixWord, tailWord_5448963, baseEnd_5448963] using wordTrace_append hprefix tailTrace_5448963
  have hstable : (prefixWord ++ tailWord_5448963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448963).length < 2 ^ (prefixWord ++ tailWord_5448963).sum := by decide
  have hdescent : baseEnd_5448963 < baseStart_5448963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448964 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_5448964 : Nat := 118140960795 + 5448964 * 2 ^ 59
def prefixEnd_5448964 : Nat := 4983230072969 + 3 ^ 40 * 5448964 * 2
def baseEnd_5448964 : Nat := 2797937601045724136990677

theorem tailTrace_5448964 : CollatzResearch.WordTrace tailWord_5448964 prefixEnd_5448964 2797937601045724136990677 := by
  unfold tailWord_5448964
  simp only [CollatzResearch.WordTrace]
  refine ⟨99370022115670755903372973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132493362820894341204497297 99370022115670755903372973)
  ·
    refine ⟨37263758293376533463764865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99370022115670755903372973 37263758293376533463764865)
    ·
      refine ⟨27947818720032400097823649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37263758293376533463764865 27947818720032400097823649)
      ·
        refine ⟨20960864040024300073367737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27947818720032400097823649 20960864040024300073367737)
        ·
          refine ⟨15720648030018225055025803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20960864040024300073367737 15720648030018225055025803)
          ·
            refine ⟨23580972045027337582538705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15720648030018225055025803 23580972045027337582538705)
            ·
              refine ⟨17685729033770503186904029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23580972045027337582538705 17685729033770503186904029)
              ·
                refine ⟨6632148387663938695089011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17685729033770503186904029 6632148387663938695089011)
                ·
                  refine ⟨9948222581495908042633517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632148387663938695089011 9948222581495908042633517)
                  ·
                    refine ⟨3730583468060965515987569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9948222581495908042633517 3730583468060965515987569)
                    ·
                      refine ⟨2797937601045724136990677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730583468060965515987569 2797937601045724136990677)
                      ·
                        rfl

theorem cell23_5448964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_5448964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448964 prefixEnd_5448964 := by exact prefixLift 5448964
  have htrace : WordTrace (prefixWord ++ tailWord_5448964) baseStart_5448964 baseEnd_5448964 := by
    simpa [prefixWord, tailWord_5448964, baseEnd_5448964] using wordTrace_append hprefix tailTrace_5448964
  have hstable : (prefixWord ++ tailWord_5448964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448964).length < 2 ^ (prefixWord ++ tailWord_5448964).sum := by decide
  have hdescent : baseEnd_5448964 < baseStart_5448964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5448977 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 4, 2, 2]
def baseStart_5448977 : Nat := 118140960795 + 5448977 * 2 ^ 59
def prefixEnd_5448977 : Nat := 4983230072969 + 3 ^ 40 * 5448977 * 2
def baseEnd_5448977 : Nat := 2797944276294232586128117

theorem tailTrace_5448977 : CollatzResearch.WordTrace tailWord_5448977 prefixEnd_5448977 2797944276294232586128117 := by
  unfold tailWord_5448977
  simp only [CollatzResearch.WordTrace]
  refine ⟨198740518380294415026969185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132493678920196276684646123 198740518380294415026969185)
  ·
    refine ⟨149055388785220811270226889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198740518380294415026969185 149055388785220811270226889)
    ·
      refine ⟨111791541588915608452670167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149055388785220811270226889 111791541588915608452670167)
      ·
        refine ⟨167687312383373412679005251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111791541588915608452670167 167687312383373412679005251)
        ·
          refine ⟨251530968575060119018507877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167687312383373412679005251 251530968575060119018507877)
          ·
            refine ⟨47162056607823772315970227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251530968575060119018507877 47162056607823772315970227)
            ·
              refine ⟨70743084911735658473955341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47162056607823772315970227 70743084911735658473955341)
              ·
                refine ⟨26528656841900871927733253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70743084911735658473955341 26528656841900871927733253)
                ·
                  refine ⟨4974123157856413486449985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26528656841900871927733253 4974123157856413486449985)
                  ·
                    refine ⟨3730592368392310114837489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4974123157856413486449985 3730592368392310114837489)
                    ·
                      refine ⟨2797944276294232586128117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730592368392310114837489 2797944276294232586128117)
                      ·
                        rfl

theorem cell23_5448977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_5448977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5448977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5448977 prefixEnd_5448977 := by exact prefixLift 5448977
  have htrace : WordTrace (prefixWord ++ tailWord_5448977) baseStart_5448977 baseEnd_5448977 := by
    simpa [prefixWord, tailWord_5448977, baseEnd_5448977] using wordTrace_append hprefix tailTrace_5448977
  have hstable : (prefixWord ++ tailWord_5448977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5448977).length < 2 ^ (prefixWord ++ tailWord_5448977).sum := by decide
  have hdescent : baseEnd_5448977 < baseStart_5448977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5448977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449028 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_5449028 : Nat := 118140960795 + 5449028 * 2 ^ 59
def prefixEnd_5449028 : Nat := 4983230072969 + 3 ^ 40 * 5449028 * 2
def baseEnd_5449028 : Nat := 2797970463807611886590383

theorem tailTrace_5449028 : CollatzResearch.WordTrace tailWord_5449028 prefixEnd_5449028 2797970463807611886590383 := by
  unfold tailWord_5449028
  simp only [CollatzResearch.WordTrace]
  refine ⟨99371189251554825368537869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132494919002073100491383825 99371189251554825368537869)
  ·
    refine ⟨37264195969333059513201701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99371189251554825368537869 37264195969333059513201701)
    ·
      refine ⟨6987036744249948658725319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37264195969333059513201701 6987036744249948658725319)
      ·
        refine ⟨10480555116374922988087979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6987036744249948658725319 10480555116374922988087979)
        ·
          refine ⟨15720832674562384482131969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10480555116374922988087979 15720832674562384482131969)
          ·
            refine ⟨11790624505921788361598977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15720832674562384482131969 11790624505921788361598977)
            ·
              refine ⟨8842968379441341271199233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11790624505921788361598977 8842968379441341271199233)
              ·
                refine ⟨6632226284581005953399425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8842968379441341271199233 6632226284581005953399425)
                ·
                  refine ⟨4974169713435754465049569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6632226284581005953399425 4974169713435754465049569)
                  ·
                    refine ⟨3730627285076815848787177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4974169713435754465049569 3730627285076815848787177)
                    ·
                      refine ⟨2797970463807611886590383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730627285076815848787177 2797970463807611886590383)
                      ·
                        rfl

theorem cell23_5449028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_5449028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449028 prefixEnd_5449028 := by exact prefixLift 5449028
  have htrace : WordTrace (prefixWord ++ tailWord_5449028) baseStart_5449028 baseEnd_5449028 := by
    simpa [prefixWord, tailWord_5449028, baseEnd_5449028] using wordTrace_append hprefix tailTrace_5449028
  have hstable : (prefixWord ++ tailWord_5449028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449028).length < 2 ^ (prefixWord ++ tailWord_5449028).sum := by decide
  have hdescent : baseEnd_5449028 < baseStart_5449028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449050 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_5449050 : Nat := 118140960795 + 5449050 * 2 ^ 59
def prefixEnd_5449050 : Nat := 4983230072969 + 3 ^ 40 * 5449050 * 2
def baseEnd_5449050 : Nat := 2797981760382010800515281

theorem tailTrace_5449050 : CollatzResearch.WordTrace tailWord_5449050 prefixEnd_5449050 2797981760382010800515281 := by
  unfold tailWord_5449050
  simp only [CollatzResearch.WordTrace]
  refine ⟨49685795227257487123594151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132495453939353298996251069 49685795227257487123594151)
  ·
    refine ⟨74528692840886230685391227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49685795227257487123594151 74528692840886230685391227)
    ·
      refine ⟨111793039261329346028086841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74528692840886230685391227 111793039261329346028086841)
      ·
        refine ⟨83844779445997009521065131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111793039261329346028086841 83844779445997009521065131)
        ·
          refine ⟨125767169168995514281597697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83844779445997009521065131 125767169168995514281597697)
          ·
            refine ⟨94325376876746635711198273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125767169168995514281597697 94325376876746635711198273)
            ·
              refine ⟨70744032657559976783398705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94325376876746635711198273 70744032657559976783398705)
              ·
                refine ⟨53058024493169982587549029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70744032657559976783398705 53058024493169982587549029)
                ·
                  refine ⟨9948379592469371735165443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53058024493169982587549029 9948379592469371735165443)
                  ·
                    refine ⟨14922569388704057602748165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9948379592469371735165443 14922569388704057602748165)
                    ·
                      refine ⟨2797981760382010800515281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14922569388704057602748165 2797981760382010800515281)
                      ·
                        rfl

theorem cell23_5449050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_5449050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449050 prefixEnd_5449050 := by exact prefixLift 5449050
  have htrace : WordTrace (prefixWord ++ tailWord_5449050) baseStart_5449050 baseEnd_5449050 := by
    simpa [prefixWord, tailWord_5449050, baseEnd_5449050] using wordTrace_append hprefix tailTrace_5449050
  have hstable : (prefixWord ++ tailWord_5449050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449050).length < 2 ^ (prefixWord ++ tailWord_5449050).sum := by decide
  have hdescent : baseEnd_5449050 < baseStart_5449050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449064 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 2, 5]
def baseStart_5449064 : Nat := 118140960795 + 5449064 * 2 ^ 59
def prefixEnd_5449064 : Nat := 4983230072969 + 3 ^ 40 * 5449064 * 2
def baseEnd_5449064 : Nat := 932662983037057915246739

theorem tailTrace_5449064 : CollatzResearch.WordTrace tailWord_5449064 prefixEnd_5449064 932662983037057915246739 := by
  unfold tailWord_5449064
  simp only [CollatzResearch.WordTrace]
  refine ⟨99371845765489614442693123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132495794353986152590257497 99371845765489614442693123)
  ·
    refine ⟨149057768648234421664039685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99371845765489614442693123 149057768648234421664039685)
    ·
      refine ⟨27948331621543954062007441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149057768648234421664039685 27948331621543954062007441)
      ·
        refine ⟨20961248716157965546505581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27948331621543954062007441 20961248716157965546505581)
        ·
          refine ⟨7860468268559237079939593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20961248716157965546505581 7860468268559237079939593)
          ·
            refine ⟨5895351201419427809954695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7860468268559237079939593 5895351201419427809954695)
            ·
              refine ⟨8843026802129141714932043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895351201419427809954695 8843026802129141714932043)
              ·
                refine ⟨13264540203193712572398065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8843026802129141714932043 13264540203193712572398065)
                ·
                  refine ⟨9948405152395284429298549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13264540203193712572398065 9948405152395284429298549)
                  ·
                    refine ⟨932662983037057915246739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9948405152395284429298549 932662983037057915246739)
                    ·
                      rfl

theorem cell23_5449064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_5449064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449064 prefixEnd_5449064 := by exact prefixLift 5449064
  have htrace : WordTrace (prefixWord ++ tailWord_5449064) baseStart_5449064 baseEnd_5449064 := by
    simpa [prefixWord, tailWord_5449064, baseEnd_5449064] using wordTrace_append hprefix tailTrace_5449064
  have hstable : (prefixWord ++ tailWord_5449064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449064).length < 2 ^ (prefixWord ++ tailWord_5449064).sum := by decide
  have hdescent : baseEnd_5449064 < baseStart_5449064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449137 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 1, 5]
def baseStart_5449137 : Nat := 118140960795 + 5449137 * 2 ^ 59
def prefixEnd_5449137 : Nat := 4983230072969 + 3 ^ 40 * 5449137 * 2
def baseEnd_5449137 : Nat := 932675477732983986709127

theorem tailTrace_5449137 : CollatzResearch.WordTrace tailWord_5449137 prefixEnd_5449137 932675477732983986709127 := by
  unfold tailWord_5449137
  simp only [CollatzResearch.WordTrace]
  refine ⟨198746354059714762352793665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132497569373143174901862443 198746354059714762352793665)
  ·
    refine ⟨149059765544786071764595249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198746354059714762352793665 149059765544786071764595249)
    ·
      refine ⟨111794824158589553823446437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149059765544786071764595249 111794824158589553823446437)
      ·
        refine ⟨20961529529735541341896207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111794824158589553823446437 20961529529735541341896207)
        ·
          refine ⟨31442294294603312012844311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20961529529735541341896207 31442294294603312012844311)
          ·
            refine ⟨47163441441904968019266467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31442294294603312012844311 47163441441904968019266467)
            ·
              refine ⟨70745162162857452028899701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47163441441904968019266467 70745162162857452028899701)
              ·
                refine ⟨6632358952767886127709347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70745162162857452028899701 6632358952767886127709347)
                ·
                  refine ⟨9948538429151829191564021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632358952767886127709347 9948538429151829191564021)
                  ·
                    refine ⟨932675477732983986709127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9948538429151829191564021 932675477732983986709127)
                    ·
                      rfl

theorem cell23_5449137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_5449137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449137 prefixEnd_5449137 := by exact prefixLift 5449137
  have htrace : WordTrace (prefixWord ++ tailWord_5449137) baseStart_5449137 baseEnd_5449137 := by
    simpa [prefixWord, tailWord_5449137, baseEnd_5449137] using wordTrace_append hprefix tailTrace_5449137
  have hstable : (prefixWord ++ tailWord_5449137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449137).length < 2 ^ (prefixWord ++ tailWord_5449137).sum := by decide
  have hdescent : baseEnd_5449137 < baseStart_5449137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449187 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 4]
def baseStart_5449187 : Nat := 118140960795 + 5449187 * 2 ^ 59
def prefixEnd_5449187 : Nat := 4983230072969 + 3 ^ 40 * 5449187 * 2
def baseEnd_5449187 : Nat := 2798052107231676764502151

theorem tailTrace_5449187 : CollatzResearch.WordTrace tailWord_5449187 prefixEnd_5449187 2798052107231676764502151 := by
  unfold tailWord_5449187
  simp only [CollatzResearch.WordTrace]
  refine ⟨198748177709533620892113815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132498785139689080594742543 198748177709533620892113815)
  ·
    refine ⟨298122266564300431338170723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198748177709533620892113815 298122266564300431338170723)
    ·
      refine ⟨447183399846450647007256085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298122266564300431338170723 447183399846450647007256085)
      ·
        refine ⟨20961721867802374078465129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 447183399846450647007256085 20961721867802374078465129)
        ·
          refine ⟨15721291400851780558848847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20961721867802374078465129 15721291400851780558848847)
          ·
            refine ⟨23581937101277670838273271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15721291400851780558848847 23581937101277670838273271)
            ·
              refine ⟨35372905651916506257409907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23581937101277670838273271 35372905651916506257409907)
              ·
                refine ⟨53059358477874759386114861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35372905651916506257409907 53059358477874759386114861)
                ·
                  refine ⟨19897259429203034769793073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53059358477874759386114861 19897259429203034769793073)
                  ·
                    refine ⟨14922944571902276077344805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19897259429203034769793073 14922944571902276077344805)
                    ·
                      refine ⟨2798052107231676764502151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14922944571902276077344805 2798052107231676764502151)
                      ·
                        rfl

theorem cell23_5449187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_5449187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449187 prefixEnd_5449187 := by exact prefixLift 5449187
  have htrace : WordTrace (prefixWord ++ tailWord_5449187) baseStart_5449187 baseEnd_5449187 := by
    simpa [prefixWord, tailWord_5449187, baseEnd_5449187] using wordTrace_append hprefix tailTrace_5449187
  have hstable : (prefixWord ++ tailWord_5449187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449187).length < 2 ^ (prefixWord ++ tailWord_5449187).sum := by decide
  have hdescent : baseEnd_5449187 < baseStart_5449187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449191 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_5449191 : Nat := 118140960795 + 5449191 * 2 ^ 59
def prefixEnd_5449191 : Nat := 4983230072969 + 3 ^ 40 * 5449191 * 2
def baseEnd_5449191 : Nat := 2798054161154294748852133

theorem tailTrace_5449191 : CollatzResearch.WordTrace tailWord_5449191 prefixEnd_5449191 2798054161154294748852133 := by
  unfold tailWord_5449191
  simp only [CollatzResearch.WordTrace]
  refine ⟨198748323601519129575259427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132498882401012753050172951 198748323601519129575259427)
  ·
    refine ⟨298122485402278694362889141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198748323601519129575259427 298122485402278694362889141)
    ·
      refine ⟨27948983006463627596520857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 298122485402278694362889141 27948983006463627596520857)
      ·
        refine ⟨20961737254847720697390643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27948983006463627596520857 20961737254847720697390643)
        ·
          refine ⟨31442605882271581046085965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20961737254847720697390643 31442605882271581046085965)
          ·
            refine ⟨11790977205851842892282237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31442605882271581046085965 11790977205851842892282237)
            ·
              refine ⟨4421616452194441084605839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11790977205851842892282237 4421616452194441084605839)
              ·
                refine ⟨6632424678291661626908759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421616452194441084605839 6632424678291661626908759)
                ·
                  refine ⟨9948637017437492440363139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632424678291661626908759 9948637017437492440363139)
                  ·
                    refine ⟨14922955526156238660544709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9948637017437492440363139 14922955526156238660544709)
                    ·
                      refine ⟨2798054161154294748852133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14922955526156238660544709 2798054161154294748852133)
                      ·
                        rfl

theorem cell23_5449191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_5449191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449191 prefixEnd_5449191 := by exact prefixLift 5449191
  have htrace : WordTrace (prefixWord ++ tailWord_5449191) baseStart_5449191 baseEnd_5449191 := by
    simpa [prefixWord, tailWord_5449191, baseEnd_5449191] using wordTrace_append hprefix tailTrace_5449191
  have hstable : (prefixWord ++ tailWord_5449191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449191).length < 2 ^ (prefixWord ++ tailWord_5449191).sum := by decide
  have hdescent : baseEnd_5449191 < baseStart_5449191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449197 : List Nat := [1, 5, 1, 3, 2, 11]
def baseStart_5449197 : Nat := 118140960795 + 5449197 * 2 ^ 59
def prefixEnd_5449197 : Nat := 4983230072969 + 3 ^ 40 * 5449197 * 2
def baseEnd_5449197 : Nat := 11514638856124369240235

theorem tailTrace_5449197 : CollatzResearch.WordTrace tailWord_5449197 prefixEnd_5449197 11514638856124369240235 := by
  unfold tailWord_5449197
  simp only [CollatzResearch.WordTrace]
  refine ⟨198748542439497392599977845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132499028292998261733318563 198748542439497392599977845)
  ·
    refine ⟨18632675853702880556247923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198748542439497392599977845 18632675853702880556247923)
    ·
      refine ⟨27949013780554320834371885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18632675853702880556247923 27949013780554320834371885)
      ·
        refine ⟨10480880167707870312889457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27949013780554320834371885 10480880167707870312889457)
        ·
          refine ⟨7860660125780902734667093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10480880167707870312889457 7860660125780902734667093)
          ·
            refine ⟨11514638856124369240235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7860660125780902734667093 11514638856124369240235)
            ·
              rfl

theorem cell23_5449197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 11].length) (baseStart_5449197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449197 prefixEnd_5449197 := by exact prefixLift 5449197
  have htrace : WordTrace (prefixWord ++ tailWord_5449197) baseStart_5449197 baseEnd_5449197 := by
    simpa [prefixWord, tailWord_5449197, baseEnd_5449197] using wordTrace_append hprefix tailTrace_5449197
  have hstable : (prefixWord ++ tailWord_5449197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449197).length < 2 ^ (prefixWord ++ tailWord_5449197).sum := by decide
  have hdescent : baseEnd_5449197 < baseStart_5449197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449208 : List Nat := [2, 1, 2, 1, 1, 6, 1, 4, 1, 2, 2]
def baseStart_5449208 : Nat := 118140960795 + 5449208 * 2 ^ 59
def prefixEnd_5449208 : Nat := 4983230072969 + 3 ^ 40 * 5449208 * 2
def baseEnd_5449208 : Nat := 2798062890325421182339555

theorem tailTrace_5449208 : CollatzResearch.WordTrace tailWord_5449208 prefixEnd_5449208 2798062890325421182339555 := by
  unfold tailWord_5449208
  simp only [CollatzResearch.WordTrace]
  refine ⟨99374471821228770739314139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132499295761638360985752185 99374471821228770739314139)
  ·
    refine ⟨149061707731843156108971209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99374471821228770739314139 149061707731843156108971209)
    ·
      refine ⟨111796280798882367081728407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149061707731843156108971209 111796280798882367081728407)
      ·
        refine ⟨167694421198323550622592611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111796280798882367081728407 167694421198323550622592611)
        ·
          refine ⟨251541631797485325933888917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167694421198323550622592611 251541631797485325933888917)
          ·
            refine ⟨11791013990507124653151043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 251541631797485325933888917 11791013990507124653151043)
            ·
              refine ⟨17686520985760686979726565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11791013990507124653151043 17686520985760686979726565)
              ·
                refine ⟨3316222684830128808698731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17686520985760686979726565 3316222684830128808698731)
                ·
                  refine ⟨4974334027245193213048097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316222684830128808698731 4974334027245193213048097)
                  ·
                    refine ⟨3730750520433894909786073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4974334027245193213048097 3730750520433894909786073)
                    ·
                      refine ⟨2798062890325421182339555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730750520433894909786073 2798062890325421182339555)
                      ·
                        rfl

theorem cell23_5449208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 2, 2].length) (baseStart_5449208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449208 prefixEnd_5449208 := by exact prefixLift 5449208
  have htrace : WordTrace (prefixWord ++ tailWord_5449208) baseStart_5449208 baseEnd_5449208 := by
    simpa [prefixWord, tailWord_5449208, baseEnd_5449208] using wordTrace_append hprefix tailTrace_5449208
  have hstable : (prefixWord ++ tailWord_5449208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449208).length < 2 ^ (prefixWord ++ tailWord_5449208).sum := by decide
  have hdescent : baseEnd_5449208 < baseStart_5449208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449210 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_5449210 : Nat := 118140960795 + 5449210 * 2 ^ 59
def prefixEnd_5449210 : Nat := 4983230072969 + 3 ^ 40 * 5449210 * 2
def baseEnd_5449210 : Nat := 932687972428910058171515

theorem tailTrace_5449210 : CollatzResearch.WordTrace tailWord_5449210 prefixEnd_5449210 932687972428910058171515 := by
  unfold tailWord_5449210
  simp only [CollatzResearch.WordTrace]
  refine ⟨49687254147112573955050271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132499344392300197213467389 49687254147112573955050271)
  ·
    refine ⟨74530881220668860932575407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49687254147112573955050271 74530881220668860932575407)
    ·
      refine ⟨111796321831003291398863111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74530881220668860932575407 111796321831003291398863111)
      ·
        refine ⟨167694482746504937098294667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111796321831003291398863111 167694482746504937098294667)
        ·
          refine ⟨251541724119757405647442001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167694482746504937098294667 251541724119757405647442001)
          ·
            refine ⟨188656293089818054235581501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251541724119757405647442001 188656293089818054235581501)
            ·
              refine ⟨70746109908681770338343063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188656293089818054235581501 70746109908681770338343063)
              ·
                refine ⟨106119164863022655507514595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70746109908681770338343063 106119164863022655507514595)
                ·
                  refine ⟨159178747294533983261271893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106119164863022655507514595 159178747294533983261271893)
                  ·
                    refine ⟨932687972428910058171515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 159178747294533983261271893 932687972428910058171515)
                    ·
                      rfl

theorem cell23_5449210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_5449210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449210 prefixEnd_5449210 := by exact prefixLift 5449210
  have htrace : WordTrace (prefixWord ++ tailWord_5449210) baseStart_5449210 baseEnd_5449210 := by
    simpa [prefixWord, tailWord_5449210, baseEnd_5449210] using wordTrace_append hprefix tailTrace_5449210
  have hstable : (prefixWord ++ tailWord_5449210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449210).length < 2 ^ (prefixWord ++ tailWord_5449210).sum := by decide
  have hdescent : baseEnd_5449210 < baseStart_5449210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449324 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 2, 5, 2]
def baseStart_5449324 : Nat := 118140960795 + 5449324 * 2 ^ 59
def prefixEnd_5449324 : Nat := 4983230072969 + 3 ^ 40 * 5449324 * 2
def baseEnd_5449324 : Nat := 2798122454081342728489021

theorem tailTrace_5449324 : CollatzResearch.WordTrace tailWord_5449324 prefixEnd_5449324 2798122454081342728489021 := by
  unfold tailWord_5449324
  simp only [CollatzResearch.WordTrace]
  refine ⟨99376587255018646644925513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132502116340024862193234017 99376587255018646644925513)
  ·
    refine ⟨74532440441263984983694135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99376587255018646644925513 74532440441263984983694135)
    ·
      refine ⟨111798660661895977475541203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74532440441263984983694135 111798660661895977475541203)
      ·
        refine ⟨167697990992843966213311805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111798660661895977475541203 167697990992843966213311805)
        ·
          refine ⟨62886746622316487329991927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167697990992843966213311805 62886746622316487329991927)
          ·
            refine ⟨94330119933474730994987891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62886746622316487329991927 94330119933474730994987891)
            ·
              refine ⟨141495179900212096492481837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94330119933474730994987891 141495179900212096492481837)
              ·
                refine ⟨53060692462579536184680689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141495179900212096492481837 53060692462579536184680689)
                ·
                  refine ⟨39795519346934652138510517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53060692462579536184680689 39795519346934652138510517)
                  ·
                    refine ⟨3730829938775123637985361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39795519346934652138510517 3730829938775123637985361)
                    ·
                      refine ⟨2798122454081342728489021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730829938775123637985361 2798122454081342728489021)
                      ·
                        rfl

theorem cell23_5449324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_5449324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449324 prefixEnd_5449324 := by exact prefixLift 5449324
  have htrace : WordTrace (prefixWord ++ tailWord_5449324) baseStart_5449324 baseEnd_5449324 := by
    simpa [prefixWord, tailWord_5449324, baseEnd_5449324] using wordTrace_append hprefix tailTrace_5449324
  have hstable : (prefixWord ++ tailWord_5449324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449324).length < 2 ^ (prefixWord ++ tailWord_5449324).sum := by decide
  have hdescent : baseEnd_5449324 < baseStart_5449324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449394 : List Nat := [3, 2, 1, 1, 1, 2, 4, 3, 6]
def baseStart_5449394 : Nat := 118140960795 + 5449394 * 2 ^ 59
def prefixEnd_5449394 : Nat := 4983230072969 + 3 ^ 40 * 5449394 * 2
def baseEnd_5449394 : Nat := 310906488636350828290411

theorem tailTrace_5449394 : CollatzResearch.WordTrace tailWord_5449394 prefixEnd_5449394 310906488636350828290411 := by
  unfold tailWord_5449394
  simp only [CollatzResearch.WordTrace]
  refine ⟨49688931904945923811224809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132503818413189130163266157 49688931904945923811224809)
  ·
    refine ⟨37266698928709442858418607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49688931904945923811224809 37266698928709442858418607)
    ·
      refine ⟨55900048393064164287627911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37266698928709442858418607 55900048393064164287627911)
      ·
        refine ⟨83850072589596246431441867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55900048393064164287627911 83850072589596246431441867)
        ·
          refine ⟨125775108884394369647162801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83850072589596246431441867 125775108884394369647162801)
          ·
            refine ⟨94331331663295777235372101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125775108884394369647162801 94331331663295777235372101)
            ·
              refine ⟨17687124686867958231632269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94331331663295777235372101 17687124686867958231632269)
              ·
                refine ⟨6632671757575484336862101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17687124686867958231632269 6632671757575484336862101)
                ·
                  refine ⟨310906488636350828290411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6632671757575484336862101 310906488636350828290411)
                  ·
                    rfl

theorem cell23_5449394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_5449394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449394 prefixEnd_5449394 := by exact prefixLift 5449394
  have htrace : WordTrace (prefixWord ++ tailWord_5449394) baseStart_5449394 baseEnd_5449394 := by
    simpa [prefixWord, tailWord_5449394, baseEnd_5449394] using wordTrace_append hprefix tailTrace_5449394
  have hstable : (prefixWord ++ tailWord_5449394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449394).length < 2 ^ (prefixWord ++ tailWord_5449394).sum := by decide
  have hdescent : baseEnd_5449394 < baseStart_5449394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449398 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_5449398 : Nat := 118140960795 + 5449398 * 2 ^ 59
def prefixEnd_5449398 : Nat := 4983230072969 + 3 ^ 40 * 5449398 * 2
def baseEnd_5449398 : Nat := 932720150549925146321227

theorem tailTrace_5449398 : CollatzResearch.WordTrace tailWord_5449398 prefixEnd_5449398 932720150549925146321227 := by
  unfold tailWord_5449398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12422242094485575245502803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132503915674512802618696565 12422242094485575245502803)
  ·
    refine ⟨18633363141728362868254205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12422242094485575245502803 18633363141728362868254205)
    ·
      refine ⟨6987511178148136075595327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18633363141728362868254205 6987511178148136075595327)
      ·
        refine ⟨10481266767222204113392991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6987511178148136075595327 10481266767222204113392991)
        ·
          refine ⟨15721900150833306170089487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10481266767222204113392991 15721900150833306170089487)
          ·
            refine ⟨23582850226249959255134231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15721900150833306170089487 23582850226249959255134231)
            ·
              refine ⟨35374275339374938882701347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23582850226249959255134231 35374275339374938882701347)
              ·
                refine ⟨53061413009062408324052021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35374275339374938882701347 53061413009062408324052021)
                ·
                  refine ⟨4974507469599600780379877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53061413009062408324052021 4974507469599600780379877)
                  ·
                    refine ⟨932720150549925146321227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4974507469599600780379877 932720150549925146321227)
                    ·
                      rfl

theorem cell23_5449398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_5449398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449398 prefixEnd_5449398 := by exact prefixLift 5449398
  have htrace : WordTrace (prefixWord ++ tailWord_5449398) baseStart_5449398 baseEnd_5449398 := by
    simpa [prefixWord, tailWord_5449398, baseEnd_5449398] using wordTrace_append hprefix tailTrace_5449398
  have hstable : (prefixWord ++ tailWord_5449398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449398).length < 2 ^ (prefixWord ++ tailWord_5449398).sum := by decide
  have hdescent : baseEnd_5449398 < baseStart_5449398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449428 : List Nat := [2, 4, 1, 3, 1, 3, 1, 2, 6]
def baseStart_5449428 : Nat := 118140960795 + 5449428 * 2 ^ 59
def prefixEnd_5449428 : Nat := 4983230072969 + 3 ^ 40 * 5449428 * 2
def baseEnd_5449428 : Nat := 310908428452156702398727

theorem tailTrace_5449428 : CollatzResearch.WordTrace tailWord_5449428 prefixEnd_5449428 310908428452156702398727 := by
  unfold tailWord_5449428
  simp only [CollatzResearch.WordTrace]
  refine ⟨99378483850830259525818469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132504645134440346034424625 99378483850830259525818469)
  ·
    refine ⟨18633465722030673661090963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99378483850830259525818469 18633465722030673661090963)
    ·
      refine ⟨27950198583046010491636445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18633465722030673661090963 27950198583046010491636445)
      ·
        refine ⟨10481324468642253934363667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27950198583046010491636445 10481324468642253934363667)
        ·
          refine ⟨15721986702963380901545501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10481324468642253934363667 15721986702963380901545501)
          ·
            refine ⟨5895745013611267838079563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15721986702963380901545501 5895745013611267838079563)
            ·
              refine ⟨8843617520416901757119345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895745013611267838079563 8843617520416901757119345)
              ·
                refine ⟨6632713140312676317839509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8843617520416901757119345 6632713140312676317839509)
                ·
                  refine ⟨310908428452156702398727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6632713140312676317839509 310908428452156702398727)
                  ·
                    rfl

theorem cell23_5449428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_5449428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449428 prefixEnd_5449428 := by exact prefixLift 5449428
  have htrace : WordTrace (prefixWord ++ tailWord_5449428) baseStart_5449428 baseEnd_5449428 := by
    simpa [prefixWord, tailWord_5449428, baseEnd_5449428] using wordTrace_append hprefix tailTrace_5449428
  have hstable : (prefixWord ++ tailWord_5449428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449428).length < 2 ^ (prefixWord ++ tailWord_5449428).sum := by decide
  have hdescent : baseEnd_5449428 < baseStart_5449428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449431 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 4, 3, 2]
def baseStart_5449431 : Nat := 118140960795 + 5449431 * 2 ^ 59
def prefixEnd_5449431 : Nat := 4983230072969 + 3 ^ 40 * 5449431 * 2
def baseEnd_5449431 : Nat := 2798177396511373809851029

theorem tailTrace_5449431 : CollatzResearch.WordTrace tailWord_5449431 prefixEnd_5449431 2798177396511373809851029 := by
  unfold tailWord_5449431
  simp only [CollatzResearch.WordTrace]
  refine ⟨198757077120649650563996147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132504718080433100375997431 198757077120649650563996147)
  ·
    refine ⟨298135615680974475845994221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198757077120649650563996147 298135615680974475845994221)
    ·
      refine ⟨111800855880365428442247833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298135615680974475845994221 111800855880365428442247833)
      ·
        refine ⟨83850641910274071331685875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111800855880365428442247833 83850641910274071331685875)
        ·
          refine ⟨125775962865411106997528813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83850641910274071331685875 125775962865411106997528813)
          ·
            refine ⟨47165986074529165124073305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125775962865411106997528813 47165986074529165124073305)
            ·
              refine ⟨35374489555896873843054979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47165986074529165124073305 35374489555896873843054979)
              ·
                refine ⟨53061734333845310764582469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35374489555896873843054979 53061734333845310764582469)
                ·
                  refine ⟨9949075187595995768359213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53061734333845310764582469 9949075187595995768359213)
                  ·
                    refine ⟨3730903195348498413134705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9949075187595995768359213 3730903195348498413134705)
                    ·
                      refine ⟨2798177396511373809851029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730903195348498413134705 2798177396511373809851029)
                      ·
                        rfl

theorem cell23_5449431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_5449431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449431 prefixEnd_5449431 := by exact prefixLift 5449431
  have htrace : WordTrace (prefixWord ++ tailWord_5449431) baseStart_5449431 baseEnd_5449431 := by
    simpa [prefixWord, tailWord_5449431, baseEnd_5449431] using wordTrace_append hprefix tailTrace_5449431
  have hstable : (prefixWord ++ tailWord_5449431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449431).length < 2 ^ (prefixWord ++ tailWord_5449431).sum := by decide
  have hdescent : baseEnd_5449431 < baseStart_5449431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449495 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 3, 2, 2]
def baseStart_5449495 : Nat := 118140960795 + 5449495 * 2 ^ 59
def prefixEnd_5449495 : Nat := 4983230072969 + 3 ^ 40 * 5449495 * 2
def baseEnd_5449495 : Nat := 2798210259273261559450735

theorem tailTrace_5449495 : CollatzResearch.WordTrace tailWord_5449495 prefixEnd_5449495 2798210259273261559450735 := by
  unfold tailWord_5449495
  simp only [CollatzResearch.WordTrace]
  refine ⟨198759411392417789494325939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132506274261611859662883959 198759411392417789494325939)
  ·
    refine ⟨298139117088626684241488909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198759411392417789494325939 298139117088626684241488909)
    ·
      refine ⟨111802168908235006590558341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298139117088626684241488909 111802168908235006590558341)
      ·
        refine ⟨20962906670294063735729689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111802168908235006590558341 20962906670294063735729689)
        ·
          refine ⟨15722180002720547801797267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20962906670294063735729689 15722180002720547801797267)
          ·
            refine ⟨23583270004080821702695901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15722180002720547801797267 23583270004080821702695901)
            ·
              refine ⟨8843726251530308138510963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23583270004080821702695901 8843726251530308138510963)
              ·
                refine ⟨13265589377295462207766445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8843726251530308138510963 13265589377295462207766445)
                ·
                  refine ⟨4974596016485798327912417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13265589377295462207766445 4974596016485798327912417)
                  ·
                    refine ⟨3730947012364348745934313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4974596016485798327912417 3730947012364348745934313)
                    ·
                      refine ⟨2798210259273261559450735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730947012364348745934313 2798210259273261559450735)
                      ·
                        rfl

theorem cell23_5449495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_5449495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449495 prefixEnd_5449495 := by exact prefixLift 5449495
  have htrace : WordTrace (prefixWord ++ tailWord_5449495) baseStart_5449495 baseEnd_5449495 := by
    simpa [prefixWord, tailWord_5449495, baseEnd_5449495] using wordTrace_append hprefix tailTrace_5449495
  have hstable : (prefixWord ++ tailWord_5449495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449495).length < 2 ^ (prefixWord ++ tailWord_5449495).sum := by decide
  have hdescent : baseEnd_5449495 < baseStart_5449495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449504 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5449504 : Nat := 118140960795 + 5449504 * 2 ^ 59
def prefixEnd_5449504 : Nat := 4983230072969 + 3 ^ 40 * 5449504 * 2
def baseEnd_5449504 : Nat := 2798214880599152024238193

theorem tailTrace_5449504 : CollatzResearch.WordTrace tailWord_5449504 prefixEnd_5449504 2798214880599152024238193 := by
  unfold tailWord_5449504
  simp only [CollatzResearch.WordTrace]
  refine ⟨99379869824692592015701783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132506493099590122687602377 99379869824692592015701783)
  ·
    refine ⟨149069804737038888023552675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99379869824692592015701783 149069804737038888023552675)
    ·
      refine ⟨223604707105558332035329013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149069804737038888023552675 223604707105558332035329013)
      ·
        refine ⟨20962941291146093628312095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223604707105558332035329013 20962941291146093628312095)
        ·
          refine ⟨31444411936719140442468143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20962941291146093628312095 31444411936719140442468143)
          ·
            refine ⟨47166617905078710663702215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31444411936719140442468143 47166617905078710663702215)
            ·
              refine ⟨70749926857618065995553323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47166617905078710663702215 70749926857618065995553323)
              ·
                refine ⟨106124890286427098993329985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70749926857618065995553323 106124890286427098993329985)
                ·
                  refine ⟨79593667714820324244997489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106124890286427098993329985 79593667714820324244997489)
                  ·
                    refine ⟨59695250786115243183748117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79593667714820324244997489 59695250786115243183748117)
                    ·
                      refine ⟨2798214880599152024238193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59695250786115243183748117 2798214880599152024238193)
                      ·
                        rfl

theorem cell23_5449504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5449504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449504 prefixEnd_5449504 := by exact prefixLift 5449504
  have htrace : WordTrace (prefixWord ++ tailWord_5449504) baseStart_5449504 baseEnd_5449504 := by
    simpa [prefixWord, tailWord_5449504, baseEnd_5449504] using wordTrace_append hprefix tailTrace_5449504
  have hstable : (prefixWord ++ tailWord_5449504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449504).length < 2 ^ (prefixWord ++ tailWord_5449504).sum := by decide
  have hdescent : baseEnd_5449504 < baseStart_5449504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449505 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 2, 4]
def baseStart_5449505 : Nat := 118140960795 + 5449505 * 2 ^ 59
def prefixEnd_5449505 : Nat := 4983230072969 + 3 ^ 40 * 5449505 * 2
def baseEnd_5449505 : Nat := 932738464693268840108563

theorem tailTrace_5449505 : CollatzResearch.WordTrace tailWord_5449505 prefixEnd_5449505 932738464693268840108563 := by
  unfold tailWord_5449505
  simp only [CollatzResearch.WordTrace]
  refine ⟨198759776122381561202189969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132506517414921040801459979 198759776122381561202189969)
  ·
    refine ⟨149069832091786170901642477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198759776122381561202189969 149069832091786170901642477)
    ·
      refine ⟨55901187034419814088115929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149069832091786170901642477 55901187034419814088115929)
      ·
        refine ⟨41925890275814860566086947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55901187034419814088115929 41925890275814860566086947)
        ·
          refine ⟨62888835413722290849130421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41925890275814860566086947 62888835413722290849130421)
          ·
            refine ⟨5895828320036464767105977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62888835413722290849130421 5895828320036464767105977)
            ·
              refine ⟨4421871240027348575329483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5895828320036464767105977 4421871240027348575329483)
              ·
                refine ⟨6632806860041022862994225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421871240027348575329483 6632806860041022862994225)
                ·
                  refine ⟨4974605145030767147245669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6632806860041022862994225 4974605145030767147245669)
                  ·
                    refine ⟨932738464693268840108563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4974605145030767147245669 932738464693268840108563)
                    ·
                      rfl

theorem cell23_5449505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_5449505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449505 prefixEnd_5449505 := by exact prefixLift 5449505
  have htrace : WordTrace (prefixWord ++ tailWord_5449505) baseStart_5449505 baseEnd_5449505 := by
    simpa [prefixWord, tailWord_5449505, baseEnd_5449505] using wordTrace_append hprefix tailTrace_5449505
  have hstable : (prefixWord ++ tailWord_5449505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449505).length < 2 ^ (prefixWord ++ tailWord_5449505).sum := by decide
  have hdescent : baseEnd_5449505 < baseStart_5449505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449568 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 1, 4, 2]
def baseStart_5449568 : Nat := 118140960795 + 5449568 * 2 ^ 59
def prefixEnd_5449568 : Nat := 4983230072969 + 3 ^ 40 * 5449568 * 2
def baseEnd_5449568 : Nat := 2798247743361039773837899

theorem tailTrace_5449568 : CollatzResearch.WordTrace tailWord_5449568 prefixEnd_5449568 2798247743361039773837899 := by
  unfold tailWord_5449568
  simp only [CollatzResearch.WordTrace]
  refine ⟨99381036960576661480866679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132508049280768881974488905 99381036960576661480866679)
  ·
    refine ⟨149071555440864992221300019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99381036960576661480866679 149071555440864992221300019)
    ·
      refine ⟨223607333161297488331950029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149071555440864992221300019 223607333161297488331950029)
      ·
        refine ⟨83852749935486558124481261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223607333161297488331950029 83852749935486558124481261)
        ·
          refine ⟨31444781225807459296680473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83852749935486558124481261 31444781225807459296680473)
          ·
            refine ⟨23583585919355594472510355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31444781225807459296680473 23583585919355594472510355)
            ·
              refine ⟨35375378879033391708765533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23583585919355594472510355 35375378879033391708765533)
              ·
                refine ⟨13265767079637521890787075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35375378879033391708765533 13265767079637521890787075)
                ·
                  refine ⟨19898650619456282836180613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13265767079637521890787075 19898650619456282836180613)
                  ·
                    refine ⟨3730996991148053031783865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19898650619456282836180613 3730996991148053031783865)
                    ·
                      refine ⟨2798247743361039773837899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3730996991148053031783865 2798247743361039773837899)
                      ·
                        rfl

theorem cell23_5449568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_5449568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449568 prefixEnd_5449568 := by exact prefixLift 5449568
  have htrace : WordTrace (prefixWord ++ tailWord_5449568) baseStart_5449568 baseEnd_5449568 := by
    simpa [prefixWord, tailWord_5449568, baseEnd_5449568] using wordTrace_append hprefix tailTrace_5449568
  have hstable : (prefixWord ++ tailWord_5449568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449568).length < 2 ^ (prefixWord ++ tailWord_5449568).sum := by decide
  have hdescent : baseEnd_5449568 < baseStart_5449568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449584 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_5449584 : Nat := 118140960795 + 5449584 * 2 ^ 59
def prefixEnd_5449584 : Nat := 4983230072969 + 3 ^ 40 * 5449584 * 2
def baseEnd_5449584 : Nat := 2798255959051511711237825

theorem tailTrace_5449584 : CollatzResearch.WordTrace tailWord_5449584 prefixEnd_5449584 2798255959051511711237825 := by
  unfold tailWord_5449584
  simp only [CollatzResearch.WordTrace]
  refine ⟨99381328744547678847157903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132508438326063571796210537 99381328744547678847157903)
  ·
    refine ⟨149071993116821518270736855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99381328744547678847157903 149071993116821518270736855)
    ·
      refine ⟨223607989675232277406105283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149071993116821518270736855 223607989675232277406105283)
      ·
        refine ⟨335411984512848416109157925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223607989675232277406105283 335411984512848416109157925)
        ·
          refine ⟨62889747096159078020467111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335411984512848416109157925 62889747096159078020467111)
          ·
            refine ⟨94334620644238617030700667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62889747096159078020467111 94334620644238617030700667)
            ·
              refine ⟨141501930966357925546051001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94334620644238617030700667 141501930966357925546051001)
              ·
                refine ⟨106126448224768444159538251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141501930966357925546051001 106126448224768444159538251)
                ·
                  refine ⟨159189672337152666239307377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106126448224768444159538251 159189672337152666239307377)
                  ·
                    refine ⟨119392254252864499679480533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159189672337152666239307377 119392254252864499679480533)
                    ·
                      refine ⟨2798255959051511711237825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119392254252864499679480533 2798255959051511711237825)
                      ·
                        rfl

theorem cell23_5449584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_5449584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449584 prefixEnd_5449584 := by exact prefixLift 5449584
  have htrace : WordTrace (prefixWord ++ tailWord_5449584) baseStart_5449584 baseEnd_5449584 := by
    simpa [prefixWord, tailWord_5449584, baseEnd_5449584] using wordTrace_append hprefix tailTrace_5449584
  have hstable : (prefixWord ++ tailWord_5449584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449584).length < 2 ^ (prefixWord ++ tailWord_5449584).sum := by decide
  have hdescent : baseEnd_5449584 < baseStart_5449584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449608 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 7]
def baseStart_5449608 : Nat := 118140960795 + 5449608 * 2 ^ 59
def prefixEnd_5449608 : Nat := 4983230072969 + 3 ^ 40 * 5449608 * 2
def baseEnd_5449608 : Nat := 310918698065246624148635

theorem tailTrace_5449608 : CollatzResearch.WordTrace tailWord_5449608 prefixEnd_5449608 310918698065246624148635 := by
  unfold tailWord_5449608
  simp only [CollatzResearch.WordTrace]
  refine ⟨99381766420504204896594739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132509021894005606528792985 99381766420504204896594739)
  ·
    refine ⟨149072649630756307344892109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99381766420504204896594739 149072649630756307344892109)
    ·
      refine ⟨55902243611533615254334541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149072649630756307344892109 55902243611533615254334541)
      ·
        refine ⟨20963341354325105720375453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55902243611533615254334541 20963341354325105720375453)
        ·
          refine ⟨7861253007871914645140795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20963341354325105720375453 7861253007871914645140795)
          ·
            refine ⟨11791879511807871967711193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7861253007871914645140795 11791879511807871967711193)
            ·
              refine ⟨8843909633855903975783395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11791879511807871967711193 8843909633855903975783395)
              ·
                refine ⟨13265864450783855963675093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8843909633855903975783395 13265864450783855963675093)
                ·
                  refine ⟨310918698065246624148635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13265864450783855963675093 310918698065246624148635)
                  ·
                    rfl

theorem cell23_5449608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 7].length) (baseStart_5449608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449608 prefixEnd_5449608 := by exact prefixLift 5449608
  have htrace : WordTrace (prefixWord ++ tailWord_5449608) baseStart_5449608 baseEnd_5449608 := by
    simpa [prefixWord, tailWord_5449608, baseEnd_5449608] using wordTrace_append hprefix tailTrace_5449608
  have hstable : (prefixWord ++ tailWord_5449608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449608).length < 2 ^ (prefixWord ++ tailWord_5449608).sum := by decide
  have hdescent : baseEnd_5449608 < baseStart_5449608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449658 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2]
def baseStart_5449658 : Nat := 118140960795 + 5449658 * 2 ^ 59
def prefixEnd_5449658 : Nat := 4983230072969 + 3 ^ 40 * 5449658 * 2
def baseEnd_5449658 : Nat := 2798293956619944421712485

theorem tailTrace_5449658 : CollatzResearch.WordTrace tailWord_5449658 prefixEnd_5449658 2798293956619944421712485 := by
  unfold tailWord_5449658
  simp only [CollatzResearch.WordTrace]
  refine ⟨49691339122706817083127407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132510237660551512221673085 49691339122706817083127407)
  ·
    refine ⟨74537008684060225624691111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49691339122706817083127407 74537008684060225624691111)
    ·
      refine ⟨111805513026090338437036667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74537008684060225624691111 111805513026090338437036667)
      ·
        refine ⟨167708269539135507655555001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111805513026090338437036667 167708269539135507655555001)
        ·
          refine ⟨125781202154351630741666251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167708269539135507655555001 125781202154351630741666251)
          ·
            refine ⟨188671803231527446112499377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125781202154351630741666251 188671803231527446112499377)
            ·
              refine ⟨141503852423645584584374533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188671803231527446112499377 141503852423645584584374533)
              ·
                refine ⟨26531972329433547109570225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141503852423645584584374533 26531972329433547109570225)
                ·
                  refine ⟨19898979247075160332177669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26531972329433547109570225 19898979247075160332177669)
                  ·
                    refine ⟨3731058608826592562283313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19898979247075160332177669 3731058608826592562283313)
                    ·
                      refine ⟨2798293956619944421712485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3731058608826592562283313 2798293956619944421712485)
                      ·
                        rfl

theorem cell23_5449658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_5449658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449658 prefixEnd_5449658 := by exact prefixLift 5449658
  have htrace : WordTrace (prefixWord ++ tailWord_5449658) baseStart_5449658 baseEnd_5449658 := by
    simpa [prefixWord, tailWord_5449658, baseEnd_5449658] using wordTrace_append hprefix tailTrace_5449658
  have hstable : (prefixWord ++ tailWord_5449658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449658).length < 2 ^ (prefixWord ++ tailWord_5449658).sum := by decide
  have hdescent : baseEnd_5449658 < baseStart_5449658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449678 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3]
def baseStart_5449678 : Nat := 118140960795 + 5449678 * 2 ^ 59
def prefixEnd_5449678 : Nat := 4983230072969 + 3 ^ 40 * 5449678 * 2
def baseEnd_5449678 : Nat := 2798304226233034343462393

theorem tailTrace_5449678 : CollatzResearch.WordTrace tailWord_5449678 prefixEnd_5449678 2798304226233034343462393 := by
  unfold tailWord_5449678
  simp only [CollatzResearch.WordTrace]
  refine ⟨24845760743844351468529711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132510723967169874498825125 24845760743844351468529711)
  ·
    refine ⟨37268641115766527202794567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24845760743844351468529711 37268641115766527202794567)
    ·
      refine ⟨55902961673649790804191851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37268641115766527202794567 55902961673649790804191851)
      ·
        refine ⟨83854442510474686206287777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55902961673649790804191851 83854442510474686206287777)
        ·
          refine ⟨62890831882856014654715833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83854442510474686206287777 62890831882856014654715833)
          ·
            refine ⟨47168123912142010991036875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62890831882856014654715833 47168123912142010991036875)
            ·
              refine ⟨70752185868213016486555313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47168123912142010991036875 70752185868213016486555313)
              ·
                refine ⟨53064139401159762364916485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70752185868213016486555313 53064139401159762364916485)
                ·
                  refine ⟨9949526137717455443421841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53064139401159762364916485 9949526137717455443421841)
                  ·
                    refine ⟨7462144603288091582566381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9949526137717455443421841 7462144603288091582566381)
                    ·
                      refine ⟨2798304226233034343462393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7462144603288091582566381 2798304226233034343462393)
                      ·
                        rfl

theorem cell23_5449678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_5449678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449678 prefixEnd_5449678 := by exact prefixLift 5449678
  have htrace : WordTrace (prefixWord ++ tailWord_5449678) baseStart_5449678 baseEnd_5449678 := by
    simpa [prefixWord, tailWord_5449678, baseEnd_5449678] using wordTrace_append hprefix tailTrace_5449678
  have hstable : (prefixWord ++ tailWord_5449678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449678).length < 2 ^ (prefixWord ++ tailWord_5449678).sum := by decide
  have hdescent : baseEnd_5449678 < baseStart_5449678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449695 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 3]
def baseStart_5449695 : Nat := 118140960795 + 5449695 * 2 ^ 59
def prefixEnd_5449695 : Nat := 4983230072969 + 3 ^ 40 * 5449695 * 2
def baseEnd_5449695 : Nat := 2798312955404160776949815

theorem tailTrace_5449695 : CollatzResearch.WordTrace tailWord_5449695 prefixEnd_5449695 2798312955404160776949815 := by
  unfold tailWord_5449695
  simp only [CollatzResearch.WordTrace]
  refine ⟨198766705991693223651606539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132511137327795482434404359 198766705991693223651606539)
  ·
    refine ⟨298150058987539835477409809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198766705991693223651606539 298150058987539835477409809)
    ·
      refine ⟨223612544240654876608057357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298150058987539835477409809 223612544240654876608057357)
      ·
        refine ⟨83854704090245578728021509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223612544240654876608057357 83854704090245578728021509)
        ·
          refine ⟨15722757016921046011504033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83854704090245578728021509 15722757016921046011504033)
          ·
            refine ⟨11792067762690784508628025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15722757016921046011504033 11792067762690784508628025)
            ·
              refine ⟨8844050822018088381471019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11792067762690784508628025 8844050822018088381471019)
              ·
                refine ⟨13266076233027132572206529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8844050822018088381471019 13266076233027132572206529)
                ·
                  refine ⟨9949557174770349429154897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13266076233027132572206529 9949557174770349429154897)
                  ·
                    refine ⟨7462167881077762071866173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9949557174770349429154897 7462167881077762071866173)
                    ·
                      refine ⟨2798312955404160776949815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7462167881077762071866173 2798312955404160776949815)
                      ·
                        rfl

theorem cell23_5449695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_5449695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449695 prefixEnd_5449695 := by exact prefixLift 5449695
  have htrace : WordTrace (prefixWord ++ tailWord_5449695) baseStart_5449695 baseEnd_5449695 := by
    simpa [prefixWord, tailWord_5449695, baseEnd_5449695] using wordTrace_append hprefix tailTrace_5449695
  have hstable : (prefixWord ++ tailWord_5449695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449695).length < 2 ^ (prefixWord ++ tailWord_5449695).sum := by decide
  have hdescent : baseEnd_5449695 < baseStart_5449695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449765 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 4]
def baseStart_5449765 : Nat := 118140960795 + 5449765 * 2 ^ 59
def prefixEnd_5449765 : Nat := 4983230072969 + 3 ^ 40 * 5449765 * 2
def baseEnd_5449765 : Nat := 2798348899049975503074493

theorem tailTrace_5449765 : CollatzResearch.WordTrace tailWord_5449765 prefixEnd_5449765 2798348899049975503074493 := by
  unfold tailWord_5449765
  simp only [CollatzResearch.WordTrace]
  refine ⟨198769259101439625606654749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132512839400959750404436499 198769259101439625606654749)
  ·
    refine ⟨74538472163039859602495531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198769259101439625606654749 74538472163039859602495531)
    ·
      refine ⟨111807708244559789403743297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74538472163039859602495531 111807708244559789403743297)
      ·
        refine ⟨83855781183419842052807473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111807708244559789403743297 83855781183419842052807473)
        ·
          refine ⟨62891835887564881539605605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83855781183419842052807473 62891835887564881539605605)
          ·
            refine ⟨11792219228918415288676051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62891835887564881539605605 11792219228918415288676051)
            ·
              refine ⟨17688328843377622933014077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11792219228918415288676051 17688328843377622933014077)
              ·
                refine ⟨6633123316266608599880279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17688328843377622933014077 6633123316266608599880279)
                ·
                  refine ⟨9949684974399912899820419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6633123316266608599880279 9949684974399912899820419)
                  ·
                    refine ⟨14924527461599869349730629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9949684974399912899820419 14924527461599869349730629)
                    ·
                      refine ⟨2798348899049975503074493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14924527461599869349730629 2798348899049975503074493)
                      ·
                        rfl

theorem cell23_5449765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_5449765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449765 prefixEnd_5449765 := by exact prefixLift 5449765
  have htrace : WordTrace (prefixWord ++ tailWord_5449765) baseStart_5449765 baseEnd_5449765 := by
    simpa [prefixWord, tailWord_5449765, baseEnd_5449765] using wordTrace_append hprefix tailTrace_5449765
  have hstable : (prefixWord ++ tailWord_5449765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449765).length < 2 ^ (prefixWord ++ tailWord_5449765).sum := by decide
  have hdescent : baseEnd_5449765 < baseStart_5449765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449785 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 5]
def baseStart_5449785 : Nat := 118140960795 + 5449785 * 2 ^ 59
def prefixEnd_5449785 : Nat := 4983230072969 + 3 ^ 40 * 5449785 * 2
def baseEnd_5449785 : Nat := 2798359168663065424824401

theorem tailTrace_5449785 : CollatzResearch.WordTrace tailWord_5449785 prefixEnd_5449785 2798359168663065424824401 := by
  unfold tailWord_5449785
  simp only [CollatzResearch.WordTrace]
  refine ⟨198769988561367169022382809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132513325707578112681588539 198769988561367169022382809)
  ·
    refine ⟨149077491421025376766787107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198769988561367169022382809 149077491421025376766787107)
    ·
      refine ⟨223616237131538065150180661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149077491421025376766787107 223616237131538065150180661)
      ·
        refine ⟨20964022231081693607829437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223616237131538065150180661 20964022231081693607829437)
        ·
          refine ⟨7861508336655635102936039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20964022231081693607829437 7861508336655635102936039)
          ·
            refine ⟨11792262504983452654404059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7861508336655635102936039 11792262504983452654404059)
            ·
              refine ⟨17688393757475178981606089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11792262504983452654404059 17688393757475178981606089)
              ·
                refine ⟨13266295318106384236204567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17688393757475178981606089 13266295318106384236204567)
                ·
                  refine ⟨19899442977159576354306851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13266295318106384236204567 19899442977159576354306851)
                  ·
                    refine ⟨29849164465739364531460277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19899442977159576354306851 29849164465739364531460277)
                    ·
                      refine ⟨2798359168663065424824401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29849164465739364531460277 2798359168663065424824401)
                      ·
                        rfl

theorem cell23_5449785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_5449785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449785 prefixEnd_5449785 := by exact prefixLift 5449785
  have htrace : WordTrace (prefixWord ++ tailWord_5449785) baseStart_5449785 baseEnd_5449785 := by
    simpa [prefixWord, tailWord_5449785, baseEnd_5449785] using wordTrace_append hprefix tailTrace_5449785
  have hstable : (prefixWord ++ tailWord_5449785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449785).length < 2 ^ (prefixWord ++ tailWord_5449785).sum := by decide
  have hdescent : baseEnd_5449785 < baseStart_5449785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449792 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 2, 4]
def baseStart_5449792 : Nat := 118140960795 + 5449792 * 2 ^ 59
def prefixEnd_5449792 : Nat := 4983230072969 + 3 ^ 40 * 5449792 * 2
def baseEnd_5449792 : Nat := 932787587675882299145623

theorem tailTrace_5449792 : CollatzResearch.WordTrace tailWord_5449792 prefixEnd_5449792 932787587675882299145623 := by
  unfold tailWord_5449792
  simp only [CollatzResearch.WordTrace]
  refine ⟨99385121936170904608943815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132513495914894539478591753 99385121936170904608943815)
  ·
    refine ⟨149077682904256356913415723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99385121936170904608943815 149077682904256356913415723)
    ·
      refine ⟨223616524356384535370123585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149077682904256356913415723 223616524356384535370123585)
      ·
        refine ⟨167712393267288401527592689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223616524356384535370123585 167712393267288401527592689)
        ·
          refine ⟨125784294950466301145694517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167712393267288401527592689 125784294950466301145694517)
          ·
            refine ⟨11792277651606215732408861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125784294950466301145694517 11792277651606215732408861)
            ·
              refine ⟨4422104119352330899653323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11792277651606215732408861 4422104119352330899653323)
              ·
                refine ⟨6633156179028496349479985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4422104119352330899653323 6633156179028496349479985)
                ·
                  refine ⟨4974867134271372262109989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6633156179028496349479985 4974867134271372262109989)
                  ·
                    refine ⟨932787587675882299145623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4974867134271372262109989 932787587675882299145623)
                    ·
                      rfl

theorem cell23_5449792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 4].length) (baseStart_5449792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449792 prefixEnd_5449792 := by exact prefixLift 5449792
  have htrace : WordTrace (prefixWord ++ tailWord_5449792) baseStart_5449792 baseEnd_5449792 := by
    simpa [prefixWord, tailWord_5449792, baseEnd_5449792] using wordTrace_append hprefix tailTrace_5449792
  have hstable : (prefixWord ++ tailWord_5449792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449792).length < 2 ^ (prefixWord ++ tailWord_5449792).sum := by decide
  have hdescent : baseEnd_5449792 < baseStart_5449792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449811 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 7]
def baseStart_5449811 : Nat := 118140960795 + 5449811 * 2 ^ 59
def prefixEnd_5449811 : Nat := 4983230072969 + 3 ^ 40 * 5449811 * 2
def baseEnd_5449811 : Nat := 2798372519160082323099281

theorem tailTrace_5449811 : CollatzResearch.WordTrace tailWord_5449811 prefixEnd_5449811 2798372519160082323099281 := by
  unfold tailWord_5449811
  simp only [CollatzResearch.WordTrace]
  refine ⟨198770936859272975462829287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132513957906181983641886191 198770936859272975462829287)
  ·
    refine ⟨298156405288909463194243931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198770936859272975462829287 298156405288909463194243931)
    ·
      refine ⟨447234607933364194791365897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298156405288909463194243931 447234607933364194791365897)
      ·
        refine ⟨335425955950023146093524423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447234607933364194791365897 335425955950023146093524423)
        ·
          refine ⟨503138933925034719140286635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335425955950023146093524423 503138933925034719140286635)
          ·
            refine ⟨754708400887552078710429953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503138933925034719140286635 754708400887552078710429953)
            ·
              refine ⟨566031300665664059032822465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754708400887552078710429953 566031300665664059032822465)
              ·
                refine ⟨424523475499248044274616849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566031300665664059032822465 424523475499248044274616849)
                ·
                  refine ⟨318392606624436033205962637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424523475499248044274616849 318392606624436033205962637)
                  ·
                    refine ⟨119397227484163512452235989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 318392606624436033205962637 119397227484163512452235989)
                    ·
                      refine ⟨2798372519160082323099281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119397227484163512452235989 2798372519160082323099281)
                      ·
                        rfl

theorem cell23_5449811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_5449811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449811 prefixEnd_5449811 := by exact prefixLift 5449811
  have htrace : WordTrace (prefixWord ++ tailWord_5449811) baseStart_5449811 baseEnd_5449811 := by
    simpa [prefixWord, tailWord_5449811, baseEnd_5449811] using wordTrace_append hprefix tailTrace_5449811
  have hstable : (prefixWord ++ tailWord_5449811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449811).length < 2 ^ (prefixWord ++ tailWord_5449811).sum := by decide
  have hdescent : baseEnd_5449811 < baseStart_5449811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449815 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 3]
def baseStart_5449815 : Nat := 118140960795 + 5449815 * 2 ^ 59
def prefixEnd_5449815 : Nat := 4983230072969 + 3 ^ 40 * 5449815 * 2
def baseEnd_5449815 : Nat := 2798374573082700307449263

theorem tailTrace_5449815 : CollatzResearch.WordTrace tailWord_5449815 prefixEnd_5449815 2798374573082700307449263 := by
  unfold tailWord_5449815
  simp only [CollatzResearch.WordTrace]
  refine ⟨198771082751258484145974899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132514055167505656097316599 198771082751258484145974899)
  ·
    refine ⟨298156624126887726218962349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198771082751258484145974899 298156624126887726218962349)
    ·
      refine ⟨111808734047582897332110881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298156624126887726218962349 111808734047582897332110881)
      ·
        refine ⟨83856550535687172999083161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111808734047582897332110881 83856550535687172999083161)
        ·
          refine ⟨62892412901765379749312371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83856550535687172999083161 62892412901765379749312371)
          ·
            refine ⟨94338619352648069623968557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62892412901765379749312371 94338619352648069623968557)
            ·
              refine ⟨35376982257243026108988209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94338619352648069623968557 35376982257243026108988209)
              ·
                refine ⟨26532736692932269581741157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35376982257243026108988209 26532736692932269581741157)
                ·
                  refine ⟨4974888129924800546576467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26532736692932269581741157 4974888129924800546576467)
                  ·
                    refine ⟨7462332194887200819864701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4974888129924800546576467 7462332194887200819864701)
                    ·
                      refine ⟨2798374573082700307449263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7462332194887200819864701 2798374573082700307449263)
                      ·
                        rfl

theorem cell23_5449815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_5449815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449815 prefixEnd_5449815 := by exact prefixLift 5449815
  have htrace : WordTrace (prefixWord ++ tailWord_5449815) baseStart_5449815 baseEnd_5449815 := by
    simpa [prefixWord, tailWord_5449815, baseEnd_5449815] using wordTrace_append hprefix tailTrace_5449815
  have hstable : (prefixWord ++ tailWord_5449815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449815).length < 2 ^ (prefixWord ++ tailWord_5449815).sum := by decide
  have hdescent : baseEnd_5449815 < baseStart_5449815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449816 : List Nat := [2, 1, 2, 2, 1, 6, 1, 3, 1, 2, 2]
def baseStart_5449816 : Nat := 118140960795 + 5449816 * 2 ^ 59
def prefixEnd_5449816 : Nat := 4983230072969 + 3 ^ 40 * 5449816 * 2
def baseEnd_5449816 : Nat := 2798375086563354803536759

theorem tailTrace_5449816 : CollatzResearch.WordTrace tailWord_5449816 prefixEnd_5449816 2798375086563354803536759 := by
  unfold tailWord_5449816
  simp only [CollatzResearch.WordTrace]
  refine ⟨99385559612127430658380651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132514079482836574211174201 99385559612127430658380651)
  ·
    refine ⟨149078339418191145987570977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99385559612127430658380651 149078339418191145987570977)
    ·
      refine ⟨111808754563643359490678233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149078339418191145987570977 111808754563643359490678233)
      ·
        refine ⟨83856565922732519618008675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111808754563643359490678233 83856565922732519618008675)
        ·
          refine ⟨125784848884098779427013013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83856565922732519618008675 125784848884098779427013013)
          ·
            refine ⟨5896164791442130285641235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125784848884098779427013013 5896164791442130285641235)
            ·
              refine ⟨8844247187163195428461853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5896164791442130285641235 8844247187163195428461853)
              ·
                refine ⟨3316592695186198285673195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8844247187163195428461853 3316592695186198285673195)
                ·
                  refine ⟨4974889042779297428509793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316592695186198285673195 4974889042779297428509793)
                  ·
                    refine ⟨3731166782084473071382345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4974889042779297428509793 3731166782084473071382345)
                    ·
                      refine ⟨2798375086563354803536759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3731166782084473071382345 2798375086563354803536759)
                      ·
                        rfl

theorem cell23_5449816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_5449816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449816 prefixEnd_5449816 := by exact prefixLift 5449816
  have htrace : WordTrace (prefixWord ++ tailWord_5449816) baseStart_5449816 baseEnd_5449816 := by
    simpa [prefixWord, tailWord_5449816, baseEnd_5449816] using wordTrace_append hprefix tailTrace_5449816
  have hstable : (prefixWord ++ tailWord_5449816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449816).length < 2 ^ (prefixWord ++ tailWord_5449816).sum := by decide
  have hdescent : baseEnd_5449816 < baseStart_5449816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449825 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_5449825 : Nat := 118140960795 + 5449825 * 2 ^ 59
def prefixEnd_5449825 : Nat := 4983230072969 + 3 ^ 40 * 5449825 * 2
def baseEnd_5449825 : Nat := 2798379707889245268324217

theorem tailTrace_5449825 : CollatzResearch.WordTrace tailWord_5449825 prefixEnd_5449825 2798379707889245268324217 := by
  unfold tailWord_5449825
  simp only [CollatzResearch.WordTrace]
  refine ⟨198771447481222255853838929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132514298320814837235892619 198771447481222255853838929)
  ·
    refine ⟨149078585610916691890379197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198771447481222255853838929 149078585610916691890379197)
    ·
      refine ⟨55904469604093759458892199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149078585610916691890379197 55904469604093759458892199)
      ·
        refine ⟨83856704406140639188338299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55904469604093759458892199 83856704406140639188338299)
        ·
          refine ⟨125785056609210958782507449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83856704406140639188338299 125785056609210958782507449)
          ·
            refine ⟨94338792456908219086880587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125785056609210958782507449 94338792456908219086880587)
            ·
              refine ⟨141508188685362328630320881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94338792456908219086880587 141508188685362328630320881)
              ·
                refine ⟨106131141514021746472740661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141508188685362328630320881 106131141514021746472740661)
                ·
                  refine ⟨9949794516939538731819437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106131141514021746472740661 9949794516939538731819437)
                  ·
                    refine ⟨3731172943852327024432289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9949794516939538731819437 3731172943852327024432289)
                    ·
                      refine ⟨2798379707889245268324217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3731172943852327024432289 2798379707889245268324217)
                      ·
                        rfl

theorem cell23_5449825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_5449825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449825 prefixEnd_5449825 := by exact prefixLift 5449825
  have htrace : WordTrace (prefixWord ++ tailWord_5449825) baseStart_5449825 baseEnd_5449825 := by
    simpa [prefixWord, tailWord_5449825, baseEnd_5449825] using wordTrace_append hprefix tailTrace_5449825
  have hstable : (prefixWord ++ tailWord_5449825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449825).length < 2 ^ (prefixWord ++ tailWord_5449825).sum := by decide
  have hdescent : baseEnd_5449825 < baseStart_5449825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449849 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 2, 1, 3]
def baseStart_5449849 : Nat := 118140960795 + 5449849 * 2 ^ 59
def prefixEnd_5449849 : Nat := 4983230072969 + 3 ^ 40 * 5449849 * 2
def baseEnd_5449849 : Nat := 2798392031424953174424107

theorem tailTrace_5449849 : CollatzResearch.WordTrace tailWord_5449849 prefixEnd_5449849 2798392031424953174424107 := by
  unfold tailWord_5449849
  simp only [CollatzResearch.WordTrace]
  refine ⟨198772322833135307952712601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132514881888756871968475067 198772322833135307952712601)
  ·
    refine ⟨149079242124851480964534451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198772322833135307952712601 149079242124851480964534451)
    ·
      refine ⟨223618863187277221446801677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149079242124851480964534451 223618863187277221446801677)
      ·
        refine ⟨83857073695228958042550629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223618863187277221446801677 83857073695228958042550629)
        ·
          refine ⟨15723201317855429632978243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83857073695228958042550629 15723201317855429632978243)
          ·
            refine ⟨23584801976783144449467365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15723201317855429632978243 23584801976783144449467365)
            ·
              refine ⟨4422150370646839584275131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23584801976783144449467365 4422150370646839584275131)
              ·
                refine ⟨6633225555970259376412697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4422150370646839584275131 6633225555970259376412697)
                ·
                  refine ⟨4974919166977694532309523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6633225555970259376412697 4974919166977694532309523)
                  ·
                    refine ⟨7462378750466541798464285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4974919166977694532309523 7462378750466541798464285)
                    ·
                      refine ⟨2798392031424953174424107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7462378750466541798464285 2798392031424953174424107)
                      ·
                        rfl

theorem cell23_5449849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_5449849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449849 prefixEnd_5449849 := by exact prefixLift 5449849
  have htrace : WordTrace (prefixWord ++ tailWord_5449849) baseStart_5449849 baseEnd_5449849 := by
    simpa [prefixWord, tailWord_5449849, baseEnd_5449849] using wordTrace_append hprefix tailTrace_5449849
  have hstable : (prefixWord ++ tailWord_5449849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449849).length < 2 ^ (prefixWord ++ tailWord_5449849).sum := by decide
  have hdescent : baseEnd_5449849 < baseStart_5449849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449859 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 1, 3, 2]
def baseStart_5449859 : Nat := 118140960795 + 5449859 * 2 ^ 59
def prefixEnd_5449859 : Nat := 4983230072969 + 3 ^ 40 * 5449859 * 2
def baseEnd_5449859 : Nat := 2798397166231498135299061

theorem tailTrace_5449859 : CollatzResearch.WordTrace tailWord_5449859 prefixEnd_5449859 2798397166231498135299061 := by
  unfold tailWord_5449859
  simp only [CollatzResearch.WordTrace]
  refine ⟨198772687563099079660576631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132515125042066053107051087 198772687563099079660576631)
  ·
    refine ⟨298159031344648619490864947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198772687563099079660576631 298159031344648619490864947)
    ·
      refine ⟨447238547016972929236297421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298159031344648619490864947 447238547016972929236297421)
      ·
        refine ⟨167714455131364848463611533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447238547016972929236297421 167714455131364848463611533)
        ·
          refine ⟨62892920674261818173854325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167714455131364848463611533 62892920674261818173854325)
          ·
            refine ⟨5896211313212045453798843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62892920674261818173854325 5896211313212045453798843)
            ·
              refine ⟨8844316969818068180698265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5896211313212045453798843 8844316969818068180698265)
              ·
                refine ⟨6633237727363551135523699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8844316969818068180698265 6633237727363551135523699)
                ·
                  refine ⟨9949856591045326703285549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6633237727363551135523699 9949856591045326703285549)
                  ·
                    refine ⟨3731196221641997513732081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9949856591045326703285549 3731196221641997513732081)
                    ·
                      refine ⟨2798397166231498135299061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3731196221641997513732081 2798397166231498135299061)
                      ·
                        rfl

theorem cell23_5449859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_5449859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449859 prefixEnd_5449859 := by exact prefixLift 5449859
  have htrace : WordTrace (prefixWord ++ tailWord_5449859) baseStart_5449859 baseEnd_5449859 := by
    simpa [prefixWord, tailWord_5449859, baseEnd_5449859] using wordTrace_append hprefix tailTrace_5449859
  have hstable : (prefixWord ++ tailWord_5449859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449859).length < 2 ^ (prefixWord ++ tailWord_5449859).sum := by decide
  have hdescent : baseEnd_5449859 < baseStart_5449859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449868 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_5449868 : Nat := 118140960795 + 5449868 * 2 ^ 59
def prefixEnd_5449868 : Nat := 4983230072969 + 3 ^ 40 * 5449868 * 2
def baseEnd_5449868 : Nat := 2798401787557388600086519

theorem tailTrace_5449868 : CollatzResearch.WordTrace tailWord_5449868 prefixEnd_5449868 2798401787557388600086519 := by
  unfold tailWord_5449868
  simp only [CollatzResearch.WordTrace]
  refine ⟨99386507910033237098827129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132515343880044316131769505 99386507910033237098827129)
  ·
    refine ⟨74539880932524927824120347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99386507910033237098827129 74539880932524927824120347)
    ·
      refine ⟨111809821398787391736180521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74539880932524927824120347 111809821398787391736180521)
      ·
        refine ⟨83857366049090543802135391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111809821398787391736180521 83857366049090543802135391)
        ·
          refine ⟨125786049073635815703203087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83857366049090543802135391 125786049073635815703203087)
          ·
            refine ⟨188679073610453723554804631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125786049073635815703203087 188679073610453723554804631)
            ·
              refine ⟨283018610415680585332206947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188679073610453723554804631 283018610415680585332206947)
              ·
                refine ⟨424527915623520877998310421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283018610415680585332206947 424527915623520877998310421)
                ·
                  refine ⟨19899746044852541156170801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 424527915623520877998310421 19899746044852541156170801)
                  ·
                    refine ⟨14924809533639405867128101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19899746044852541156170801 14924809533639405867128101)
                    ·
                      refine ⟨2798401787557388600086519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14924809533639405867128101 2798401787557388600086519)
                      ·
                        rfl

theorem cell23_5449868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_5449868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449868 prefixEnd_5449868 := by exact prefixLift 5449868
  have htrace : WordTrace (prefixWord ++ tailWord_5449868) baseStart_5449868 baseEnd_5449868 := by
    simpa [prefixWord, tailWord_5449868, baseEnd_5449868] using wordTrace_append hprefix tailTrace_5449868
  have hstable : (prefixWord ++ tailWord_5449868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449868).length < 2 ^ (prefixWord ++ tailWord_5449868).sum := by decide
  have hdescent : baseEnd_5449868 < baseStart_5449868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449889 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_5449889 : Nat := 118140960795 + 5449889 * 2 ^ 59
def prefixEnd_5449889 : Nat := 4983230072969 + 3 ^ 40 * 5449889 * 2
def baseEnd_5449889 : Nat := 2798412570651133017923923

theorem tailTrace_5449889 : CollatzResearch.WordTrace tailWord_5449889 prefixEnd_5449889 2798412570651133017923923 := by
  unfold tailWord_5449889
  simp only [CollatzResearch.WordTrace]
  refine ⟨198773781752990394784168721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132515854501993596522779147 198773781752990394784168721)
  ·
    refine ⟨149080336314742796088126541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198773781752990394784168721 149080336314742796088126541)
    ·
      refine ⟨55905126118028548533047453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149080336314742796088126541 55905126118028548533047453)
      ·
        refine ⟨20964422294260705699892795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55905126118028548533047453 20964422294260705699892795)
        ·
          refine ⟨31446633441391058549839193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20964422294260705699892795 31446633441391058549839193)
          ·
            refine ⟨23584975081043293912379395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31446633441391058549839193 23584975081043293912379395)
            ·
              refine ⟨35377462621564940868569093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23584975081043293912379395 35377462621564940868569093)
              ·
                refine ⟨6633274241543426412856705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35377462621564940868569093 6633274241543426412856705)
                ·
                  refine ⟨4974955681157569809642529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6633274241543426412856705 4974955681157569809642529)
                  ·
                    refine ⟨3731216760868177357231897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4974955681157569809642529 3731216760868177357231897)
                    ·
                      refine ⟨2798412570651133017923923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3731216760868177357231897 2798412570651133017923923)
                      ·
                        rfl

theorem cell23_5449889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_5449889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449889 prefixEnd_5449889 := by exact prefixLift 5449889
  have htrace : WordTrace (prefixWord ++ tailWord_5449889) baseStart_5449889 baseEnd_5449889 := by
    simpa [prefixWord, tailWord_5449889, baseEnd_5449889] using wordTrace_append hprefix tailTrace_5449889
  have hstable : (prefixWord ++ tailWord_5449889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449889).length < 2 ^ (prefixWord ++ tailWord_5449889).sum := by decide
  have hdescent : baseEnd_5449889 < baseStart_5449889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449915 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 2, 5, 2]
def baseStart_5449915 : Nat := 118140960795 + 5449915 * 2 ^ 59
def prefixEnd_5449915 : Nat := 4983230072969 + 3 ^ 40 * 5449915 * 2
def baseEnd_5449915 : Nat := 2798425921148149916198803

theorem tailTrace_5449915 : CollatzResearch.WordTrace tailWord_5449915 prefixEnd_5449915 2798425921148149916198803 := by
  unfold tailWord_5449915
  simp only [CollatzResearch.WordTrace]
  refine ⟨198774730050896201224615199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132516486700597467483076799 198774730050896201224615199)
  ·
    refine ⟨298162095076344301836922799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198774730050896201224615199 298162095076344301836922799)
    ·
      refine ⟨447243142614516452755384199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298162095076344301836922799 447243142614516452755384199)
      ·
        refine ⟨670864713921774679133076299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447243142614516452755384199 670864713921774679133076299)
        ·
          refine ⟨1006297070882662018699614449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670864713921774679133076299 1006297070882662018699614449)
          ·
            refine ⟨754722803161996514024710837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006297070882662018699614449 754722803161996514024710837)
            ·
              refine ⟨70755262796437173189816641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 754722803161996514024710837 70755262796437173189816641)
              ·
                refine ⟨53066447097327879892362481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70755262796437173189816641 53066447097327879892362481)
                ·
                  refine ⟨39799835322995909919271861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53066447097327879892362481 39799835322995909919271861)
                  ·
                    refine ⟨3731234561530866554931737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39799835322995909919271861 3731234561530866554931737)
                    ·
                      refine ⟨2798425921148149916198803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3731234561530866554931737 2798425921148149916198803)
                      ·
                        rfl

theorem cell23_5449915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 5, 2].length) (baseStart_5449915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449915 prefixEnd_5449915 := by exact prefixLift 5449915
  have htrace : WordTrace (prefixWord ++ tailWord_5449915) baseStart_5449915 baseEnd_5449915 := by
    simpa [prefixWord, tailWord_5449915, baseEnd_5449915] using wordTrace_append hprefix tailTrace_5449915
  have hstable : (prefixWord ++ tailWord_5449915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449915).length < 2 ^ (prefixWord ++ tailWord_5449915).sum := by decide
  have hdescent : baseEnd_5449915 < baseStart_5449915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449925 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_5449925 : Nat := 118140960795 + 5449925 * 2 ^ 59
def prefixEnd_5449925 : Nat := 4983230072969 + 3 ^ 40 * 5449925 * 2
def baseEnd_5449925 : Nat := 932810351984898292357919

theorem tailTrace_5449925 : CollatzResearch.WordTrace tailWord_5449925 prefixEnd_5449925 932810351984898292357919 := by
  unfold tailWord_5449925
  simp only [CollatzResearch.WordTrace]
  refine ⟨198775094780859972932479229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132516729853906648621652819 198775094780859972932479229)
  ·
    refine ⟨74540660542822489849679711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198775094780859972932479229 74540660542822489849679711)
    ·
      refine ⟨111810990814233734774519567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74540660542822489849679711 111810990814233734774519567)
      ·
        refine ⟨167716486221350602161779351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111810990814233734774519567 167716486221350602161779351)
        ·
          refine ⟨251574729332025903242669027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167716486221350602161779351 251574729332025903242669027)
          ·
            refine ⟨377362093998038854864003541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251574729332025903242669027 377362093998038854864003541)
            ·
              refine ⟨8844424078079035660875083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 377362093998038854864003541 8844424078079035660875083)
              ·
                refine ⟨13266636117118553491312625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8844424078079035660875083 13266636117118553491312625)
                ·
                  refine ⟨9949977087838915118484469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13266636117118553491312625 9949977087838915118484469)
                  ·
                    refine ⟨932810351984898292357919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9949977087838915118484469 932810351984898292357919)
                    ·
                      rfl

theorem cell23_5449925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_5449925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449925 prefixEnd_5449925 := by exact prefixLift 5449925
  have htrace : WordTrace (prefixWord ++ tailWord_5449925) baseStart_5449925 baseEnd_5449925 := by
    simpa [prefixWord, tailWord_5449925, baseEnd_5449925] using wordTrace_append hprefix tailTrace_5449925
  have hstable : (prefixWord ++ tailWord_5449925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449925).length < 2 ^ (prefixWord ++ tailWord_5449925).sum := by decide
  have hdescent : baseEnd_5449925 < baseStart_5449925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449945 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_5449945 : Nat := 118140960795 + 5449945 * 2 ^ 59
def prefixEnd_5449945 : Nat := 4983230072969 + 3 ^ 40 * 5449945 * 2
def baseEnd_5449945 : Nat := 2798441325567784798823665

theorem tailTrace_5449945 : CollatzResearch.WordTrace tailWord_5449945 prefixEnd_5449945 2798441325567784798823665 := by
  unfold tailWord_5449945
  simp only [CollatzResearch.WordTrace]
  refine ⟨198775824240787516348207289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132517216160525010898804859 198775824240787516348207289)
  ·
    refine ⟨149081868180590637261155467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198775824240787516348207289 149081868180590637261155467)
    ·
      refine ⟨223622802270885955891733201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149081868180590637261155467 223622802270885955891733201)
      ·
        refine ⟨167717101703164466918799901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223622802270885955891733201 167717101703164466918799901)
        ·
          refine ⟨62893913138686675094549963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167717101703164466918799901 62893913138686675094549963)
          ·
            refine ⟨94340869708030012641824945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62893913138686675094549963 94340869708030012641824945)
            ·
              refine ⟨70755652281022509481368709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94340869708030012641824945 70755652281022509481368709)
              ·
                refine ⟨13266684802691720527756633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70755652281022509481368709 13266684802691720527756633)
                ·
                  refine ⟨9950013602018790395817475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13266684802691720527756633 9950013602018790395817475)
                  ·
                    refine ⟨14925020403028185593726213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9950013602018790395817475 14925020403028185593726213)
                    ·
                      refine ⟨2798441325567784798823665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14925020403028185593726213 2798441325567784798823665)
                      ·
                        rfl

theorem cell23_5449945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_5449945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449945 prefixEnd_5449945 := by exact prefixLift 5449945
  have htrace : WordTrace (prefixWord ++ tailWord_5449945) baseStart_5449945 baseEnd_5449945 := by
    simpa [prefixWord, tailWord_5449945, baseEnd_5449945] using wordTrace_append hprefix tailTrace_5449945
  have hstable : (prefixWord ++ tailWord_5449945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449945).length < 2 ^ (prefixWord ++ tailWord_5449945).sum := by decide
  have hdescent : baseEnd_5449945 < baseStart_5449945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449962 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_5449962 : Nat := 118140960795 + 5449962 * 2 ^ 59
def prefixEnd_5449962 : Nat := 4983230072969 + 3 ^ 40 * 5449962 * 2
def baseEnd_5449962 : Nat := 2798450054738911232311087

theorem tailTrace_5449962 : CollatzResearch.WordTrace tailWord_5449962 prefixEnd_5449962 2798450054738911232311087 := by
  unfold tailWord_5449962
  simp only [CollatzResearch.WordTrace]
  refine ⟨49694111070431482062894035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132517629521150618834384093 49694111070431482062894035)
  ·
    refine ⟨74541166605647223094341053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49694111070431482062894035 74541166605647223094341053)
    ·
      refine ⟨27952937477117708660377895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74541166605647223094341053 27952937477117708660377895)
      ·
        refine ⟨41929406215676562990566843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27952937477117708660377895 41929406215676562990566843)
        ·
          refine ⟨62894109323514844485850265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41929406215676562990566843 62894109323514844485850265)
          ·
            refine ⟨47170581992636133364387699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62894109323514844485850265 47170581992636133364387699)
            ·
              refine ⟨70755872988954200046581549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47170581992636133364387699 70755872988954200046581549)
              ·
                refine ⟨26533452370857825017468081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70755872988954200046581549 26533452370857825017468081)
                ·
                  refine ⟨19900089278143368763101061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26533452370857825017468081 19900089278143368763101061)
                  ·
                    refine ⟨3731266739651881643081449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19900089278143368763101061 3731266739651881643081449)
                    ·
                      refine ⟨2798450054738911232311087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3731266739651881643081449 2798450054738911232311087)
                      ·
                        rfl

theorem cell23_5449962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_5449962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449962 prefixEnd_5449962 := by exact prefixLift 5449962
  have htrace : WordTrace (prefixWord ++ tailWord_5449962) baseStart_5449962 baseEnd_5449962 := by
    simpa [prefixWord, tailWord_5449962, baseEnd_5449962] using wordTrace_append hprefix tailTrace_5449962
  have hstable : (prefixWord ++ tailWord_5449962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449962).length < 2 ^ (prefixWord ++ tailWord_5449962).sum := by decide
  have hdescent : baseEnd_5449962 < baseStart_5449962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5449982 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_5449982 : Nat := 118140960795 + 5449982 * 2 ^ 59
def prefixEnd_5449982 : Nat := 4983230072969 + 3 ^ 40 * 5449982 * 2
def baseEnd_5449982 : Nat := 2798460324352001154060995

theorem tailTrace_5449982 : CollatzResearch.WordTrace tailWord_5449982 prefixEnd_5449982 2798460324352001154060995 := by
  unfold tailWord_5449982
  simp only [CollatzResearch.WordTrace]
  refine ⟨24847146717706683958413025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132518115827768981111536133 24847146717706683958413025)
  ·
    refine ⟨18635360038280012968809769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24847146717706683958413025 18635360038280012968809769)
    ·
      refine ⟨13976520028710009726607327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18635360038280012968809769 13976520028710009726607327)
      ·
        refine ⟨20964780043065014589910991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13976520028710009726607327 20964780043065014589910991)
        ·
          refine ⟨31447170064597521884866487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20964780043065014589910991 31447170064597521884866487)
          ·
            refine ⟨47170755096896282827299731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31447170064597521884866487 47170755096896282827299731)
            ·
              refine ⟨70756132645344424240949597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47170755096896282827299731 70756132645344424240949597)
              ·
                refine ⟨26533549742004159090356099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70756132645344424240949597 26533549742004159090356099)
                ·
                  refine ⟨39800324613006238635534149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26533549742004159090356099 39800324613006238635534149)
                  ·
                    refine ⟨7462560864938669744162653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39800324613006238635534149 7462560864938669744162653)
                    ·
                      refine ⟨2798460324352001154060995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7462560864938669744162653 2798460324352001154060995)
                      ·
                        rfl

theorem cell23_5449982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_5449982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5449982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5449982 prefixEnd_5449982 := by exact prefixLift 5449982
  have htrace : WordTrace (prefixWord ++ tailWord_5449982) baseStart_5449982 baseEnd_5449982 := by
    simpa [prefixWord, tailWord_5449982, baseEnd_5449982] using wordTrace_append hprefix tailTrace_5449982
  have hstable : (prefixWord ++ tailWord_5449982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5449982).length < 2 ^ (prefixWord ++ tailWord_5449982).sum := by decide
  have hdescent : baseEnd_5449982 < baseStart_5449982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5449982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450119 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_5450119 : Nat := 118140960795 + 5450119 * 2 ^ 59
def prefixEnd_5450119 : Nat := 4983230072969 + 3 ^ 40 * 5450119 * 2
def baseEnd_5450119 : Nat := 2798530671201667118047865

theorem tailTrace_5450119 : CollatzResearch.WordTrace tailWord_5450119 prefixEnd_5450119 2798530671201667118047865 := by
  unfold tailWord_5450119
  simp only [CollatzResearch.WordTrace]
  refine ⟨198782170542157144065041411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132521447028104762710027607 198782170542157144065041411)
  ·
    refine ⟨298173255813235716097562117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198782170542157144065041411 298173255813235716097562117)
    ·
      refine ⟨55907485464981696768292897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298173255813235716097562117 55907485464981696768292897)
      ·
        refine ⟨41930614098736272576219673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55907485464981696768292897 41930614098736272576219673)
        ·
          refine ⟨31447960574052204432164755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41930614098736272576219673 31447960574052204432164755)
          ·
            refine ⟨47171940861078306648247133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31447960574052204432164755 47171940861078306648247133)
            ·
              refine ⟨17689477822904364993092675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47171940861078306648247133 17689477822904364993092675)
              ·
                refine ⟨26534216734356547489639013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17689477822904364993092675 26534216734356547489639013)
                ·
                  refine ⟨4975165637691852654307315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26534216734356547489639013 4975165637691852654307315)
                  ·
                    refine ⟨7462748456537778981460973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4975165637691852654307315 7462748456537778981460973)
                    ·
                      refine ⟨2798530671201667118047865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7462748456537778981460973 2798530671201667118047865)
                      ·
                        rfl

theorem cell23_5450119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_5450119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450119 prefixEnd_5450119 := by exact prefixLift 5450119
  have htrace : WordTrace (prefixWord ++ tailWord_5450119) baseStart_5450119 baseEnd_5450119 := by
    simpa [prefixWord, tailWord_5450119, baseEnd_5450119] using wordTrace_append hprefix tailTrace_5450119
  have hstable : (prefixWord ++ tailWord_5450119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450119).length < 2 ^ (prefixWord ++ tailWord_5450119).sum := by decide
  have hdescent : baseEnd_5450119 < baseStart_5450119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450136 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5450136 : Nat := 118140960795 + 5450136 * 2 ^ 59
def prefixEnd_5450136 : Nat := 4983230072969 + 3 ^ 40 * 5450136 * 2
def baseEnd_5450136 : Nat := 2798539400372793551535287

theorem tailTrace_5450136 : CollatzResearch.WordTrace tailWord_5450136 prefixEnd_5450136 2798539400372793551535287 := by
  unfold tailWord_5450136
  simp only [CollatzResearch.WordTrace]
  refine ⟨99391395291547777984205131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132521860388730370645606841 99391395291547777984205131)
  ·
    refine ⟨149087092937321666976307697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99391395291547777984205131 149087092937321666976307697)
    ·
      refine ⟨111815319702991250232230773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149087092937321666976307697 111815319702991250232230773)
      ·
        refine ⟨10482686222155429709271635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111815319702991250232230773 10482686222155429709271635)
        ·
          refine ⟨15724029333233144563907453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10482686222155429709271635 15724029333233144563907453)
          ·
            refine ⟨5896510999962429211465295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15724029333233144563907453 5896510999962429211465295)
            ·
              refine ⟨8844766499943643817197943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5896510999962429211465295 8844766499943643817197943)
              ·
                refine ⟨13267149749915465725796915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8844766499943643817197943 13267149749915465725796915)
                ·
                  refine ⟨19900724624873198588695373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13267149749915465725796915 19900724624873198588695373)
                  ·
                    refine ⟨7462771734327449470760765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19900724624873198588695373 7462771734327449470760765)
                    ·
                      refine ⟨2798539400372793551535287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7462771734327449470760765 2798539400372793551535287)
                      ·
                        rfl

theorem cell23_5450136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5450136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450136 prefixEnd_5450136 := by exact prefixLift 5450136
  have htrace : WordTrace (prefixWord ++ tailWord_5450136) baseStart_5450136 baseEnd_5450136 := by
    simpa [prefixWord, tailWord_5450136, baseEnd_5450136] using wordTrace_append hprefix tailTrace_5450136
  have hstable : (prefixWord ++ tailWord_5450136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450136).length < 2 ^ (prefixWord ++ tailWord_5450136).sum := by decide
  have hdescent : baseEnd_5450136 < baseStart_5450136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450162 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_5450162 : Nat := 118140960795 + 5450162 * 2 ^ 59
def prefixEnd_5450162 : Nat := 4983230072969 + 3 ^ 40 * 5450162 * 2
def baseEnd_5450162 : Nat := 2798552750869810449810167

theorem tailTrace_5450162 : CollatzResearch.WordTrace tailWord_5450162 prefixEnd_5450162 2798552750869810449810167 := by
  unfold tailWord_5450162
  simp only [CollatzResearch.WordTrace]
  refine ⟨49695934720250340602214185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132522492587334241605904493 49695934720250340602214185)
  ·
    refine ⟨37271951040187755451660639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49695934720250340602214185 37271951040187755451660639)
    ·
      refine ⟨55907926560281633177490959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37271951040187755451660639 55907926560281633177490959)
      ·
        refine ⟨83861889840422449766236439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55907926560281633177490959 83861889840422449766236439)
        ·
          refine ⟨125792834760633674649354659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83861889840422449766236439 125792834760633674649354659)
          ·
            refine ⟨188689252140950511974031989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125792834760633674649354659 188689252140950511974031989)
            ·
              refine ⟨17689617388214110497565499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188689252140950511974031989 17689617388214110497565499)
              ·
                refine ⟨26534426082321165746348249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17689617388214110497565499 26534426082321165746348249)
                ·
                  refine ⟨19900819561740874309761187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26534426082321165746348249 19900819561740874309761187)
                  ·
                    refine ⟨29851229342611311464641781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19900819561740874309761187 29851229342611311464641781)
                    ·
                      refine ⟨2798552750869810449810167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29851229342611311464641781 2798552750869810449810167)
                      ·
                        rfl

theorem cell23_5450162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_5450162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450162 prefixEnd_5450162 := by exact prefixLift 5450162
  have htrace : WordTrace (prefixWord ++ tailWord_5450162) baseStart_5450162 baseEnd_5450162 := by
    simpa [prefixWord, tailWord_5450162, baseEnd_5450162] using wordTrace_append hprefix tailTrace_5450162
  have hstable : (prefixWord ++ tailWord_5450162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450162).length < 2 ^ (prefixWord ++ tailWord_5450162).sum := by decide
  have hdescent : baseEnd_5450162 < baseStart_5450162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450176 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 2, 2, 2]
def baseStart_5450176 : Nat := 118140960795 + 5450176 * 2 ^ 59
def prefixEnd_5450176 : Nat := 4983230072969 + 3 ^ 40 * 5450176 * 2
def baseEnd_5450176 : Nat := 2798559939598973395035103

theorem tailTrace_5450176 : CollatzResearch.WordTrace tailWord_5450176 prefixEnd_5450176 2798559939598973395035103 := by
  unfold tailWord_5450176
  simp only [CollatzResearch.WordTrace]
  refine ⟨99392124751475321399933191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132522833001967095199910921 99392124751475321399933191)
  ·
    refine ⟨149088187127212982099899787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99392124751475321399933191 149088187127212982099899787)
    ·
      refine ⟨223632280690819473149849681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149088187127212982099899787 223632280690819473149849681)
      ·
        refine ⟨167724210518114604862387261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223632280690819473149849681 167724210518114604862387261)
        ·
          refine ⟨62896578944292976823395223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167724210518114604862387261 62896578944292976823395223)
          ·
            refine ⟨94344868416439465235092835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62896578944292976823395223 94344868416439465235092835)
            ·
              refine ⟨141517302624659197852639253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94344868416439465235092835 141517302624659197852639253)
              ·
                refine ⟨6633623560530899899342465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141517302624659197852639253 6633623560530899899342465)
                ·
                  refine ⟨4975217670398174924506849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6633623560530899899342465 4975217670398174924506849)
                  ·
                    refine ⟨3731413252798631193380137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4975217670398174924506849 3731413252798631193380137)
                    ·
                      refine ⟨2798559939598973395035103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3731413252798631193380137 2798559939598973395035103)
                      ·
                        rfl

theorem cell23_5450176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_5450176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450176 prefixEnd_5450176 := by exact prefixLift 5450176
  have htrace : WordTrace (prefixWord ++ tailWord_5450176) baseStart_5450176 baseEnd_5450176 := by
    simpa [prefixWord, tailWord_5450176, baseEnd_5450176] using wordTrace_append hprefix tailTrace_5450176
  have hstable : (prefixWord ++ tailWord_5450176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450176).length < 2 ^ (prefixWord ++ tailWord_5450176).sum := by decide
  have hdescent : baseEnd_5450176 < baseStart_5450176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450210 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_5450210 : Nat := 118140960795 + 5450210 * 2 ^ 59
def prefixEnd_5450210 : Nat := 4983230072969 + 3 ^ 40 * 5450210 * 2
def baseEnd_5450210 : Nat := 2798577397941226262009947

theorem tailTrace_5450210 : CollatzResearch.WordTrace tailWord_5450210 prefixEnd_5450210 2798577397941226262009947 := by
  unfold tailWord_5450210
  simp only [CollatzResearch.WordTrace]
  refine ⟨49696372396206866651651021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132523659723218311071069389 49696372396206866651651021)
  ·
    refine ⟨18636139648577574994369133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49696372396206866651651021 18636139648577574994369133)
    ·
      refine ⟨6988552368216590622888425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18636139648577574994369133 6988552368216590622888425)
      ·
        refine ⟨5241414276162442967166319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6988552368216590622888425 5241414276162442967166319)
        ·
          refine ⟨7862121414243664450749479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5241414276162442967166319 7862121414243664450749479)
          ·
            refine ⟨11793182121365496676124219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7862121414243664450749479 11793182121365496676124219)
            ·
              refine ⟨17689773182048245014186329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11793182121365496676124219 17689773182048245014186329)
              ·
                refine ⟨13267329886536183760639747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17689773182048245014186329 13267329886536183760639747)
                ·
                  refine ⟨19900994829804275640959621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13267329886536183760639747 19900994829804275640959621)
                  ·
                    refine ⟨3731436530588301682679929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19900994829804275640959621 3731436530588301682679929)
                    ·
                      refine ⟨2798577397941226262009947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3731436530588301682679929 2798577397941226262009947)
                      ·
                        rfl

theorem cell23_5450210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_5450210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450210 prefixEnd_5450210 := by exact prefixLift 5450210
  have htrace : WordTrace (prefixWord ++ tailWord_5450210) baseStart_5450210 baseEnd_5450210 := by
    simpa [prefixWord, tailWord_5450210, baseEnd_5450210] using wordTrace_append hprefix tailTrace_5450210
  have hstable : (prefixWord ++ tailWord_5450210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450210).length < 2 ^ (prefixWord ++ tailWord_5450210).sum := by decide
  have hdescent : baseEnd_5450210 < baseStart_5450210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450259 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 3, 4]
def baseStart_5450259 : Nat := 118140960795 + 5450259 * 2 ^ 59
def prefixEnd_5450259 : Nat := 4983230072969 + 3 ^ 40 * 5450259 * 2
def baseEnd_5450259 : Nat := 932867519497765523432407

theorem tailTrace_5450259 : CollatzResearch.WordTrace tailWord_5450259 prefixEnd_5450259 932867519497765523432407 := by
  unfold tailWord_5450259
  simp only [CollatzResearch.WordTrace]
  refine ⟨198787276761649947975137831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132524851174433298650091887 198787276761649947975137831)
  ·
    refine ⟨298180915142474921962706747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198787276761649947975137831 298180915142474921962706747)
    ·
      refine ⟨447271372713712382944060121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298180915142474921962706747 447271372713712382944060121)
      ·
        refine ⟨335453529535284287208045091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447271372713712382944060121 335453529535284287208045091)
        ·
          refine ⟨503180294302926430812067637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335453529535284287208045091 503180294302926430812067637)
          ·
            refine ⟨47173152590899352888631341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 503180294302926430812067637 47173152590899352888631341)
            ·
              refine ⟨17689932221587257333236753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47173152590899352888631341 17689932221587257333236753)
              ·
                refine ⟨13267449166190442999927565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17689932221587257333236753 13267449166190442999927565)
                ·
                  refine ⟨4975293437321416124972837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13267449166190442999927565 4975293437321416124972837)
                  ·
                    refine ⟨932867519497765523432407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4975293437321416124972837 932867519497765523432407)
                    ·
                      rfl

theorem cell23_5450259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 4].length) (baseStart_5450259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450259 prefixEnd_5450259 := by exact prefixLift 5450259
  have htrace : WordTrace (prefixWord ++ tailWord_5450259) baseStart_5450259 baseEnd_5450259 := by
    simpa [prefixWord, tailWord_5450259, baseEnd_5450259] using wordTrace_append hprefix tailTrace_5450259
  have hstable : (prefixWord ++ tailWord_5450259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450259).length < 2 ^ (prefixWord ++ tailWord_5450259).sum := by decide
  have hdescent : baseEnd_5450259 < baseStart_5450259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450263 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 2, 5]
def baseStart_5450263 : Nat := 118140960795 + 5450263 * 2 ^ 59
def prefixEnd_5450263 : Nat := 4983230072969 + 3 ^ 40 * 5450263 * 2
def baseEnd_5450263 : Nat := 932868204138638184882401

theorem tailTrace_5450263 : CollatzResearch.WordTrace tailWord_5450263 prefixEnd_5450263 932868204138638184882401 := by
  unfold tailWord_5450263
  simp only [CollatzResearch.WordTrace]
  refine ⟨198787422653635456658283443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132524948435756971105522295 198787422653635456658283443)
  ·
    refine ⟨298181133980453184987425165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198787422653635456658283443 298181133980453184987425165)
    ·
      refine ⟨111817925242669944370284437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298181133980453184987425165 111817925242669944370284437)
      ·
        refine ⟨5241465245750153642357083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111817925242669944370284437 5241465245750153642357083)
        ·
          refine ⟨7862197868625230463535625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5241465245750153642357083 7862197868625230463535625)
          ·
            refine ⟨5896648401468922847651719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7862197868625230463535625 5896648401468922847651719)
            ·
              refine ⟨8844972602203384271477579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5896648401468922847651719 8844972602203384271477579)
              ·
                refine ⟨13267458903305076407216369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8844972602203384271477579 13267458903305076407216369)
                ·
                  refine ⟨9950594177478807305412277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13267458903305076407216369 9950594177478807305412277)
                  ·
                    refine ⟨932868204138638184882401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9950594177478807305412277 932868204138638184882401)
                    ·
                      rfl

theorem cell23_5450263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_5450263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450263 prefixEnd_5450263 := by exact prefixLift 5450263
  have htrace : WordTrace (prefixWord ++ tailWord_5450263) baseStart_5450263 baseEnd_5450263 := by
    simpa [prefixWord, tailWord_5450263, baseEnd_5450263] using wordTrace_append hprefix tailTrace_5450263
  have hstable : (prefixWord ++ tailWord_5450263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450263).length < 2 ^ (prefixWord ++ tailWord_5450263).sum := by decide
  have hdescent : baseEnd_5450263 < baseStart_5450263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450289 : List Nat := [1, 2, 2, 3, 1, 1, 5, 2, 6]
def baseStart_5450289 : Nat := 118140960795 + 5450289 * 2 ^ 59
def prefixEnd_5450289 : Nat := 4983230072969 + 3 ^ 40 * 5450289 * 2
def baseEnd_5450289 : Nat := 310957551434770161435787

theorem tailTrace_5450289 : CollatzResearch.WordTrace tailWord_5450289 prefixEnd_5450289 310957551434770161435787 := by
  unfold tailWord_5450289
  simp only [CollatzResearch.WordTrace]
  refine ⟨198788370951541263098729921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132525580634360842065819947 198788370951541263098729921)
  ·
    refine ⟨149091278213655947324047441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198788370951541263098729921 149091278213655947324047441)
    ·
      refine ⟨111818458660241960493035581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149091278213655947324047441 111818458660241960493035581)
      ·
        refine ⟨41931921997590735184888343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111818458660241960493035581 41931921997590735184888343)
        ·
          refine ⟨62897882996386102777332515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41931921997590735184888343 62897882996386102777332515)
          ·
            refine ⟨94346824494579154165998773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62897882996386102777332515 94346824494579154165998773)
            ·
              refine ⟨8845014796366795703062385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94346824494579154165998773 8845014796366795703062385)
              ·
                refine ⟨6633761097275096777296789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8845014796366795703062385 6633761097275096777296789)
                ·
                  refine ⟨310957551434770161435787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6633761097275096777296789 310957551434770161435787)
                  ·
                    rfl

theorem cell23_5450289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 2, 6].length) (baseStart_5450289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450289 prefixEnd_5450289 := by exact prefixLift 5450289
  have htrace : WordTrace (prefixWord ++ tailWord_5450289) baseStart_5450289 baseEnd_5450289 := by
    simpa [prefixWord, tailWord_5450289, baseEnd_5450289] using wordTrace_append hprefix tailTrace_5450289
  have hstable : (prefixWord ++ tailWord_5450289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450289).length < 2 ^ (prefixWord ++ tailWord_5450289).sum := by decide
  have hdescent : baseEnd_5450289 < baseStart_5450289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450312 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_5450312 : Nat := 118140960795 + 5450312 * 2 ^ 59
def prefixEnd_5450312 : Nat := 4983230072969 + 3 ^ 40 * 5450312 * 2
def baseEnd_5450312 : Nat := 2798629772967984862934477

theorem tailTrace_5450312 : CollatzResearch.WordTrace tailWord_5450312 prefixEnd_5450312 2798629772967984862934477 := by
  unfold tailWord_5450312
  simp only [CollatzResearch.WordTrace]
  refine ⟨99394604915228969013408595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132526139886971958684544793 99394604915228969013408595)
  ·
    refine ⟨149091907372843453520112893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99394604915228969013408595 149091907372843453520112893)
    ·
      refine ⟨55909465264816295070042335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149091907372843453520112893 55909465264816295070042335)
      ·
        refine ⟨83864197897224442605063503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55909465264816295070042335 83864197897224442605063503)
        ·
          refine ⟨125796296845836663907595255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83864197897224442605063503 125796296845836663907595255)
          ·
            refine ⟨188694445268754995861392883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125796296845836663907595255 188694445268754995861392883)
            ·
              refine ⟨283041667903132493792089325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188694445268754995861392883 283041667903132493792089325)
              ·
                refine ⟨106140625463674685172033497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283041667903132493792089325 106140625463674685172033497)
                ·
                  refine ⟨79605469097756013879025123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106140625463674685172033497 79605469097756013879025123)
                  ·
                    refine ⟨119408203646634020818537685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79605469097756013879025123 119408203646634020818537685)
                    ·
                      refine ⟨2798629772967984862934477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119408203646634020818537685 2798629772967984862934477)
                      ·
                        rfl

theorem cell23_5450312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_5450312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450312 prefixEnd_5450312 := by exact prefixLift 5450312
  have htrace : WordTrace (prefixWord ++ tailWord_5450312) baseStart_5450312 baseEnd_5450312 := by
    simpa [prefixWord, tailWord_5450312, baseEnd_5450312] using wordTrace_append hprefix tailTrace_5450312
  have hstable : (prefixWord ++ tailWord_5450312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450312).length < 2 ^ (prefixWord ++ tailWord_5450312).sum := by decide
  have hdescent : baseEnd_5450312 < baseStart_5450312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450316 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 3, 1, 3]
def baseStart_5450316 : Nat := 118140960795 + 5450316 * 2 ^ 59
def prefixEnd_5450316 : Nat := 4983230072969 + 3 ^ 40 * 5450316 * 2
def baseEnd_5450316 : Nat := 2798631826890602847284459

theorem tailTrace_5450316 : CollatzResearch.WordTrace tailWord_5450316 prefixEnd_5450316 2798631826890602847284459 := by
  unfold tailWord_5450316
  simp only [CollatzResearch.WordTrace]
  refine ⟨99394677861221723354981401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132526237148295631139975201 99394677861221723354981401)
  ·
    refine ⟨74546008395916292516236051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99394677861221723354981401 74546008395916292516236051)
    ·
      refine ⟨111819012593874438774354077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74546008395916292516236051 111819012593874438774354077)
      ·
        refine ⟨41932129722702914540382779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111819012593874438774354077 41932129722702914540382779)
        ·
          refine ⟨62898194584054371810574169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41932129722702914540382779 62898194584054371810574169)
          ·
            refine ⟨47173645938040778857930627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62898194584054371810574169 47173645938040778857930627)
            ·
              refine ⟨70760468907061168286895941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47173645938040778857930627 70760468907061168286895941)
              ·
                refine ⟨13267587920073969053792989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70760468907061168286895941 13267587920073969053792989)
                ·
                  refine ⟨4975345470027738395172371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13267587920073969053792989 4975345470027738395172371)
                  ·
                    refine ⟨7463018205041607592758557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4975345470027738395172371 7463018205041607592758557)
                    ·
                      refine ⟨2798631826890602847284459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7463018205041607592758557 2798631826890602847284459)
                      ·
                        rfl

theorem cell23_5450316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_5450316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450316 prefixEnd_5450316 := by exact prefixLift 5450316
  have htrace : WordTrace (prefixWord ++ tailWord_5450316) baseStart_5450316 baseEnd_5450316 := by
    simpa [prefixWord, tailWord_5450316, baseEnd_5450316] using wordTrace_append hprefix tailTrace_5450316
  have hstable : (prefixWord ++ tailWord_5450316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450316).length < 2 ^ (prefixWord ++ tailWord_5450316).sum := by decide
  have hdescent : baseEnd_5450316 < baseStart_5450316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450319 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 1, 5]
def baseStart_5450319 : Nat := 118140960795 + 5450319 * 2 ^ 59
def prefixEnd_5450319 : Nat := 4983230072969 + 3 ^ 40 * 5450319 * 2
def baseEnd_5450319 : Nat := 932877789110855445182315

theorem tailTrace_5450319 : CollatzResearch.WordTrace tailWord_5450319 prefixEnd_5450319 932877789110855445182315 := by
  unfold tailWord_5450319
  simp only [CollatzResearch.WordTrace]
  refine ⟨198789465141432578222322011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132526310094288385481548007 198789465141432578222322011)
  ·
    refine ⟨298184197712148867333483017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198789465141432578222322011 298184197712148867333483017)
    ·
      refine ⟨223638148284111650500112263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298184197712148867333483017 223638148284111650500112263)
      ·
        refine ⟨335457222426167475750168395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223638148284111650500112263 335457222426167475750168395)
        ·
          refine ⟨503185833639251213625252593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335457222426167475750168395 503185833639251213625252593)
          ·
            refine ⟨377389375229438410218939445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503185833639251213625252593 377389375229438410218939445)
            ·
              refine ⟨35380253927759850958025573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 377389375229438410218939445 35380253927759850958025573)
              ·
                refine ⟨6633797611454972054629795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35380253927759850958025573 6633797611454972054629795)
                ·
                  refine ⟨9950696417182458081944693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6633797611454972054629795 9950696417182458081944693)
                  ·
                    refine ⟨932877789110855445182315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9950696417182458081944693 932877789110855445182315)
                    ·
                      rfl

theorem cell23_5450319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 5].length) (baseStart_5450319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450319 prefixEnd_5450319 := by exact prefixLift 5450319
  have htrace : WordTrace (prefixWord ++ tailWord_5450319) baseStart_5450319 baseEnd_5450319 := by
    simpa [prefixWord, tailWord_5450319, baseEnd_5450319] using wordTrace_append hprefix tailTrace_5450319
  have hstable : (prefixWord ++ tailWord_5450319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450319).length < 2 ^ (prefixWord ++ tailWord_5450319).sum := by decide
  have hdescent : baseEnd_5450319 < baseStart_5450319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450350 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_5450350 : Nat := 118140960795 + 5450350 * 2 ^ 59
def prefixEnd_5450350 : Nat := 4983230072969 + 3 ^ 40 * 5450350 * 2
def baseEnd_5450350 : Nat := 2798649285232855714259303

theorem tailTrace_5450350 : CollatzResearch.WordTrace tailWord_5450350 prefixEnd_5450350 2798649285232855714259303 := by
  unfold tailWord_5450350
  simp only [CollatzResearch.WordTrace]
  refine ⟨24848824475540033814587563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132527063869546847011133669 24848824475540033814587563)
  ·
    refine ⟨37273236713310050721881345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24848824475540033814587563 37273236713310050721881345)
    ·
      refine ⟨27954927534982538041411009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37273236713310050721881345 27954927534982538041411009)
      ·
        refine ⟨20966195651236903531058257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27954927534982538041411009 20966195651236903531058257)
        ·
          refine ⟨15724646738427677648293693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20966195651236903531058257 15724646738427677648293693)
          ·
            refine ⟨5896742526910379118110135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15724646738427677648293693 5896742526910379118110135)
            ·
              refine ⟨8845113790365568677165203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5896742526910379118110135 8845113790365568677165203)
              ·
                refine ⟨13267670685548353015747805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8845113790365568677165203 13267670685548353015747805)
                ·
                  refine ⟨4975376507080632380905427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13267670685548353015747805 4975376507080632380905427)
                  ·
                    refine ⟨7463064760620948571358141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4975376507080632380905427 7463064760620948571358141)
                    ·
                      refine ⟨2798649285232855714259303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7463064760620948571358141 2798649285232855714259303)
                      ·
                        rfl

theorem cell23_5450350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_5450350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450350 prefixEnd_5450350 := by exact prefixLift 5450350
  have htrace : WordTrace (prefixWord ++ tailWord_5450350) baseStart_5450350 baseEnd_5450350 := by
    simpa [prefixWord, tailWord_5450350, baseEnd_5450350] using wordTrace_append hprefix tailTrace_5450350
  have hstable : (prefixWord ++ tailWord_5450350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450350).length < 2 ^ (prefixWord ++ tailWord_5450350).sum := by decide
  have hdescent : baseEnd_5450350 < baseStart_5450350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450359 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_5450359 : Nat := 118140960795 + 5450359 * 2 ^ 59
def prefixEnd_5450359 : Nat := 4983230072969 + 3 ^ 40 * 5450359 * 2
def baseEnd_5450359 : Nat := 2798653906558746179046761

theorem tailTrace_5450359 : CollatzResearch.WordTrace tailWord_5450359 prefixEnd_5450359 2798653906558746179046761 := by
  unfold tailWord_5450359
  simp only [CollatzResearch.WordTrace]
  refine ⟨198790924061287665053778131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132527282707525110035852087 198790924061287665053778131)
  ·
    refine ⟨298186386091931497580667197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198790924061287665053778131 298186386091931497580667197)
    ·
      refine ⟨111819894784474311592750199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298186386091931497580667197 111819894784474311592750199)
      ·
        refine ⟨167729842176711467389125299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111819894784474311592750199 167729842176711467389125299)
        ·
          refine ⟨251594763265067201083687949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167729842176711467389125299 251594763265067201083687949)
          ·
            refine ⟨94348036224400200406382981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251594763265067201083687949 94348036224400200406382981)
            ·
              refine ⟨17690256792075037576196809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94348036224400200406382981 17690256792075037576196809)
              ·
                refine ⟨13267692594056278182147607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17690256792075037576196809 13267692594056278182147607)
                ·
                  refine ⟨19901538891084417273221411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13267692594056278182147607 19901538891084417273221411)
                  ·
                    refine ⟨29852308336626625909832117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19901538891084417273221411 29852308336626625909832117)
                    ·
                      refine ⟨2798653906558746179046761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29852308336626625909832117 2798653906558746179046761)
                      ·
                        rfl

theorem cell23_5450359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_5450359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450359 prefixEnd_5450359 := by exact prefixLift 5450359
  have htrace : WordTrace (prefixWord ++ tailWord_5450359) baseStart_5450359 baseEnd_5450359 := by
    simpa [prefixWord, tailWord_5450359, baseEnd_5450359] using wordTrace_append hprefix tailTrace_5450359
  have hstable : (prefixWord ++ tailWord_5450359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450359).length < 2 ^ (prefixWord ++ tailWord_5450359).sum := by decide
  have hdescent : baseEnd_5450359 < baseStart_5450359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450369 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_5450369 : Nat := 118140960795 + 5450369 * 2 ^ 59
def prefixEnd_5450369 : Nat := 4983230072969 + 3 ^ 40 * 5450369 * 2
def baseEnd_5450369 : Nat := 2798659041365291139921715

theorem tailTrace_5450369 : CollatzResearch.WordTrace tailWord_5450369 prefixEnd_5450369 2798659041365291139921715 := by
  unfold tailWord_5450369
  simp only [CollatzResearch.WordTrace]
  refine ⟨198791288791251436761642161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132527525860834291174428107 198791288791251436761642161)
  ·
    refine ⟨149093466593438577571231621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198791288791251436761642161 149093466593438577571231621)
    ·
      refine ⟨27955024986269733294605929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149093466593438577571231621 27955024986269733294605929)
      ·
        refine ⟨20966268739702299970954447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27955024986269733294605929 20966268739702299970954447)
        ·
          refine ⟨31449403109553449956431671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20966268739702299970954447 31449403109553449956431671)
          ·
            refine ⟨47174104664330174934647507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31449403109553449956431671 47174104664330174934647507)
            ·
              refine ⟨70761156996495262401971261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47174104664330174934647507 70761156996495262401971261)
              ·
                refine ⟨26535433873685723400739223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70761156996495262401971261 26535433873685723400739223)
                ·
                  refine ⟨39803150810528585101108835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26535433873685723400739223 39803150810528585101108835)
                  ·
                    refine ⟨59704726215792877651663253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39803150810528585101108835 59704726215792877651663253)
                    ·
                      refine ⟨2798659041365291139921715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59704726215792877651663253 2798659041365291139921715)
                      ·
                        rfl

theorem cell23_5450369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_5450369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450369 prefixEnd_5450369 := by exact prefixLift 5450369
  have htrace : WordTrace (prefixWord ++ tailWord_5450369) baseStart_5450369 baseEnd_5450369 := by
    simpa [prefixWord, tailWord_5450369, baseEnd_5450369] using wordTrace_append hprefix tailTrace_5450369
  have hstable : (prefixWord ++ tailWord_5450369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450369).length < 2 ^ (prefixWord ++ tailWord_5450369).sum := by decide
  have hdescent : baseEnd_5450369 < baseStart_5450369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450373 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 4]
def baseStart_5450373 : Nat := 118140960795 + 5450373 * 2 ^ 59
def prefixEnd_5450373 : Nat := 4983230072969 + 3 ^ 40 * 5450373 * 2
def baseEnd_5450373 : Nat := 2798661095287909124271697

theorem tailTrace_5450373 : CollatzResearch.WordTrace tailWord_5450373 prefixEnd_5450373 2798661095287909124271697 := by
  unfold tailWord_5450373
  simp only [CollatzResearch.WordTrace]
  refine ⟨198791434683236945444787773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132527623122157963629858515 198791434683236945444787773)
  ·
    refine ⟨74546788006213854541795415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198791434683236945444787773 74546788006213854541795415)
    ·
      refine ⟨111820182009320781812693123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74546788006213854541795415 111820182009320781812693123)
      ·
        refine ⟨167730273013981172719039685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111820182009320781812693123 167730273013981172719039685)
        ·
          refine ⟨31449426190121469884819941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167730273013981172719039685 31449426190121469884819941)
          ·
            refine ⟨5896767410647775603403739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31449426190121469884819941 5896767410647775603403739)
            ·
              refine ⟨8845151115971663405105609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5896767410647775603403739 8845151115971663405105609)
              ·
                refine ⟨6633863336978747553829207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8845151115971663405105609 6633863336978747553829207)
                ·
                  refine ⟨9950795005468121330743811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6633863336978747553829207 9950795005468121330743811)
                  ·
                    refine ⟨14926192508202181996115717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9950795005468121330743811 14926192508202181996115717)
                    ·
                      refine ⟨2798661095287909124271697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14926192508202181996115717 2798661095287909124271697)
                      ·
                        rfl

theorem cell23_5450373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_5450373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450373 prefixEnd_5450373 := by exact prefixLift 5450373
  have htrace : WordTrace (prefixWord ++ tailWord_5450373) baseStart_5450373 baseEnd_5450373 := by
    simpa [prefixWord, tailWord_5450373, baseEnd_5450373] using wordTrace_append hprefix tailTrace_5450373
  have hstable : (prefixWord ++ tailWord_5450373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450373).length < 2 ^ (prefixWord ++ tailWord_5450373).sum := by decide
  have hdescent : baseEnd_5450373 < baseStart_5450373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450386 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_5450386 : Nat := 118140960795 + 5450386 * 2 ^ 59
def prefixEnd_5450386 : Nat := 4983230072969 + 3 ^ 40 * 5450386 * 2
def baseEnd_5450386 : Nat := 2798667770536417573409137

theorem tailTrace_5450386 : CollatzResearch.WordTrace tailWord_5450386 prefixEnd_5450386 2798667770536417573409137 := by
  unfold tailWord_5450386
  simp only [CollatzResearch.WordTrace]
  refine ⟨49697977208047462166252753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132527939221459899110007341 49697977208047462166252753)
  ·
    refine ⟨37273482906035596624689565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49697977208047462166252753 37273482906035596624689565)
    ·
      refine ⟨13977556089763348734258587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37273482906035596624689565 13977556089763348734258587)
      ·
        refine ⟨20966334134645023101387881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13977556089763348734258587 20966334134645023101387881)
        ·
          refine ⟨15724750600983767326040911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20966334134645023101387881 15724750600983767326040911)
          ·
            refine ⟨23587125901475650989061367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15724750600983767326040911 23587125901475650989061367)
            ·
              refine ⟨35380688852213476483592051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23587125901475650989061367 35380688852213476483592051)
              ·
                refine ⟨53071033278320214725388077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35380688852213476483592051 53071033278320214725388077)
                ·
                  refine ⟨19901637479370080522020529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53071033278320214725388077 19901637479370080522020529)
                  ·
                    refine ⟨14926228109527560391515397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19901637479370080522020529 14926228109527560391515397)
                    ·
                      refine ⟨2798667770536417573409137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14926228109527560391515397 2798667770536417573409137)
                      ·
                        rfl

theorem cell23_5450386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_5450386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450386 prefixEnd_5450386 := by exact prefixLift 5450386
  have htrace : WordTrace (prefixWord ++ tailWord_5450386) baseStart_5450386 baseEnd_5450386 := by
    simpa [prefixWord, tailWord_5450386, baseEnd_5450386] using wordTrace_append hprefix tailTrace_5450386
  have hstable : (prefixWord ++ tailWord_5450386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450386).length < 2 ^ (prefixWord ++ tailWord_5450386).sum := by decide
  have hdescent : baseEnd_5450386 < baseStart_5450386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450393 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 1, 2, 3]
def baseStart_5450393 : Nat := 118140960795 + 5450393 * 2 ^ 59
def prefixEnd_5450393 : Nat := 4983230072969 + 3 ^ 40 * 5450393 * 2
def baseEnd_5450393 : Nat := 2798671364900999046021605

theorem tailTrace_5450393 : CollatzResearch.WordTrace tailWord_5450393 prefixEnd_5450393 2798671364900999046021605 := by
  unfold tailWord_5450393
  simp only [CollatzResearch.WordTrace]
  refine ⟨198792164143164488860515833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132528109428776325907010555 198792164143164488860515833)
  ·
    refine ⟨149094123107373366645386875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198792164143164488860515833 149094123107373366645386875)
    ·
      refine ⟨223641184661060049968080313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149094123107373366645386875 223641184661060049968080313)
      ·
        refine ⟨167730888495795037476060235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223641184661060049968080313 167730888495795037476060235)
        ·
          refine ⟨251596332743692556214090353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167730888495795037476060235 251596332743692556214090353)
          ·
            refine ⟨188697249557769417160567765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251596332743692556214090353 188697249557769417160567765)
            ·
              refine ⟨4422591786510220714700807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 188697249557769417160567765 4422591786510220714700807)
              ·
                refine ⟨6633887679765331072051211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4422591786510220714700807 6633887679765331072051211)
                ·
                  refine ⟨9950831519647996608076817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6633887679765331072051211 9950831519647996608076817)
                  ·
                    refine ⟨7463123639735997456057613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9950831519647996608076817 7463123639735997456057613)
                    ·
                      refine ⟨2798671364900999046021605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7463123639735997456057613 2798671364900999046021605)
                      ·
                        rfl

theorem cell23_5450393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_5450393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450393 prefixEnd_5450393 := by exact prefixLift 5450393
  have htrace : WordTrace (prefixWord ++ tailWord_5450393) baseStart_5450393 baseEnd_5450393 := by
    simpa [prefixWord, tailWord_5450393, baseEnd_5450393] using wordTrace_append hprefix tailTrace_5450393
  have hstable : (prefixWord ++ tailWord_5450393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450393).length < 2 ^ (prefixWord ++ tailWord_5450393).sum := by decide
  have hdescent : baseEnd_5450393 < baseStart_5450393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450423 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_5450423 : Nat := 118140960795 + 5450423 * 2 ^ 59
def prefixEnd_5450423 : Nat := 4983230072969 + 3 ^ 40 * 5450423 * 2
def baseEnd_5450423 : Nat := 2798686769320633928646467

theorem tailTrace_5450423 : CollatzResearch.WordTrace tailWord_5450423 prefixEnd_5450423 2798686769320633928646467 := by
  unfold tailWord_5450423
  simp only [CollatzResearch.WordTrace]
  refine ⟨198793258333055803984107923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132528838888703869322738615 198793258333055803984107923)
  ·
    refine ⟨298189887499583705976161885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198793258333055803984107923 298189887499583705976161885)
    ·
      refine ⟨111821207812343889741060707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298189887499583705976161885 111821207812343889741060707)
      ·
        refine ⟨167731811718515834611591061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111821207812343889741060707 167731811718515834611591061)
        ·
          refine ⟨7862428674305429747418331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 167731811718515834611591061 7862428674305429747418331)
          ·
            refine ⟨11793643011458144621127497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7862428674305429747418331 11793643011458144621127497)
            ·
              refine ⟨8845232258593608465845623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11793643011458144621127497 8845232258593608465845623)
              ·
                refine ⟨13267848387890412698768435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8845232258593608465845623 13267848387890412698768435)
                ·
                  refine ⟨19901772581835619048152653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13267848387890412698768435 19901772581835619048152653)
                  ·
                    refine ⟨7463164718188357143057245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19901772581835619048152653 7463164718188357143057245)
                    ·
                      refine ⟨2798686769320633928646467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7463164718188357143057245 2798686769320633928646467)
                      ·
                        rfl

theorem cell23_5450423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_5450423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450423 prefixEnd_5450423 := by exact prefixLift 5450423
  have htrace : WordTrace (prefixWord ++ tailWord_5450423) baseStart_5450423 baseEnd_5450423 := by
    simpa [prefixWord, tailWord_5450423, baseEnd_5450423] using wordTrace_append hprefix tailTrace_5450423
  have hstable : (prefixWord ++ tailWord_5450423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450423).length < 2 ^ (prefixWord ++ tailWord_5450423).sum := by decide
  have hdescent : baseEnd_5450423 < baseStart_5450423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450449 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_5450449 : Nat := 118140960795 + 5450449 * 2 ^ 59
def prefixEnd_5450449 : Nat := 4983230072969 + 3 ^ 40 * 5450449 * 2
def baseEnd_5450449 : Nat := 2798700119817650826921347

theorem tailTrace_5450449 : CollatzResearch.WordTrace tailWord_5450449 prefixEnd_5450449 2798700119817650826921347 := by
  unfold tailWord_5450449
  simp only [CollatzResearch.WordTrace]
  refine ⟨198794206630961610424554401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132529471087307740283036267 198794206630961610424554401)
  ·
    refine ⟨149095654973221207818415801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198794206630961610424554401 149095654973221207818415801)
    ·
      refine ⟨111821741229915905863811851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149095654973221207818415801 111821741229915905863811851)
      ·
        refine ⟨167732611844873858795717777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111821741229915905863811851 167732611844873858795717777)
        ·
          refine ⟨125799458883655394096788333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167732611844873858795717777 125799458883655394096788333)
          ·
            refine ⟨47174797081370772786295625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125799458883655394096788333 47174797081370772786295625)
            ·
              refine ⟨35381097811028079589721719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47174797081370772786295625 35381097811028079589721719)
              ·
                refine ⟨53071646716542119384582579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35381097811028079589721719 53071646716542119384582579)
                ·
                  refine ⟨79607470074813179076873869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53071646716542119384582579 79607470074813179076873869)
                  ·
                    refine ⟨29852801278054942153827701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79607470074813179076873869 29852801278054942153827701)
                    ·
                      refine ⟨2798700119817650826921347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29852801278054942153827701 2798700119817650826921347)
                      ·
                        rfl

theorem cell23_5450449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_5450449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450449 prefixEnd_5450449 := by exact prefixLift 5450449
  have htrace : WordTrace (prefixWord ++ tailWord_5450449) baseStart_5450449 baseEnd_5450449 := by
    simpa [prefixWord, tailWord_5450449, baseEnd_5450449] using wordTrace_append hprefix tailTrace_5450449
  have hstable : (prefixWord ++ tailWord_5450449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450449).length < 2 ^ (prefixWord ++ tailWord_5450449).sum := by decide
  have hdescent : baseEnd_5450449 < baseStart_5450449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450486 : List Nat := [5, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_5450486 : Nat := 118140960795 + 5450486 * 2 ^ 59
def prefixEnd_5450486 : Nat := 4983230072969 + 3 ^ 40 * 5450486 * 2
def baseEnd_5450486 : Nat := 310968790955763020239853

theorem tailTrace_5450486 : CollatzResearch.WordTrace tailWord_5450486 prefixEnd_5450486 310968790955763020239853 := by
  unfold tailWord_5450486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12424722258239222858978207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132530370754551710495767541 12424722258239222858978207)
  ·
    refine ⟨18637083387358834288467311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12424722258239222858978207 18637083387358834288467311)
    ·
      refine ⟨27955625081038251432700967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18637083387358834288467311 27955625081038251432700967)
      ·
        refine ⟨41933437621557377149051451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27955625081038251432700967 41933437621557377149051451)
        ·
          refine ⟨62900156432336065723577177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41933437621557377149051451 62900156432336065723577177)
          ·
            refine ⟨47175117324252049292682883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62900156432336065723577177 47175117324252049292682883)
            ·
              refine ⟨70762675986378073939024325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47175117324252049292682883 70762675986378073939024325)
              ·
                refine ⟨13268001747445888863567061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70762675986378073939024325 13268001747445888863567061)
                ·
                  refine ⟨310968790955763020239853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13268001747445888863567061 310968790955763020239853)
                  ·
                    rfl

theorem cell23_5450486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_5450486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450486 prefixEnd_5450486 := by exact prefixLift 5450486
  have htrace : WordTrace (prefixWord ++ tailWord_5450486) baseStart_5450486 baseEnd_5450486 := by
    simpa [prefixWord, tailWord_5450486, baseEnd_5450486] using wordTrace_append hprefix tailTrace_5450486
  have hstable : (prefixWord ++ tailWord_5450486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450486).length < 2 ^ (prefixWord ++ tailWord_5450486).sum := by decide
  have hdescent : baseEnd_5450486 < baseStart_5450486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450576 : List Nat := [2, 1, 1, 1, 1, 4, 3, 4, 6]
def baseStart_5450576 : Nat := 118140960795 + 5450576 * 2 ^ 59
def prefixEnd_5450576 : Nat := 4983230072969 + 3 ^ 40 * 5450576 * 2
def baseEnd_5450576 : Nat := 310973925762307981114807

theorem tailTrace_5450576 : CollatzResearch.WordTrace tailWord_5450576 prefixEnd_5450576 310973925762307981114807 := by
  unfold tailWord_5450576
  simp only [CollatzResearch.WordTrace]
  refine ⟨99399419350750755557213791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132532559134334340742951721 99399419350750755557213791)
  ·
    refine ⟨149099129026126133335820687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99399419350750755557213791 149099129026126133335820687)
    ·
      refine ⟨223648693539189200003731031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149099129026126133335820687 223648693539189200003731031)
      ·
        refine ⟨335473040308783800005596547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223648693539189200003731031 335473040308783800005596547)
        ·
          refine ⟨503209560463175700008394821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335473040308783800005596547 503209560463175700008394821)
          ·
            refine ⟨94351792586845443751574029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 503209560463175700008394821 94351792586845443751574029)
            ·
              refine ⟨35381922220067041406840261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94351792586845443751574029 35381922220067041406840261)
              ·
                refine ⟨6634110416262570263782549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35381922220067041406840261 6634110416262570263782549)
                ·
                  refine ⟨310973925762307981114807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6634110416262570263782549 310973925762307981114807)
                  ·
                    rfl

theorem cell23_5450576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 6].length) (baseStart_5450576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450576 prefixEnd_5450576 := by exact prefixLift 5450576
  have htrace : WordTrace (prefixWord ++ tailWord_5450576) baseStart_5450576 baseEnd_5450576 := by
    simpa [prefixWord, tailWord_5450576, baseEnd_5450576] using wordTrace_append hprefix tailTrace_5450576
  have hstable : (prefixWord ++ tailWord_5450576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450576).length < 2 ^ (prefixWord ++ tailWord_5450576).sum := by decide
  have hdescent : baseEnd_5450576 < baseStart_5450576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450603 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 3]
def baseStart_5450603 : Nat := 118140960795 + 5450603 * 2 ^ 59
def prefixEnd_5450603 : Nat := 4983230072969 + 3 ^ 40 * 5450603 * 2
def baseEnd_5450603 : Nat := 2798779195838443224395639

theorem tailTrace_5450603 : CollatzResearch.WordTrace tailWord_5450603 prefixEnd_5450603 2798779195838443224395639 := by
  unfold tailWord_5450603
  simp only [CollatzResearch.WordTrace]
  refine ⟨198799823472403694725660463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132533215648269129817106975 198799823472403694725660463)
  ·
    refine ⟨298199735208605542088490695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198799823472403694725660463 298199735208605542088490695)
    ·
      refine ⟨447299602812908313132736043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298199735208605542088490695 447299602812908313132736043)
      ·
        refine ⟨670949404219362469699104065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447299602812908313132736043 670949404219362469699104065)
        ·
          refine ⟨503212053164521852274328049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 670949404219362469699104065 503212053164521852274328049)
          ·
            refine ⟨377409039873391389205746037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503212053164521852274328049 377409039873391389205746037)
            ·
              refine ⟨35382097488130442738038691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 377409039873391389205746037 35382097488130442738038691)
              ·
                refine ⟨53073146232195664107058037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35382097488130442738038691 53073146232195664107058037)
                ·
                  refine ⟨4975607459268343510036691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53073146232195664107058037 4975607459268343510036691)
                  ·
                    refine ⟨7463411188902515265055037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4975607459268343510036691 7463411188902515265055037)
                    ·
                      refine ⟨2798779195838443224395639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7463411188902515265055037 2798779195838443224395639)
                      ·
                        rfl

theorem cell23_5450603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 1, 3].length) (baseStart_5450603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450603 prefixEnd_5450603 := by exact prefixLift 5450603
  have htrace : WordTrace (prefixWord ++ tailWord_5450603) baseStart_5450603 baseEnd_5450603 := by
    simpa [prefixWord, tailWord_5450603, baseEnd_5450603] using wordTrace_append hprefix tailTrace_5450603
  have hstable : (prefixWord ++ tailWord_5450603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450603).length < 2 ^ (prefixWord ++ tailWord_5450603).sum := by decide
  have hdescent : baseEnd_5450603 < baseStart_5450603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450614 : List Nat := [5, 1, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_5450614 : Nat := 118140960795 + 5450614 * 2 ^ 59
def prefixEnd_5450614 : Nat := 4983230072969 + 3 ^ 40 * 5450614 * 2
def baseEnd_5450614 : Nat := 932928281375214227119363

theorem tailTrace_5450614 : CollatzResearch.WordTrace tailWord_5450614 prefixEnd_5450614 932928281375214227119363 := by
  unfold tailWord_5450614
  simp only [CollatzResearch.WordTrace]
  refine ⟨12425014042210240225269431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132533483116909229069540597 12425014042210240225269431)
  ·
    refine ⟨18637521063315360337904147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12425014042210240225269431 18637521063315360337904147)
    ·
      refine ⟨27956281594973040506856221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18637521063315360337904147 27956281594973040506856221)
      ·
        refine ⟨10483605598114890190071083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27956281594973040506856221 10483605598114890190071083)
        ·
          refine ⟨15725408397172335285106625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10483605598114890190071083 15725408397172335285106625)
          ·
            refine ⟨11794056297879251463829969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15725408397172335285106625 11794056297879251463829969)
            ·
              refine ⟨8845542223409438597872477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11794056297879251463829969 8845542223409438597872477)
              ·
                refine ⟨3317078333778539474202179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8845542223409438597872477 3317078333778539474202179)
                ·
                  refine ⟨4975617500667809211303269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317078333778539474202179 4975617500667809211303269)
                  ·
                    refine ⟨932928281375214227119363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4975617500667809211303269 932928281375214227119363)
                    ·
                      rfl

theorem cell23_5450614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_5450614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450614 prefixEnd_5450614 := by exact prefixLift 5450614
  have htrace : WordTrace (prefixWord ++ tailWord_5450614) baseStart_5450614 baseEnd_5450614 := by
    simpa [prefixWord, tailWord_5450614, baseEnd_5450614] using wordTrace_append hprefix tailTrace_5450614
  have hstable : (prefixWord ++ tailWord_5450614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450614).length < 2 ^ (prefixWord ++ tailWord_5450614).sum := by decide
  have hdescent : baseEnd_5450614 < baseStart_5450614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450636 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_5450636 : Nat := 118140960795 + 5450636 * 2 ^ 59
def prefixEnd_5450636 : Nat := 4983230072969 + 3 ^ 40 * 5450636 * 2
def baseEnd_5450636 : Nat := 932932046900013865094329

theorem tailTrace_5450636 : CollatzResearch.WordTrace tailWord_5450636 prefixEnd_5450636 932932046900013865094329 := by
  unfold tailWord_5450636
  simp only [CollatzResearch.WordTrace]
  refine ⟨99400513540642070680805881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132534018054189427574407841 99400513540642070680805881)
  ·
    refine ⟨74550385155481553010604411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99400513540642070680805881 74550385155481553010604411)
    ·
      refine ⟨111825577733222329515906617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74550385155481553010604411 111825577733222329515906617)
      ·
        refine ⟨83869183299916747136929963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111825577733222329515906617 83869183299916747136929963)
        ·
          refine ⟨125803774949875120705394945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83869183299916747136929963 125803774949875120705394945)
          ·
            refine ⟨94352831212406340529046209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125803774949875120705394945 94352831212406340529046209)
            ·
              refine ⟨70764623409304755396784657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94352831212406340529046209 70764623409304755396784657)
              ·
                refine ⟨53073467556978566547588493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70764623409304755396784657 53073467556978566547588493)
                ·
                  refine ⟨19902550333866962455345685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53073467556978566547588493 19902550333866962455345685)
                  ·
                    refine ⟨932932046900013865094329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19902550333866962455345685 932932046900013865094329)
                    ·
                      rfl

theorem cell23_5450636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_5450636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450636 prefixEnd_5450636 := by exact prefixLift 5450636
  have htrace : WordTrace (prefixWord ++ tailWord_5450636) baseStart_5450636 baseEnd_5450636 := by
    simpa [prefixWord, tailWord_5450636, baseEnd_5450636] using wordTrace_append hprefix tailTrace_5450636
  have hstable : (prefixWord ++ tailWord_5450636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450636).length < 2 ^ (prefixWord ++ tailWord_5450636).sum := by decide
  have hdescent : baseEnd_5450636 < baseStart_5450636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450660 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_5450660 : Nat := 118140960795 + 5450660 * 2 ^ 59
def prefixEnd_5450660 : Nat := 4983230072969 + 3 ^ 40 * 5450660 * 2
def baseEnd_5450660 : Nat := 2798808464235749501382877

theorem tailTrace_5450660 : CollatzResearch.WordTrace tailWord_5450660 prefixEnd_5450660 2798808464235749501382877 := by
  unfold tailWord_5450660
  simp only [CollatzResearch.WordTrace]
  refine ⟨99400951216598596730242717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132534601622131462306990289 99400951216598596730242717)
  ·
    refine ⟨37275356706224473773841019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99400951216598596730242717 37275356706224473773841019)
    ·
      refine ⟨55913035059336710660761529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37275356706224473773841019 55913035059336710660761529)
      ·
        refine ⟨41934776294502532995571147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55913035059336710660761529 41934776294502532995571147)
        ·
          refine ⟨62902164441753799493356721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41934776294502532995571147 62902164441753799493356721)
          ·
            refine ⟨47176623331315349620017541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62902164441753799493356721 47176623331315349620017541)
            ·
              refine ⟨8845616874621628053753289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47176623331315349620017541 8845616874621628053753289)
              ·
                refine ⟨6634212655966221040314967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8845616874621628053753289 6634212655966221040314967)
                ·
                  refine ⟨9951318983949331560472451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6634212655966221040314967 9951318983949331560472451)
                  ·
                    refine ⟨14926978475923997340708677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9951318983949331560472451 14926978475923997340708677)
                    ·
                      refine ⟨2798808464235749501382877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14926978475923997340708677 2798808464235749501382877)
                      ·
                        rfl

theorem cell23_5450660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_5450660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450660 prefixEnd_5450660 := by exact prefixLift 5450660
  have htrace : WordTrace (prefixWord ++ tailWord_5450660) baseStart_5450660 baseEnd_5450660 := by
    simpa [prefixWord, tailWord_5450660, baseEnd_5450660] using wordTrace_append hprefix tailTrace_5450660
  have hstable : (prefixWord ++ tailWord_5450660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450660).length < 2 ^ (prefixWord ++ tailWord_5450660).sum := by decide
  have hdescent : baseEnd_5450660 < baseStart_5450660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450680 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 1, 2, 3]
def baseStart_5450680 : Nat := 118140960795 + 5450680 * 2 ^ 59
def prefixEnd_5450680 : Nat := 4983230072969 + 3 ^ 40 * 5450680 * 2
def baseEnd_5450680 : Nat := 2798818733848839423132785

theorem tailTrace_5450680 : CollatzResearch.WordTrace tailWord_5450680 prefixEnd_5450680 2798818733848839423132785 := by
  unfold tailWord_5450680
  simp only [CollatzResearch.WordTrace]
  refine ⟨99401315946562368438106747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132535087928749824584142329 99401315946562368438106747)
  ·
    refine ⟨149101973919843552657160121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99401315946562368438106747 149101973919843552657160121)
    ·
      refine ⟨111826480439882664492870091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149101973919843552657160121 111826480439882664492870091)
      ·
        refine ⟨167739720659823996739305137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111826480439882664492870091 167739720659823996739305137)
        ·
          refine ⟨125804790494867997554478853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167739720659823996739305137 125804790494867997554478853)
          ·
            refine ⟨23588398217787749541464785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125804790494867997554478853 23588398217787749541464785)
            ·
              refine ⟨17691298663340812156098589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23588398217787749541464785 17691298663340812156098589)
              ·
                refine ⟨6634236998752804558536971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17691298663340812156098589 6634236998752804558536971)
                ·
                  refine ⟨9951355498129206837805457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6634236998752804558536971 9951355498129206837805457)
                  ·
                    refine ⟨7463516623596905128354093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9951355498129206837805457 7463516623596905128354093)
                    ·
                      refine ⟨2798818733848839423132785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7463516623596905128354093 2798818733848839423132785)
                      ·
                        rfl

theorem cell23_5450680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_5450680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450680 prefixEnd_5450680 := by exact prefixLift 5450680
  have htrace : WordTrace (prefixWord ++ tailWord_5450680) baseStart_5450680 baseEnd_5450680 := by
    simpa [prefixWord, tailWord_5450680, baseEnd_5450680] using wordTrace_append hprefix tailTrace_5450680
  have hstable : (prefixWord ++ tailWord_5450680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450680).length < 2 ^ (prefixWord ++ tailWord_5450680).sum := by decide
  have hdescent : baseEnd_5450680 < baseStart_5450680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450763 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 4]
def baseStart_5450763 : Nat := 118140960795 + 5450763 * 2 ^ 59
def prefixEnd_5450763 : Nat := 4983230072969 + 3 ^ 40 * 5450763 * 2
def baseEnd_5450763 : Nat := 2798861352743162598394903

theorem tailTrace_5450763 : CollatzResearch.WordTrace tailWord_5450763 prefixEnd_5450763 2798861352743162598394903 := by
  unfold tailWord_5450763
  simp only [CollatzResearch.WordTrace]
  refine ⟨198805659151824042051484943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132537106101216028034323295 198805659151824042051484943)
  ·
    refine ⟨298208488727736063077227415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198805659151824042051484943 298208488727736063077227415)
    ·
      refine ⟨447312733091604094615841123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298208488727736063077227415 447312733091604094615841123)
      ·
        refine ⟨670969099637406141923761685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447312733091604094615841123 670969099637406141923761685)
        ·
          refine ⟨31451676545503412902676329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 670969099637406141923761685 31451676545503412902676329)
          ·
            refine ⟨23588757409127559677007247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31451676545503412902676329 23588757409127559677007247)
            ·
              refine ⟨35383136113691339515510871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23588757409127559677007247 35383136113691339515510871)
              ·
                refine ⟨53074704170537009273266307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35383136113691339515510871 53074704170537009273266307)
                ·
                  refine ⟨79612056255805513909899461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53074704170537009273266307 79612056255805513909899461)
                  ·
                    refine ⟨14927260547963533858106149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79612056255805513909899461 14927260547963533858106149)
                    ·
                      refine ⟨2798861352743162598394903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14927260547963533858106149 2798861352743162598394903)
                      ·
                        rfl

theorem cell23_5450763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 4].length) (baseStart_5450763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450763 prefixEnd_5450763 := by exact prefixLift 5450763
  have htrace : WordTrace (prefixWord ++ tailWord_5450763) baseStart_5450763 baseEnd_5450763 := by
    simpa [prefixWord, tailWord_5450763, baseEnd_5450763] using wordTrace_append hprefix tailTrace_5450763
  have hstable : (prefixWord ++ tailWord_5450763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450763).length < 2 ^ (prefixWord ++ tailWord_5450763).sum := by decide
  have hdescent : baseEnd_5450763 < baseStart_5450763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450773 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 9]
def baseStart_5450773 : Nat := 118140960795 + 5450773 * 2 ^ 59
def prefixEnd_5450773 : Nat := 4983230072969 + 3 ^ 40 * 5450773 * 2
def baseEnd_5450773 : Nat := 310985165283300839918873

theorem tailTrace_5450773 : CollatzResearch.WordTrace tailWord_5450773 prefixEnd_5450773 310985165283300839918873 := by
  unfold tailWord_5450773
  simp only [CollatzResearch.WordTrace]
  refine ⟨198806023881787813759348973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132537349254525209172899315 198806023881787813759348973)
  ·
    refine ⟨74552258955670430159755865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198806023881787813759348973 74552258955670430159755865)
    ·
      refine ⟨55914194216752822619816899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74552258955670430159755865 55914194216752822619816899)
      ·
        refine ⟨83871291325129233929725349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55914194216752822619816899 83871291325129233929725349)
        ·
          refine ⟨15725867123461731361823503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83871291325129233929725349 15725867123461731361823503)
          ·
            refine ⟨23588800685192597042735255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15725867123461731361823503 23588800685192597042735255)
            ·
              refine ⟨35383201027788895564102883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23588800685192597042735255 35383201027788895564102883)
              ·
                refine ⟨53074801541683343346154325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35383201027788895564102883 53074801541683343346154325)
                ·
                  refine ⟨310985165283300839918873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53074801541683343346154325 310985165283300839918873)
                  ·
                    rfl

theorem cell23_5450773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_5450773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450773 prefixEnd_5450773 := by exact prefixLift 5450773
  have htrace : WordTrace (prefixWord ++ tailWord_5450773) baseStart_5450773 baseEnd_5450773 := by
    simpa [prefixWord, tailWord_5450773, baseEnd_5450773] using wordTrace_append hprefix tailTrace_5450773
  have hstable : (prefixWord ++ tailWord_5450773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450773).length < 2 ^ (prefixWord ++ tailWord_5450773).sum := by decide
  have hdescent : baseEnd_5450773 < baseStart_5450773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450803 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 4, 5]
def baseStart_5450803 : Nat := 118140960795 + 5450803 * 2 ^ 59
def prefixEnd_5450803 : Nat := 4983230072969 + 3 ^ 40 * 5450803 * 2
def baseEnd_5450803 : Nat := 932960630656447480631573

theorem tailTrace_5450803 : CollatzResearch.WordTrace tailWord_5450803 prefixEnd_5450803 932960630656447480631573 := by
  unfold tailWord_5450803
  simp only [CollatzResearch.WordTrace]
  refine ⟨198807118071679128882941063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132538078714452752588627375 198807118071679128882941063)
  ·
    refine ⟨298210677107518693324411595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198807118071679128882941063 298210677107518693324411595)
    ·
      refine ⟨447316015661278039986617393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298210677107518693324411595 447316015661278039986617393)
      ·
        refine ⟨335487011745958529989963045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447316015661278039986617393 335487011745958529989963045)
        ·
          refine ⟨62903814702367224373118071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335487011745958529989963045 62903814702367224373118071)
          ·
            refine ⟨94355722053550836559677107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62903814702367224373118071 94355722053550836559677107)
            ·
              refine ⟨141533583080326254839515661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94355722053550836559677107 141533583080326254839515661)
              ·
                refine ⟨53075093655122345564818373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141533583080326254839515661 53075093655122345564818373)
                ·
                  refine ⟨9951580060335439793403445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53075093655122345564818373 9951580060335439793403445)
                  ·
                    refine ⟨932960630656447480631573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9951580060335439793403445 932960630656447480631573)
                    ·
                      rfl

theorem cell23_5450803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 5].length) (baseStart_5450803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450803 prefixEnd_5450803 := by exact prefixLift 5450803
  have htrace : WordTrace (prefixWord ++ tailWord_5450803) baseStart_5450803 baseEnd_5450803 := by
    simpa [prefixWord, tailWord_5450803, baseEnd_5450803] using wordTrace_append hprefix tailTrace_5450803
  have hstable : (prefixWord ++ tailWord_5450803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450803).length < 2 ^ (prefixWord ++ tailWord_5450803).sum := by decide
  have hdescent : baseEnd_5450803 < baseStart_5450803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450810 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2]
def baseStart_5450810 : Nat := 118140960795 + 5450810 * 2 ^ 59
def prefixEnd_5450810 : Nat := 4983230072969 + 3 ^ 40 * 5450810 * 2
def baseEnd_5450810 : Nat := 2798885486333923914507187

theorem tailTrace_5450810 : CollatzResearch.WordTrace tailWord_5450810 prefixEnd_5450810 2798885486333923914507187 := by
  unfold tailWord_5450810
  simp only [CollatzResearch.WordTrace]
  refine ⟨49701843345663442269611471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132538248921769179385630589 49701843345663442269611471)
  ·
    refine ⟨74552765018495163404417207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49701843345663442269611471 74552765018495163404417207)
    ·
      refine ⟨111829147527742745106625811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74552765018495163404417207 111829147527742745106625811)
      ·
        refine ⟨167743721291614117659938717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111829147527742745106625811 167743721291614117659938717)
        ·
          refine ⟨62903895484355294122477019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167743721291614117659938717 62903895484355294122477019)
          ·
            refine ⟨94355843226532941183715529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62903895484355294122477019 94355843226532941183715529)
            ·
              refine ⟨70766882419899705887786647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94355843226532941183715529 70766882419899705887786647)
              ·
                refine ⟨106150323629849558831679971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70766882419899705887786647 106150323629849558831679971)
                ·
                  refine ⟨159225485444774338247519957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106150323629849558831679971 159225485444774338247519957)
                  ·
                    refine ⟨3731847315111898552676249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 159225485444774338247519957 3731847315111898552676249)
                    ·
                      refine ⟨2798885486333923914507187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3731847315111898552676249 2798885486333923914507187)
                      ·
                        rfl

theorem cell23_5450810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_5450810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450810 prefixEnd_5450810 := by exact prefixLift 5450810
  have htrace : WordTrace (prefixWord ++ tailWord_5450810) baseStart_5450810 baseEnd_5450810 := by
    simpa [prefixWord, tailWord_5450810, baseEnd_5450810] using wordTrace_append hprefix tailTrace_5450810
  have hstable : (prefixWord ++ tailWord_5450810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450810).length < 2 ^ (prefixWord ++ tailWord_5450810).sum := by decide
  have hdescent : baseEnd_5450810 < baseStart_5450810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450840 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_5450840 : Nat := 118140960795 + 5450840 * 2 ^ 59
def prefixEnd_5450840 : Nat := 4983230072969 + 3 ^ 40 * 5450840 * 2
def baseEnd_5450840 : Nat := 2798900890753558797132049

theorem tailTrace_5450840 : CollatzResearch.WordTrace tailWord_5450840 prefixEnd_5450840 2798900890753558797132049 := by
  unfold tailWord_5450840
  simp only [CollatzResearch.WordTrace]
  refine ⟨99404233786272542101018987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132538978381696722801358649 99404233786272542101018987)
  ·
    refine ⟨149106350679408813151528481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99404233786272542101018987 149106350679408813151528481)
    ·
      refine ⟨111829763009556609863646361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149106350679408813151528481 111829763009556609863646361)
      ·
        refine ⟨83872322257167457397734771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111829763009556609863646361 83872322257167457397734771)
        ·
          refine ⟨125808483385751186096602157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83872322257167457397734771 125808483385751186096602157)
          ·
            refine ⟨47178181269656694786225809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125808483385751186096602157 47178181269656694786225809)
            ·
              refine ⟨35383635952242521089669357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47178181269656694786225809 35383635952242521089669357)
              ·
                refine ⟨13268863482090945408626009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35383635952242521089669357 13268863482090945408626009)
                ·
                  refine ⟨9951647611568209056469507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13268863482090945408626009 9951647611568209056469507)
                  ·
                    refine ⟨14927471417352313584704261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9951647611568209056469507 14927471417352313584704261)
                    ·
                      refine ⟨2798900890753558797132049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14927471417352313584704261 2798900890753558797132049)
                      ·
                        rfl

theorem cell23_5450840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_5450840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450840 prefixEnd_5450840 := by exact prefixLift 5450840
  have htrace : WordTrace (prefixWord ++ tailWord_5450840) baseStart_5450840 baseEnd_5450840 := by
    simpa [prefixWord, tailWord_5450840, baseEnd_5450840] using wordTrace_append hprefix tailTrace_5450840
  have hstable : (prefixWord ++ tailWord_5450840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450840).length < 2 ^ (prefixWord ++ tailWord_5450840).sum := by decide
  have hdescent : baseEnd_5450840 < baseStart_5450840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450863 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 8]
def baseStart_5450863 : Nat := 118140960795 + 5450863 * 2 ^ 59
def prefixEnd_5450863 : Nat := 4983230072969 + 3 ^ 40 * 5450863 * 2
def baseEnd_5450863 : Nat := 310990300089845800793827

theorem tailTrace_5450863 : CollatzResearch.WordTrace tailWord_5450863 prefixEnd_5450863 310990300089845800793827 := by
  unfold tailWord_5450863
  simp only [CollatzResearch.WordTrace]
  refine ⟨198809306451461759130125243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132539537634307839420083495 198809306451461759130125243)
  ·
    refine ⟨298213959677192638695187865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198809306451461759130125243 298213959677192638695187865)
    ·
      refine ⟨223660469757894479021390899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298213959677192638695187865 223660469757894479021390899)
      ·
        refine ⟨335490704636841718532086349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223660469757894479021390899 335490704636841718532086349)
        ·
          refine ⟨125809014238815644449532381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335490704636841718532086349 125809014238815644449532381)
          ·
            refine ⟨47178380339555866668574643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125809014238815644449532381 47178380339555866668574643)
            ·
              refine ⟨70767570509333800002861965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47178380339555866668574643 70767570509333800002861965)
              ·
                refine ⟨26537838941000175001073237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70767570509333800002861965 26537838941000175001073237)
                ·
                  refine ⟨310990300089845800793827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26537838941000175001073237 310990300089845800793827)
                  ·
                    rfl

theorem cell23_5450863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 8].length) (baseStart_5450863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450863 prefixEnd_5450863 := by exact prefixLift 5450863
  have htrace : WordTrace (prefixWord ++ tailWord_5450863) baseStart_5450863 baseEnd_5450863 := by
    simpa [prefixWord, tailWord_5450863, baseEnd_5450863] using wordTrace_append hprefix tailTrace_5450863
  have hstable : (prefixWord ++ tailWord_5450863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450863).length < 2 ^ (prefixWord ++ tailWord_5450863).sum := by decide
  have hdescent : baseEnd_5450863 < baseStart_5450863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450894 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_5450894 : Nat := 118140960795 + 5450894 * 2 ^ 59
def prefixEnd_5450894 : Nat := 4983230072969 + 3 ^ 40 * 5450894 * 2
def baseEnd_5450894 : Nat := 2798928618708901585856801

theorem tailTrace_5450894 : CollatzResearch.WordTrace tailWord_5450894 prefixEnd_5450894 2798928618708901585856801 := by
  unfold tailWord_5450894
  simp only [CollatzResearch.WordTrace]
  refine ⟨24851304639293681428062967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132540291409566300949669157 24851304639293681428062967)
  ·
    refine ⟨37276956958940522142094451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24851304639293681428062967 37276956958940522142094451)
    ·
      refine ⟨55915435438410783213141677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37276956958940522142094451 55915435438410783213141677)
      ·
        refine ⟨20968288289404043704928129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55915435438410783213141677 20968288289404043704928129)
        ·
          refine ⟨15726216217053032778696097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20968288289404043704928129 15726216217053032778696097)
          ·
            refine ⟨11794662162789774584022073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15726216217053032778696097 11794662162789774584022073)
            ·
              refine ⟨8845996622092330938016555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11794662162789774584022073 8845996622092330938016555)
              ·
                refine ⟨13268994933138496407024833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8845996622092330938016555 13268994933138496407024833)
                ·
                  refine ⟨9951746199853872305268625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13268994933138496407024833 9951746199853872305268625)
                  ·
                    refine ⟨7463809649890404228951469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9951746199853872305268625 7463809649890404228951469)
                    ·
                      refine ⟨2798928618708901585856801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7463809649890404228951469 2798928618708901585856801)
                      ·
                        rfl

theorem cell23_5450894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_5450894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450894 prefixEnd_5450894 := by exact prefixLift 5450894
  have htrace : WordTrace (prefixWord ++ tailWord_5450894) baseStart_5450894 baseEnd_5450894 := by
    simpa [prefixWord, tailWord_5450894, baseEnd_5450894] using wordTrace_append hprefix tailTrace_5450894
  have hstable : (prefixWord ++ tailWord_5450894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450894).length < 2 ^ (prefixWord ++ tailWord_5450894).sum := by decide
  have hdescent : baseEnd_5450894 < baseStart_5450894 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450914 : List Nat := [3, 3, 1, 3, 2, 1, 2, 2, 6]
def baseStart_5450914 : Nat := 118140960795 + 5450914 * 2 ^ 59
def prefixEnd_5450914 : Nat := 4983230072969 + 3 ^ 40 * 5450914 * 2
def baseEnd_5450914 : Nat := 310993209813554611956301

theorem tailTrace_5450914 : CollatzResearch.WordTrace tailWord_5450914 prefixEnd_5450914 310993209813554611956301 := by
  unfold tailWord_5450914
  simp only [CollatzResearch.WordTrace]
  refine ⟨49702791643569248710057949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132540777716184663226821197 49702791643569248710057949)
  ·
    refine ⟨18638546866338468266271731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49702791643569248710057949 18638546866338468266271731)
    ·
      refine ⟨27957820299507702399407597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18638546866338468266271731 27957820299507702399407597)
      ·
        refine ⟨10484182612315388399777849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27957820299507702399407597 10484182612315388399777849)
        ·
          refine ⟨7863136959236541299833387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10484182612315388399777849 7863136959236541299833387)
          ·
            refine ⟨11794705438854811949750081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7863136959236541299833387 11794705438854811949750081)
            ·
              refine ⟨8846029079141108962312561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11794705438854811949750081 8846029079141108962312561)
              ·
                refine ⟨6634521809355831721734421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8846029079141108962312561 6634521809355831721734421)
                ·
                  refine ⟨310993209813554611956301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6634521809355831721734421 310993209813554611956301)
                  ·
                    rfl

theorem cell23_5450914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_5450914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450914 prefixEnd_5450914 := by exact prefixLift 5450914
  have htrace : WordTrace (prefixWord ++ tailWord_5450914) baseStart_5450914 baseEnd_5450914 := by
    simpa [prefixWord, tailWord_5450914, baseEnd_5450914] using wordTrace_append hprefix tailTrace_5450914
  have hstable : (prefixWord ++ tailWord_5450914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450914).length < 2 ^ (prefixWord ++ tailWord_5450914).sum := by decide
  have hdescent : baseEnd_5450914 < baseStart_5450914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450958 : List Nat := [4, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3]
def baseStart_5450958 : Nat := 118140960795 + 5450958 * 2 ^ 59
def prefixEnd_5450958 : Nat := 4983230072969 + 3 ^ 40 * 5450958 * 2
def baseEnd_5450958 : Nat := 2798961481470789335456507

theorem tailTrace_5450958 : CollatzResearch.WordTrace tailWord_5450958 prefixEnd_5450958 2798961481470789335456507 := by
  unfold tailWord_5450958
  simp only [CollatzResearch.WordTrace]
  refine ⟨24851596423264698794354191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132541847590745060236555685 24851596423264698794354191)
  ·
    refine ⟨37277394634897048191531287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24851596423264698794354191 37277394634897048191531287)
    ·
      refine ⟨55916091952345572287296931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37277394634897048191531287 55916091952345572287296931)
      ·
        refine ⟨83874137928518358430945397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55916091952345572287296931 83874137928518358430945397)
        ·
          refine ⟨7863200430798596102901131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83874137928518358430945397 7863200430798596102901131)
          ·
            refine ⟨11794800646197894154351697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7863200430798596102901131 11794800646197894154351697)
            ·
              refine ⟨8846100484648420615763773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11794800646197894154351697 8846100484648420615763773)
              ·
                refine ⟨3317287681743157730911415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8846100484648420615763773 3317287681743157730911415)
                ·
                  refine ⟨4975931522614736596367123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317287681743157730911415 4975931522614736596367123)
                  ·
                    refine ⟨7463897283922104894550685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4975931522614736596367123 7463897283922104894550685)
                    ·
                      refine ⟨2798961481470789335456507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7463897283922104894550685 2798961481470789335456507)
                      ·
                        rfl

theorem cell23_5450958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3].length) (baseStart_5450958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450958 prefixEnd_5450958 := by exact prefixLift 5450958
  have htrace : WordTrace (prefixWord ++ tailWord_5450958) baseStart_5450958 baseEnd_5450958 := by
    simpa [prefixWord, tailWord_5450958, baseEnd_5450958] using wordTrace_append hprefix tailTrace_5450958
  have hstable : (prefixWord ++ tailWord_5450958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450958).length < 2 ^ (prefixWord ++ tailWord_5450958).sum := by decide
  have hdescent : baseEnd_5450958 < baseStart_5450958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5450991 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 2, 4]
def baseStart_5450991 : Nat := 118140960795 + 5450991 * 2 ^ 59
def prefixEnd_5450991 : Nat := 4983230072969 + 3 ^ 40 * 5450991 * 2
def baseEnd_5450991 : Nat := 932992808777462568781285

theorem tailTrace_5450991 : CollatzResearch.WordTrace tailWord_5450991 prefixEnd_5450991 932992808777462568781285 := by
  unfold tailWord_5450991
  simp only [CollatzResearch.WordTrace]
  refine ⟨198813974994998036990784827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132542649996665357993856551 198813974994998036990784827)
  ·
    refine ⟨298220962492497055486177241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198813974994998036990784827 298220962492497055486177241)
    ·
      refine ⟨223665721869372791614632931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298220962492497055486177241 223665721869372791614632931)
      ·
        refine ⟨335498582804059187421949397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223665721869372791614632931 335498582804059187421949397)
        ·
          refine ⟨7863248034470137205201939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 335498582804059187421949397 7863248034470137205201939)
          ·
            refine ⟨11794872051705205807802909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7863248034470137205201939 11794872051705205807802909)
            ·
              refine ⟨4423077019389452177926091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11794872051705205807802909 4423077019389452177926091)
              ·
                refine ⟨6634615529084178266889137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423077019389452177926091 6634615529084178266889137)
                ·
                  refine ⟨4975961646813133700166853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6634615529084178266889137 4975961646813133700166853)
                  ·
                    refine ⟨932992808777462568781285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4975961646813133700166853 932992808777462568781285)
                    ·
                      rfl

theorem cell23_5450991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 4].length) (baseStart_5450991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5450991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5450991 prefixEnd_5450991 := by exact prefixLift 5450991
  have htrace : WordTrace (prefixWord ++ tailWord_5450991) baseStart_5450991 baseEnd_5450991 := by
    simpa [prefixWord, tailWord_5450991, baseEnd_5450991] using wordTrace_append hprefix tailTrace_5450991
  have hstable : (prefixWord ++ tailWord_5450991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5450991).length < 2 ^ (prefixWord ++ tailWord_5450991).sum := by decide
  have hdescent : baseEnd_5450991 < baseStart_5450991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5450991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451004 : List Nat := [2, 2, 2, 1, 5, 2, 2, 7]
def baseStart_5451004 : Nat := 118140960795 + 5451004 * 2 ^ 59
def prefixEnd_5451004 : Nat := 4983230072969 + 3 ^ 40 * 5451004 * 2
def baseEnd_5451004 : Nat := 103666114873366524277085

theorem tailTrace_5451004 : CollatzResearch.WordTrace tailWord_5451004 prefixEnd_5451004 103666114873366524277085 := by
  unfold tailWord_5451004
  simp only [CollatzResearch.WordTrace]
  refine ⟨99407224571975470105504033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132542966095967293474005377 99407224571975470105504033)
  ·
    refine ⟨74555418428981602579128025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99407224571975470105504033 74555418428981602579128025)
    ·
      refine ⟨55916563821736201934346019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74555418428981602579128025 55916563821736201934346019)
      ·
        refine ⟨83874845732604302901519029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55916563821736201934346019 83874845732604302901519029)
        ·
          refine ⟨7863266787431653397017409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83874845732604302901519029 7863266787431653397017409)
          ·
            refine ⟨5897450090573740047763057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7863266787431653397017409 5897450090573740047763057)
            ·
              refine ⟨4423087567930305035822293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5897450090573740047763057 4423087567930305035822293)
              ·
                refine ⟨103666114873366524277085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4423087567930305035822293 103666114873366524277085)
                ·
                  rfl

theorem cell23_5451004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 7].length) (baseStart_5451004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451004 prefixEnd_5451004 := by exact prefixLift 5451004
  have htrace : WordTrace (prefixWord ++ tailWord_5451004) baseStart_5451004 baseEnd_5451004 := by
    simpa [prefixWord, tailWord_5451004, baseEnd_5451004] using wordTrace_append hprefix tailTrace_5451004
  have hstable : (prefixWord ++ tailWord_5451004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451004).length < 2 ^ (prefixWord ++ tailWord_5451004).sum := by decide
  have hdescent : baseEnd_5451004 < baseStart_5451004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451048 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_5451048 : Nat := 118140960795 + 5451048 * 2 ^ 59
def prefixEnd_5451048 : Nat := 4983230072969 + 3 ^ 40 * 5451048 * 2
def baseEnd_5451048 : Nat := 2799007694729693983331093

theorem tailTrace_5451048 : CollatzResearch.WordTrace tailWord_5451048 prefixEnd_5451048 2799007694729693983331093 := by
  unfold tailWord_5451048
  simp only [CollatzResearch.WordTrace]
  refine ⟨99408026977895767862804899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132544035970527690483739865 99408026977895767862804899)
  ·
    refine ⟨149112040466843651794207349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99408026977895767862804899 149112040466843651794207349)
    ·
      refine ⟨13979253793766592355706939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149112040466843651794207349 13979253793766592355706939)
      ·
        refine ⟨20968880690649888533560409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13979253793766592355706939 20968880690649888533560409)
        ·
          refine ⟨15726660517987416400170307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20968880690649888533560409 15726660517987416400170307)
          ·
            refine ⟨23589990776981124600255461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15726660517987416400170307 23589990776981124600255461)
            ·
              refine ⟨4423123270683960862547899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23589990776981124600255461 4423123270683960862547899)
              ·
                refine ⟨6634684906025941293821849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423123270683960862547899 6634684906025941293821849)
                ·
                  refine ⟨4976013679519455970366387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6634684906025941293821849 4976013679519455970366387)
                  ·
                    refine ⟨7464020519279183955549581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976013679519455970366387 7464020519279183955549581)
                    ·
                      refine ⟨2799007694729693983331093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464020519279183955549581 2799007694729693983331093)
                      ·
                        rfl

theorem cell23_5451048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_5451048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451048 prefixEnd_5451048 := by exact prefixLift 5451048
  have htrace : WordTrace (prefixWord ++ tailWord_5451048) baseStart_5451048 baseEnd_5451048 := by
    simpa [prefixWord, tailWord_5451048, baseEnd_5451048] using wordTrace_append hprefix tailTrace_5451048
  have hstable : (prefixWord ++ tailWord_5451048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451048).length < 2 ^ (prefixWord ++ tailWord_5451048).sum := by decide
  have hdescent : baseEnd_5451048 < baseStart_5451048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451057 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_5451057 : Nat := 118140960795 + 5451057 * 2 ^ 59
def prefixEnd_5451057 : Nat := 4983230072969 + 3 ^ 40 * 5451057 * 2
def baseEnd_5451057 : Nat := 2799012316055584448118551

theorem tailTrace_5451057 : CollatzResearch.WordTrace tailWord_5451057 prefixEnd_5451057 2799012316055584448118551 := by
  unfold tailWord_5451057
  simp only [CollatzResearch.WordTrace]
  refine ⟨198816382212758930262687425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132544254808505953508458283 198816382212758930262687425)
  ·
    refine ⟨149112286659569197697015569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198816382212758930262687425 149112286659569197697015569)
    ·
      refine ⟨111834214994676898272761677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149112286659569197697015569 111834214994676898272761677)
      ·
        refine ⟨41937830623003836852285629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111834214994676898272761677 41937830623003836852285629)
        ·
          refine ⟨15726686483626438819607111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41937830623003836852285629 15726686483626438819607111)
          ·
            refine ⟨23590029725439658229410667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15726686483626438819607111 23590029725439658229410667)
            ·
              refine ⟨35385044588159487344116001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23590029725439658229410667 35385044588159487344116001)
              ·
                refine ⟨26538783441119615508087001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35385044588159487344116001 26538783441119615508087001)
                ·
                  refine ⟨19904087580839711631065251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26538783441119615508087001 19904087580839711631065251)
                  ·
                    refine ⟨29856131371259567446597877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19904087580839711631065251 29856131371259567446597877)
                    ·
                      refine ⟨2799012316055584448118551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29856131371259567446597877 2799012316055584448118551)
                      ·
                        rfl

theorem cell23_5451057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_5451057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451057 prefixEnd_5451057 := by exact prefixLift 5451057
  have htrace : WordTrace (prefixWord ++ tailWord_5451057) baseStart_5451057 baseEnd_5451057 := by
    simpa [prefixWord, tailWord_5451057, baseEnd_5451057] using wordTrace_append hprefix tailTrace_5451057
  have hstable : (prefixWord ++ tailWord_5451057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451057).length < 2 ^ (prefixWord ++ tailWord_5451057).sum := by decide
  have hdescent : baseEnd_5451057 < baseStart_5451057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451058 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_5451058 : Nat := 118140960795 + 5451058 * 2 ^ 59
def prefixEnd_5451058 : Nat := 4983230072969 + 3 ^ 40 * 5451058 * 2
def baseEnd_5451058 : Nat := 2799012829536238944206047

theorem tailTrace_5451058 : CollatzResearch.WordTrace tailWord_5451058 prefixEnd_5451058 2799012829536238944206047 := by
  unfold tailWord_5451058
  simp only [CollatzResearch.WordTrace]
  refine ⟨49704104671438826858368457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132544279123836871622315885 49704104671438826858368457)
  ·
    refine ⟨37278078503579120143776343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49704104671438826858368457 37278078503579120143776343)
    ·
      refine ⟨55917117755368680215664515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37278078503579120143776343 55917117755368680215664515)
      ·
        refine ⟨83875676633053020323496773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55917117755368680215664515 83875676633053020323496773)
        ·
          refine ⟨15726689368697441310655645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83875676633053020323496773 15726689368697441310655645)
          ·
            refine ⟨5897508513261540491495867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15726689368697441310655645 5897508513261540491495867)
            ·
              refine ⟨8846262769892310737243801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5897508513261540491495867 8846262769892310737243801)
              ·
                refine ⟨6634697077419233052932851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8846262769892310737243801 6634697077419233052932851)
                ·
                  refine ⟨9952045616128849579399277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6634697077419233052932851 9952045616128849579399277)
                  ·
                    refine ⟨3732017106048318592274729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9952045616128849579399277 3732017106048318592274729)
                    ·
                      refine ⟨2799012829536238944206047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3732017106048318592274729 2799012829536238944206047)
                      ·
                        rfl

theorem cell23_5451058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_5451058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451058 prefixEnd_5451058 := by exact prefixLift 5451058
  have htrace : WordTrace (prefixWord ++ tailWord_5451058) baseStart_5451058 baseEnd_5451058 := by
    simpa [prefixWord, tailWord_5451058, baseEnd_5451058] using wordTrace_append hprefix tailTrace_5451058
  have hstable : (prefixWord ++ tailWord_5451058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451058).length < 2 ^ (prefixWord ++ tailWord_5451058).sum := by decide
  have hdescent : baseEnd_5451058 < baseStart_5451058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5451104 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 3]
def baseStart_5451104 : Nat := 118140960795 + 5451104 * 2 ^ 59
def prefixEnd_5451104 : Nat := 4983230072969 + 3 ^ 40 * 5451104 * 2
def baseEnd_5451104 : Nat := 2799036449646345764230835

theorem tailTrace_5451104 : CollatzResearch.WordTrace tailWord_5451104 prefixEnd_5451104 2799036449646345764230835 := by
  unfold tailWord_5451104
  simp only [CollatzResearch.WordTrace]
  refine ⟨99409048221794328644824183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132545397629059104859765577 99409048221794328644824183)
  ·
    refine ⟨149113572332691492967236275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99409048221794328644824183 149113572332691492967236275)
    ·
      refine ⟨223670358499037239450854413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149113572332691492967236275 223670358499037239450854413)
      ·
        refine ⟨83876384437138964794070405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223670358499037239450854413 83876384437138964794070405)
        ·
          refine ⟨15726822081963555898888201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83876384437138964794070405 15726822081963555898888201)
          ·
            refine ⟨11795116561472666924166151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15726822081963555898888201 11795116561472666924166151)
            ·
              refine ⟨17692674842209000386249227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11795116561472666924166151 17692674842209000386249227)
              ·
                refine ⟨26539012263313500579373841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17692674842209000386249227 26539012263313500579373841)
                ·
                  refine ⟨19904259197485125434530381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26539012263313500579373841 19904259197485125434530381)
                  ·
                    refine ⟨7464097199056922037948893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19904259197485125434530381 7464097199056922037948893)
                    ·
                      refine ⟨2799036449646345764230835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7464097199056922037948893 2799036449646345764230835)
                      ·
                        rfl

theorem cell23_5451104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_5451104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5451104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5451104 prefixEnd_5451104 := by exact prefixLift 5451104
  have htrace : WordTrace (prefixWord ++ tailWord_5451104) baseStart_5451104 baseEnd_5451104 := by
    simpa [prefixWord, tailWord_5451104, baseEnd_5451104] using wordTrace_append hprefix tailTrace_5451104
  have hstable : (prefixWord ++ tailWord_5451104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5451104).length < 2 ^ (prefixWord ++ tailWord_5451104).sum := by decide
  have hdescent : baseEnd_5451104 < baseStart_5451104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5451104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
