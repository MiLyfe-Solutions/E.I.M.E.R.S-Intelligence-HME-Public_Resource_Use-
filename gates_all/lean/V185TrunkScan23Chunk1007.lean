import V185TrunkScan23Chunk1006

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5963633 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 1, 5]
def baseStart_5963633 : Nat := 118140960795 + 5963633 * 2 ^ 59
def prefixEnd_5963633 : Nat := 4983230072969 + 3 ^ 40 * 5963633 * 2
def baseEnd_5963633 : Nat := 1020736725338190330720419

theorem tailTrace_5963633 : CollatzResearch.WordTrace tailWord_5963633 prefixEnd_5963633 1020736725338190330720419 := by
  unfold tailWord_5963633
  simp only [CollatzResearch.WordTrace]
  refine ⟨217511564803783623273991553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145007709869189082182661035 217511564803783623273991553)
  ·
    refine ⟨163133673602837717455493665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217511564803783623273991553 163133673602837717455493665)
    ·
      refine ⟨122350255202128288091620249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163133673602837717455493665 122350255202128288091620249)
      ·
        refine ⟨91762691401596216068715187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122350255202128288091620249 91762691401596216068715187)
        ·
          refine ⟨137644037102394324103072781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91762691401596216068715187 137644037102394324103072781)
          ·
            refine ⟨51616513913397871538652293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137644037102394324103072781 51616513913397871538652293)
            ·
              refine ⟨9678096358762100913497305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51616513913397871538652293 9678096358762100913497305)
              ·
                refine ⟨7258572269071575685122979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9678096358762100913497305 7258572269071575685122979)
                ·
                  refine ⟨10887858403607363527684469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7258572269071575685122979 10887858403607363527684469)
                  ·
                    refine ⟨1020736725338190330720419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10887858403607363527684469 1020736725338190330720419)
                    ·
                      rfl

theorem cell23_5963633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_5963633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963633 prefixEnd_5963633 := by exact prefixLift 5963633
  have htrace : WordTrace (prefixWord ++ tailWord_5963633) baseStart_5963633 baseEnd_5963633 := by
    simpa [prefixWord, tailWord_5963633, baseEnd_5963633] using wordTrace_append hprefix tailTrace_5963633
  have hstable : (prefixWord ++ tailWord_5963633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963633).length < 2 ^ (prefixWord ++ tailWord_5963633).sum := by decide
  have hdescent : baseEnd_5963633 < baseStart_5963633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963653 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 4]
def baseStart_5963653 : Nat := 118140960795 + 5963653 * 2 ^ 59
def prefixEnd_5963653 : Nat := 4983230072969 + 3 ^ 40 * 5963653 * 2
def baseEnd_5963653 : Nat := 3062220445627660913911165

theorem tailTrace_5963653 : CollatzResearch.WordTrace tailWord_5963653 prefixEnd_5963653 3062220445627660913911165 := by
  unfold tailWord_5963653
  simp only [CollatzResearch.WordTrace]
  refine ⟨217512294263711166689719613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145008196175807444459813075 217512294263711166689719613)
  ·
    refine ⟨81567110348891687508644855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217512294263711166689719613 81567110348891687508644855)
    ·
      refine ⟨122350665523337531262967283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81567110348891687508644855 122350665523337531262967283)
      ·
        refine ⟨183525998285006296894450925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122350665523337531262967283 183525998285006296894450925)
        ·
          refine ⟨68822249356877361335419097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183525998285006296894450925 68822249356877361335419097)
          ·
            refine ⟨51616687017658021001564323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68822249356877361335419097 51616687017658021001564323)
            ·
              refine ⟨77425030526487031502346485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51616687017658021001564323 77425030526487031502346485)
              ·
                refine ⟨7258596611858159203344983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77425030526487031502346485 7258596611858159203344983)
                ·
                  refine ⟨10887894917787238805017475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7258596611858159203344983 10887894917787238805017475)
                  ·
                    refine ⟨16331842376680858207526213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10887894917787238805017475 16331842376680858207526213)
                    ·
                      refine ⟨3062220445627660913911165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16331842376680858207526213 3062220445627660913911165)
                      ·
                        rfl

theorem cell23_5963653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_5963653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963653 prefixEnd_5963653 := by exact prefixLift 5963653
  have htrace : WordTrace (prefixWord ++ tailWord_5963653) baseStart_5963653 baseEnd_5963653 := by
    simpa [prefixWord, tailWord_5963653, baseEnd_5963653] using wordTrace_append hprefix tailTrace_5963653
  have hstable : (prefixWord ++ tailWord_5963653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963653).length < 2 ^ (prefixWord ++ tailWord_5963653).sum := by decide
  have hdescent : baseEnd_5963653 < baseStart_5963653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963687 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_5963687 : Nat := 118140960795 + 5963687 * 2 ^ 59
def prefixEnd_5963687 : Nat := 4983230072969 + 3 ^ 40 * 5963687 * 2
def baseEnd_5963687 : Nat := 3062237903969913780886009

theorem tailTrace_5963687 : CollatzResearch.WordTrace tailWord_5963687 prefixEnd_5963687 3062237903969913780886009 := by
  unfold tailWord_5963687
  simp only [CollatzResearch.WordTrace]
  refine ⟨217513534345587990496457315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145009022897058660330971543 217513534345587990496457315)
  ·
    refine ⟨326270301518381985744685973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217513534345587990496457315 326270301518381985744685973)
    ·
      refine ⟨15293920383674155581782155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 326270301518381985744685973 15293920383674155581782155)
      ·
        refine ⟨22940880575511233372673233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15293920383674155581782155 22940880575511233372673233)
        ·
          refine ⟨17205660431633425029504925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22940880575511233372673233 17205660431633425029504925)
          ·
            refine ⟨6452122661862534386064347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17205660431633425029504925 6452122661862534386064347)
            ·
              refine ⟨9678183992793801579096521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6452122661862534386064347 9678183992793801579096521)
              ·
                refine ⟨7258637994595351184322391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9678183992793801579096521 7258637994595351184322391)
                ·
                  refine ⟨10887956991893026776483587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7258637994595351184322391 10887956991893026776483587)
                  ·
                    refine ⟨16331935487839540164725381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10887956991893026776483587 16331935487839540164725381)
                    ·
                      refine ⟨3062237903969913780886009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16331935487839540164725381 3062237903969913780886009)
                      ·
                        rfl

theorem cell23_5963687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_5963687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963687 prefixEnd_5963687 := by exact prefixLift 5963687
  have htrace : WordTrace (prefixWord ++ tailWord_5963687) baseStart_5963687 baseEnd_5963687 := by
    simpa [prefixWord, tailWord_5963687, baseEnd_5963687] using wordTrace_append hprefix tailTrace_5963687
  have hstable : (prefixWord ++ tailWord_5963687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963687).length < 2 ^ (prefixWord ++ tailWord_5963687).sum := by decide
  have hdescent : baseEnd_5963687 < baseStart_5963687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963760 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 1, 4, 2]
def baseStart_5963760 : Nat := 118140960795 + 5963760 * 2 ^ 59
def prefixEnd_5963760 : Nat := 4983230072969 + 3 ^ 40 * 5963760 * 2
def baseEnd_5963760 : Nat := 3062275388057691995273173

theorem tailTrace_5963760 : CollatzResearch.WordTrace tailWord_5963760 prefixEnd_5963760 3062275388057691995273173 := by
  unfold tailWord_5963760
  simp only [CollatzResearch.WordTrace]
  refine ⟨108758098437161761981932367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145010797916215682642576489 108758098437161761981932367)
  ·
    refine ⟨163137147655742642972898551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108758098437161761981932367 163137147655742642972898551)
    ·
      refine ⟨244705721483613964459347827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163137147655742642972898551 244705721483613964459347827)
      ·
        refine ⟨367058582225420946689021741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244705721483613964459347827 367058582225420946689021741)
        ·
          refine ⟨137646968334532855008383153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367058582225420946689021741 137646968334532855008383153)
          ·
            refine ⟨103235226250899641256287365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137646968334532855008383153 103235226250899641256287365)
            ·
              refine ⟨19356604922043682735553881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103235226250899641256287365 19356604922043682735553881)
              ·
                refine ⟨14517453691532762051665411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19356604922043682735553881 14517453691532762051665411)
                ·
                  refine ⟨21776180537299143077498117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14517453691532762051665411 21776180537299143077498117)
                  ·
                    refine ⟨4083033850743589327030897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21776180537299143077498117 4083033850743589327030897)
                    ·
                      refine ⟨3062275388057691995273173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083033850743589327030897 3062275388057691995273173)
                      ·
                        rfl

theorem cell23_5963760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 4, 2].length) (baseStart_5963760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963760 prefixEnd_5963760 := by exact prefixLift 5963760
  have htrace : WordTrace (prefixWord ++ tailWord_5963760) baseStart_5963760 baseEnd_5963760 := by
    simpa [prefixWord, tailWord_5963760, baseEnd_5963760] using wordTrace_append hprefix tailTrace_5963760
  have hstable : (prefixWord ++ tailWord_5963760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963760).length < 2 ^ (prefixWord ++ tailWord_5963760).sum := by decide
  have hdescent : baseEnd_5963760 < baseStart_5963760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963773 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_5963773 : Nat := 118140960795 + 5963773 * 2 ^ 59
def prefixEnd_5963773 : Nat := 4983230072969 + 3 ^ 40 * 5963773 * 2
def baseEnd_5963773 : Nat := 3062282063306200444410613

theorem tailTrace_5963773 : CollatzResearch.WordTrace tailWord_5963773 prefixEnd_5963773 3062282063306200444410613 := by
  unfold tailWord_5963773
  simp only [CollatzResearch.WordTrace]
  refine ⟨217516671023276427184087973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145011114015517618122725315 217516671023276427184087973)
  ·
    refine ⟨40784375816864330097016495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217516671023276427184087973 40784375816864330097016495)
    ·
      refine ⟨61176563725296495145524743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40784375816864330097016495 61176563725296495145524743)
      ·
        refine ⟨91764845587944742718287115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61176563725296495145524743 91764845587944742718287115)
        ·
          refine ⟨137647268381917114077430673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91764845587944742718287115 137647268381917114077430673)
          ·
            refine ⟨103235451286437835558073005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137647268381917114077430673 103235451286437835558073005)
            ·
              refine ⟨38713294232414188334277377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103235451286437835558073005 38713294232414188334277377)
              ·
                refine ⟨29034970674310641250708033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38713294232414188334277377 29034970674310641250708033)
                ·
                  refine ⟨21776228005732980938031025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29034970674310641250708033 21776228005732980938031025)
                  ·
                    refine ⟨16332171004299735703523269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21776228005732980938031025 16332171004299735703523269)
                    ·
                      refine ⟨3062282063306200444410613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16332171004299735703523269 3062282063306200444410613)
                      ·
                        rfl

theorem cell23_5963773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_5963773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963773 prefixEnd_5963773 := by exact prefixLift 5963773
  have htrace : WordTrace (prefixWord ++ tailWord_5963773) baseStart_5963773 baseEnd_5963773 := by
    simpa [prefixWord, tailWord_5963773, baseEnd_5963773] using wordTrace_append hprefix tailTrace_5963773
  have hstable : (prefixWord ++ tailWord_5963773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963773).length < 2 ^ (prefixWord ++ tailWord_5963773).sum := by decide
  have hdescent : baseEnd_5963773 < baseStart_5963773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963776 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_5963776 : Nat := 118140960795 + 5963776 * 2 ^ 59
def prefixEnd_5963776 : Nat := 4983230072969 + 3 ^ 40 * 5963776 * 2
def baseEnd_5963776 : Nat := 3062283603748163932673099

theorem tailTrace_5963776 : CollatzResearch.WordTrace tailWord_5963776 prefixEnd_5963776 3062283603748163932673099 := by
  unfold tailWord_5963776
  simp only [CollatzResearch.WordTrace]
  refine ⟨108758390221132779348223591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145011186961510372464298121 108758390221132779348223591)
  ·
    refine ⟨163137585331699169022335387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108758390221132779348223591 163137585331699169022335387)
    ·
      refine ⟨244706377997548753533503081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163137585331699169022335387 244706377997548753533503081)
      ·
        refine ⟨183529783498161565150127311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244706377997548753533503081 183529783498161565150127311)
        ·
          refine ⟨275294675247242347725190967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183529783498161565150127311 275294675247242347725190967)
          ·
            refine ⟨412942012870863521587786451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275294675247242347725190967 412942012870863521587786451)
            ·
              refine ⟨619413019306295282381679677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412942012870863521587786451 619413019306295282381679677)
              ·
                refine ⟨232279882239860730893129879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 619413019306295282381679677 232279882239860730893129879)
                ·
                  refine ⟨348419823359791096339694819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232279882239860730893129879 348419823359791096339694819)
                  ·
                    refine ⟨522629735039686644509542229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 348419823359791096339694819 522629735039686644509542229)
                    ·
                      refine ⟨3062283603748163932673099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 522629735039686644509542229 3062283603748163932673099)
                      ·
                        rfl

theorem cell23_5963776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_5963776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963776 prefixEnd_5963776 := by exact prefixLift 5963776
  have htrace : WordTrace (prefixWord ++ tailWord_5963776) baseStart_5963776 baseEnd_5963776 := by
    simpa [prefixWord, tailWord_5963776, baseEnd_5963776] using wordTrace_append hprefix tailTrace_5963776
  have hstable : (prefixWord ++ tailWord_5963776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963776).length < 2 ^ (prefixWord ++ tailWord_5963776).sum := by decide
  have hdescent : baseEnd_5963776 < baseStart_5963776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963777 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_5963777 : Nat := 118140960795 + 5963777 * 2 ^ 59
def prefixEnd_5963777 : Nat := 4983230072969 + 3 ^ 40 * 5963777 * 2
def baseEnd_5963777 : Nat := 3062284117228818428760595

theorem tailTrace_5963777 : CollatzResearch.WordTrace tailWord_5963777 prefixEnd_5963777 3062284117228818428760595 := by
  unfold tailWord_5963777
  simp only [CollatzResearch.WordTrace]
  refine ⟨217516816915261935867233585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145011211276841290578155723 217516816915261935867233585)
  ·
    refine ⟨163137612686446451900425189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217516816915261935867233585 163137612686446451900425189)
    ·
      refine ⟨30588302378708709731329723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163137612686446451900425189 30588302378708709731329723)
      ·
        refine ⟨45882453568063064596994585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30588302378708709731329723 45882453568063064596994585)
        ·
          refine ⟨34411840176047298447745939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45882453568063064596994585 34411840176047298447745939)
          ·
            refine ⟨51617760264070947671618909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34411840176047298447745939 51617760264070947671618909)
            ·
              refine ⟨19356660099026605376857091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51617760264070947671618909 19356660099026605376857091)
              ·
                refine ⟨29034990148539908065285637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19356660099026605376857091 29034990148539908065285637)
                ·
                  refine ⟨5444060652851232762241057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29034990148539908065285637 5444060652851232762241057)
                  ·
                    refine ⟨4083045489638424571680793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5444060652851232762241057 4083045489638424571680793)
                    ·
                      refine ⟨3062284117228818428760595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083045489638424571680793 3062284117228818428760595)
                      ·
                        rfl

theorem cell23_5963777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_5963777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963777 prefixEnd_5963777 := by exact prefixLift 5963777
  have htrace : WordTrace (prefixWord ++ tailWord_5963777) baseStart_5963777 baseEnd_5963777 := by
    simpa [prefixWord, tailWord_5963777, baseEnd_5963777] using wordTrace_append hprefix tailTrace_5963777
  have hstable : (prefixWord ++ tailWord_5963777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963777).length < 2 ^ (prefixWord ++ tailWord_5963777).sum := by decide
  have hdescent : baseEnd_5963777 < baseStart_5963777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963783 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 7]
def baseStart_5963783 : Nat := 118140960795 + 5963783 * 2 ^ 59
def prefixEnd_5963783 : Nat := 4983230072969 + 3 ^ 40 * 5963783 * 2
def baseEnd_5963783 : Nat := 340254133123638378365063

theorem tailTrace_5963783 : CollatzResearch.WordTrace tailWord_5963783 prefixEnd_5963783 340254133123638378365063 := by
  unfold tailWord_5963783
  simp only [CollatzResearch.WordTrace]
  refine ⟨217517035753240198891952003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145011357168826799261301335 217517035753240198891952003)
  ·
    refine ⟨326275553629860298337928005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217517035753240198891952003 326275553629860298337928005)
    ·
      refine ⟨61176666305598805938361501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326275553629860298337928005 61176666305598805938361501)
      ·
        refine ⟨22941249864599552226885563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61176666305598805938361501 22941249864599552226885563)
        ·
          refine ⟨34411874796899328340328345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22941249864599552226885563 34411874796899328340328345)
          ·
            refine ⟨25808906097674496255246259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34411874796899328340328345 25808906097674496255246259)
            ·
              refine ⟨38713359146511744382869389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25808906097674496255246259 38713359146511744382869389)
              ·
                refine ⟨14517509679941904143576021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38713359146511744382869389 14517509679941904143576021)
                ·
                  refine ⟨340254133123638378365063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14517509679941904143576021 340254133123638378365063)
                  ·
                    rfl

theorem cell23_5963783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 7].length) (baseStart_5963783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963783 prefixEnd_5963783 := by exact prefixLift 5963783
  have htrace : WordTrace (prefixWord ++ tailWord_5963783) baseStart_5963783 baseEnd_5963783 := by
    simpa [prefixWord, tailWord_5963783, baseEnd_5963783] using wordTrace_append hprefix tailTrace_5963783
  have hstable : (prefixWord ++ tailWord_5963783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963783).length < 2 ^ (prefixWord ++ tailWord_5963783).sum := by decide
  have hdescent : baseEnd_5963783 < baseStart_5963783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963813 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_5963813 : Nat := 118140960795 + 5963813 * 2 ^ 59
def prefixEnd_5963813 : Nat := 4983230072969 + 3 ^ 40 * 5963813 * 2
def baseEnd_5963813 : Nat := 1020767534177460095970143

theorem tailTrace_5963813 : CollatzResearch.WordTrace tailWord_5963813 prefixEnd_5963813 1020767534177460095970143 := by
  unfold tailWord_5963813
  simp only [CollatzResearch.WordTrace]
  refine ⟨217518129943131514015544093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145012086628754342677029395 217518129943131514015544093)
  ·
    refine ⟨81569298728674317755829035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217518129943131514015544093 81569298728674317755829035)
    ·
      refine ⟨122353948093011476633743553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81569298728674317755829035 122353948093011476633743553)
      ·
        refine ⟨91765461069758607475307665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122353948093011476633743553 91765461069758607475307665)
        ·
          refine ⟨68824095802318955606480749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91765461069758607475307665 68824095802318955606480749)
          ·
            refine ⟨25809035925869608352430281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68824095802318955606480749 25809035925869608352430281)
            ·
              refine ⟨19356776944402206264322711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25809035925869608352430281 19356776944402206264322711)
              ·
                refine ⟨29035165416603309396484067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19356776944402206264322711 29035165416603309396484067)
                ·
                  refine ⟨43552748124904964094726101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29035165416603309396484067 43552748124904964094726101)
                  ·
                    refine ⟨1020767534177460095970143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43552748124904964094726101 1020767534177460095970143)
                    ·
                      rfl

theorem cell23_5963813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_5963813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963813 prefixEnd_5963813 := by exact prefixLift 5963813
  have htrace : WordTrace (prefixWord ++ tailWord_5963813) baseStart_5963813 baseEnd_5963813 := by
    simpa [prefixWord, tailWord_5963813, baseEnd_5963813] using wordTrace_append hprefix tailTrace_5963813
  have hstable : (prefixWord ++ tailWord_5963813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963813).length < 2 ^ (prefixWord ++ tailWord_5963813).sum := by decide
  have hdescent : baseEnd_5963813 < baseStart_5963813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963850 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_5963850 : Nat := 118140960795 + 5963850 * 2 ^ 59
def prefixEnd_5963850 : Nat := 4983230072969 + 3 ^ 40 * 5963850 * 2
def baseEnd_5963850 : Nat := 3062321601316596643147759

theorem tailTrace_5963850 : CollatzResearch.WordTrace tailWord_5963850 prefixEnd_5963850 3062321601316596643147759 := by
  unfold tailWord_5963850
  simp only [CollatzResearch.WordTrace]
  refine ⟨54379869860999367333660251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145012986295998312889760669 54379869860999367333660251)
  ·
    refine ⟨81569804791499051000490377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54379869860999367333660251 81569804791499051000490377)
    ·
      refine ⟨61177353593624288250367783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81569804791499051000490377 61177353593624288250367783)
      ·
        refine ⟨91766030390436432375551675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61177353593624288250367783 91766030390436432375551675)
        ·
          refine ⟨137649045585654648563327513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91766030390436432375551675 137649045585654648563327513)
          ·
            refine ⟨103236784189240986422495635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137649045585654648563327513 103236784189240986422495635)
            ·
              refine ⟨154855176283861479633743453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103236784189240986422495635 154855176283861479633743453)
              ·
                refine ⟨58070691106448054862653795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154855176283861479633743453 58070691106448054862653795)
                ·
                  refine ⟨87106036659672082293980693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58070691106448054862653795 87106036659672082293980693)
                  ·
                    refine ⟨4083095468422128857530345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87106036659672082293980693 4083095468422128857530345)
                    ·
                      refine ⟨3062321601316596643147759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083095468422128857530345 3062321601316596643147759)
                      ·
                        rfl

theorem cell23_5963850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_5963850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963850 prefixEnd_5963850 := by exact prefixLift 5963850
  have htrace : WordTrace (prefixWord ++ tailWord_5963850) baseStart_5963850 baseEnd_5963850 := by
    simpa [prefixWord, tailWord_5963850, baseEnd_5963850] using wordTrace_append hprefix tailTrace_5963850
  have hstable : (prefixWord ++ tailWord_5963850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963850).length < 2 ^ (prefixWord ++ tailWord_5963850).sum := by decide
  have hdescent : baseEnd_5963850 < baseStart_5963850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963860 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 5, 4]
def baseStart_5963860 : Nat := 118140960795 + 5963860 * 2 ^ 59
def prefixEnd_5963860 : Nat := 4983230072969 + 3 ^ 40 * 5963860 * 2
def baseEnd_5963860 : Nat := 1020775578707713868007571

theorem tailTrace_5963860 : CollatzResearch.WordTrace tailWord_5963860 prefixEnd_5963860 1020775578707713868007571 := by
  unfold tailWord_5963860
  simp only [CollatzResearch.WordTrace]
  refine ⟨108759922086980620521252517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145013229449307494028336689 108759922086980620521252517)
  ·
    refine ⟨20392485391308866347734847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108759922086980620521252517 20392485391308866347734847)
    ·
      refine ⟨30588728086963299521602271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20392485391308866347734847 30588728086963299521602271)
      ·
        refine ⟨45883092130444949282403407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30588728086963299521602271 45883092130444949282403407)
        ·
          refine ⟨68824638195667423923605111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45883092130444949282403407 68824638195667423923605111)
          ·
            refine ⟨103236957293501135885407667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68824638195667423923605111 103236957293501135885407667)
            ·
              refine ⟨154855435940251703828111501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103236957293501135885407667 154855435940251703828111501)
              ·
                refine ⟨58070788477594388935541813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154855435940251703828111501 58070788477594388935541813)
                ·
                  refine ⟨5444136419774473962707045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58070788477594388935541813 5444136419774473962707045)
                  ·
                    refine ⟨1020775578707713868007571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5444136419774473962707045 1020775578707713868007571)
                    ·
                      rfl

theorem cell23_5963860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_5963860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963860 prefixEnd_5963860 := by exact prefixLift 5963860
  have htrace : WordTrace (prefixWord ++ tailWord_5963860) baseStart_5963860 baseEnd_5963860 := by
    simpa [prefixWord, tailWord_5963860, baseEnd_5963860] using wordTrace_append hprefix tailTrace_5963860
  have hstable : (prefixWord ++ tailWord_5963860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963860).length < 2 ^ (prefixWord ++ tailWord_5963860).sum := by decide
  have hdescent : baseEnd_5963860 < baseStart_5963860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963863 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_5963863 : Nat := 118140960795 + 5963863 * 2 ^ 59
def prefixEnd_5963863 : Nat := 4983230072969 + 3 ^ 40 * 5963863 * 2
def baseEnd_5963863 : Nat := 3062328276565105092285199

theorem tailTrace_5963863 : CollatzResearch.WordTrace tailWord_5963863 prefixEnd_5963863 3062328276565105092285199 := by
  unfold tailWord_5963863
  simp only [CollatzResearch.WordTrace]
  refine ⟨217519953592950372554864243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145013302395300248369909495 217519953592950372554864243)
  ·
    refine ⟨326279930389425558832296365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217519953592950372554864243 326279930389425558832296365)
    ·
      refine ⟨122354973896034584562111137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326279930389425558832296365 122354973896034584562111137)
      ·
        refine ⟨91766230422025938421583353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122354973896034584562111137 91766230422025938421583353)
        ·
          refine ⟨68824672816519453816187515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91766230422025938421583353 68824672816519453816187515)
          ·
            refine ⟨103237009224779180724281273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68824672816519453816187515 103237009224779180724281273)
            ·
              refine ⟨77427756918584385543210955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103237009224779180724281273 77427756918584385543210955)
              ·
                refine ⟨116141635377876578314816433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77427756918584385543210955 116141635377876578314816433)
                ·
                  refine ⟨87106226533407433736112325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116141635377876578314816433 87106226533407433736112325)
                  ·
                    refine ⟨16332417475013893825521061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87106226533407433736112325 16332417475013893825521061)
                    ·
                      refine ⟨3062328276565105092285199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16332417475013893825521061 3062328276565105092285199)
                      ·
                        rfl

theorem cell23_5963863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_5963863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963863 prefixEnd_5963863 := by exact prefixLift 5963863
  have htrace : WordTrace (prefixWord ++ tailWord_5963863) baseStart_5963863 baseEnd_5963863 := by
    simpa [prefixWord, tailWord_5963863, baseEnd_5963863] using wordTrace_append hprefix tailTrace_5963863
  have hstable : (prefixWord ++ tailWord_5963863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963863).length < 2 ^ (prefixWord ++ tailWord_5963863).sum := by decide
  have hdescent : baseEnd_5963863 < baseStart_5963863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963890 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 6]
def baseStart_5963890 : Nat := 118140960795 + 5963890 * 2 ^ 59
def prefixEnd_5963890 : Nat := 4983230072969 + 3 ^ 40 * 5963890 * 2
def baseEnd_5963890 : Nat := 340260237838086276294175

theorem tailTrace_5963890 : CollatzResearch.WordTrace tailWord_5963890 prefixEnd_5963890 340260237838086276294175 := by
  unfold tailWord_5963890
  simp only [CollatzResearch.WordTrace]
  refine ⟨54380234590963139041524281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145013958909235037444064749 54380234590963139041524281)
  ·
    refine ⟨40785175943222354281143211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54380234590963139041524281 40785175943222354281143211)
    ·
      refine ⟨61177763914833531421714817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40785175943222354281143211 61177763914833531421714817)
      ·
        refine ⟨45883322936125148566286113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61177763914833531421714817 45883322936125148566286113)
        ·
          refine ⟨34412492202093861424714585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45883322936125148566286113 34412492202093861424714585)
          ·
            refine ⟨25809369151570396068535939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34412492202093861424714585 25809369151570396068535939)
            ·
              refine ⟨38714053727355594102803909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25809369151570396068535939 38714053727355594102803909)
              ·
                refine ⟨7258885073879173894275733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38714053727355594102803909 7258885073879173894275733)
                ·
                  refine ⟨340260237838086276294175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7258885073879173894275733 340260237838086276294175)
                  ·
                    rfl

theorem cell23_5963890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_5963890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963890 prefixEnd_5963890 := by exact prefixLift 5963890
  have htrace : WordTrace (prefixWord ++ tailWord_5963890) baseStart_5963890 baseEnd_5963890 := by
    simpa [prefixWord, tailWord_5963890, baseEnd_5963890] using wordTrace_append hprefix tailTrace_5963890
  have hstable : (prefixWord ++ tailWord_5963890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963890).length < 2 ^ (prefixWord ++ tailWord_5963890).sum := by decide
  have hdescent : baseEnd_5963890 < baseStart_5963890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963913 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_5963913 : Nat := 118140960795 + 5963913 * 2 ^ 59
def prefixEnd_5963913 : Nat := 4983230072969 + 3 ^ 40 * 5963913 * 2
def baseEnd_5963913 : Nat := 3062353950597829896659969

theorem tailTrace_5963913 : CollatzResearch.WordTrace tailWord_5963913 prefixEnd_5963913 3062353950597829896659969 := by
  unfold tailWord_5963913
  simp only [CollatzResearch.WordTrace]
  refine ⟨217521777242769231094184393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145014518161846154062789595 217521777242769231094184393)
  ·
    refine ⟨163141332932076923320638295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217521777242769231094184393 163141332932076923320638295)
    ·
      refine ⟨244711999398115384980957443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163141332932076923320638295 244711999398115384980957443)
      ·
        refine ⟨367067999097173077471436165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244711999398115384980957443 367067999097173077471436165)
        ·
          refine ⟨68825249830719952025894281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367067999097173077471436165 68825249830719952025894281)
          ·
            refine ⟨51618937373039964019420711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68825249830719952025894281 51618937373039964019420711)
            ·
              refine ⟨77428406059559946029131067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51618937373039964019420711 77428406059559946029131067)
              ·
                refine ⟨116142609089339919043696601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77428406059559946029131067 116142609089339919043696601)
                ·
                  refine ⟨87106956817004939282772451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116142609089339919043696601 87106956817004939282772451)
                  ·
                    refine ⟨130660435225507408924158677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87106956817004939282772451 130660435225507408924158677)
                    ·
                      refine ⟨3062353950597829896659969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130660435225507408924158677 3062353950597829896659969)
                      ·
                        rfl

theorem cell23_5963913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_5963913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963913 prefixEnd_5963913 := by exact prefixLift 5963913
  have htrace : WordTrace (prefixWord ++ tailWord_5963913) baseStart_5963913 baseEnd_5963913 := by
    simpa [prefixWord, tailWord_5963913, baseEnd_5963913] using wordTrace_append hprefix tailTrace_5963913
  have hstable : (prefixWord ++ tailWord_5963913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963913).length < 2 ^ (prefixWord ++ tailWord_5963913).sum := by decide
  have hdescent : baseEnd_5963913 < baseStart_5963913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963920 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 1, 5]
def baseStart_5963920 : Nat := 118140960795 + 5963920 * 2 ^ 59
def prefixEnd_5963920 : Nat := 4983230072969 + 3 ^ 40 * 5963920 * 2
def baseEnd_5963920 : Nat := 1020785848320803789757479

theorem tailTrace_5963920 : CollatzResearch.WordTrace tailWord_5963920 prefixEnd_5963920 1020785848320803789757479 := by
  unfold tailWord_5963920
  simp only [CollatzResearch.WordTrace]
  refine ⟨108761016276871935644844607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145014688369162580859792809 108761016276871935644844607)
  ·
    refine ⟨163141524415307903467266911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108761016276871935644844607 163141524415307903467266911)
    ·
      refine ⟨244712286622961855200900367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163141524415307903467266911 244712286622961855200900367)
      ·
        refine ⟨367068429934442782801350551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244712286622961855200900367 367068429934442782801350551)
        ·
          refine ⟨550602644901664174202025827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367068429934442782801350551 550602644901664174202025827)
          ·
            refine ⟨825903967352496261303038741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550602644901664174202025827 825903967352496261303038741)
            ·
              refine ⟨38714248469648262248579941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 825903967352496261303038741 38714248469648262248579941)
              ·
                refine ⟨7258921588059049171608739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38714248469648262248579941 7258921588059049171608739)
                ·
                  refine ⟨10888382382088573757413109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7258921588059049171608739 10888382382088573757413109)
                  ·
                    refine ⟨1020785848320803789757479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10888382382088573757413109 1020785848320803789757479)
                    ·
                      rfl

theorem cell23_5963920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 5].length) (baseStart_5963920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963920 prefixEnd_5963920 := by exact prefixLift 5963920
  have htrace : WordTrace (prefixWord ++ tailWord_5963920) baseStart_5963920 baseEnd_5963920 := by
    simpa [prefixWord, tailWord_5963920, baseEnd_5963920] using wordTrace_append hprefix tailTrace_5963920
  have hstable : (prefixWord ++ tailWord_5963920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963920).length < 2 ^ (prefixWord ++ tailWord_5963920).sum := by decide
  have hdescent : baseEnd_5963920 < baseStart_5963920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963937 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 1, 5]
def baseStart_5963937 : Nat := 118140960795 + 5963937 * 2 ^ 59
def prefixEnd_5963937 : Nat := 4983230072969 + 3 ^ 40 * 5963937 * 2
def baseEnd_5963937 : Nat := 1020788758044512600919953

theorem tailTrace_5963937 : CollatzResearch.WordTrace tailWord_5963937 prefixEnd_5963937 1020788758044512600919953 := by
  unfold tailWord_5963937
  simp only [CollatzResearch.WordTrace]
  refine ⟨217522652594682283193058065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145015101729788188795372043 217522652594682283193058065)
  ·
    refine ⟨163141989446011712394793549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217522652594682283193058065 163141989446011712394793549)
    ·
      refine ⟨61178246042254392148047581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163141989446011712394793549 61178246042254392148047581)
      ·
        refine ⟨22941842265845397055517843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61178246042254392148047581 22941842265845397055517843)
        ·
          refine ⟨34412763398768095583276765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22941842265845397055517843 34412763398768095583276765)
          ·
            refine ⟨12904786274538035843728787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34412763398768095583276765 12904786274538035843728787)
            ·
              refine ⟨19357179411807053765593181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12904786274538035843728787 19357179411807053765593181)
              ·
                refine ⟨7258942279427645162097443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19357179411807053765593181 7258942279427645162097443)
                ·
                  refine ⟨10888413419141467743146165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7258942279427645162097443 10888413419141467743146165)
                  ·
                    refine ⟨1020788758044512600919953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10888413419141467743146165 1020788758044512600919953)
                    ·
                      rfl

theorem cell23_5963937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_5963937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963937 prefixEnd_5963937 := by exact prefixLift 5963937
  have htrace : WordTrace (prefixWord ++ tailWord_5963937) baseStart_5963937 baseEnd_5963937 := by
    simpa [prefixWord, tailWord_5963937, baseEnd_5963937] using wordTrace_append hprefix tailTrace_5963937
  have hstable : (prefixWord ++ tailWord_5963937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963937).length < 2 ^ (prefixWord ++ tailWord_5963937).sum := by decide
  have hdescent : baseEnd_5963937 < baseStart_5963937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963960 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_5963960 : Nat := 118140960795 + 5963960 * 2 ^ 59
def prefixEnd_5963960 : Nat := 4983230072969 + 3 ^ 40 * 5963960 * 2
def baseEnd_5963960 : Nat := 3062378084188591212772253

theorem tailTrace_5963960 : CollatzResearch.WordTrace tailWord_5963960 prefixEnd_5963960 3062378084188591212772253 := by
  unfold tailWord_5963960
  simp only [CollatzResearch.WordTrace]
  refine ⟨108761745736799479060572667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145015660982399305414096889 108761745736799479060572667)
  ·
    refine ⟨163142618605199218590859001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108761745736799479060572667 163142618605199218590859001)
    ·
      refine ⟨122356963953899413943144251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163142618605199218590859001 122356963953899413943144251)
      ·
        refine ⟨183535445930849120914716377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122356963953899413943144251 183535445930849120914716377)
        ·
          refine ⟨137651584448136840686037283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183535445930849120914716377 137651584448136840686037283)
          ·
            refine ⟨206477376672205261029055925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137651584448136840686037283 206477376672205261029055925)
            ·
              refine ⟨19357254063019243221473993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206477376672205261029055925 19357254063019243221473993)
              ·
                refine ⟨14517940547264432416105495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19357254063019243221473993 14517940547264432416105495)
                ·
                  refine ⟨21776910820896648624158243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14517940547264432416105495 21776910820896648624158243)
                  ·
                    refine ⟨32665366231344972936237365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21776910820896648624158243 32665366231344972936237365)
                    ·
                      refine ⟨3062378084188591212772253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32665366231344972936237365 3062378084188591212772253)
                      ·
                        rfl

theorem cell23_5963960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_5963960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963960 prefixEnd_5963960 := by exact prefixLift 5963960
  have htrace : WordTrace (prefixWord ++ tailWord_5963960) baseStart_5963960 baseEnd_5963960 := by
    simpa [prefixWord, tailWord_5963960, baseEnd_5963960] using wordTrace_append hprefix tailTrace_5963960
  have hstable : (prefixWord ++ tailWord_5963960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963960).length < 2 ^ (prefixWord ++ tailWord_5963960).sum := by decide
  have hdescent : baseEnd_5963960 < baseStart_5963960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963963 : List Nat := [1, 1, 1, 1, 1, 2, 6, 10]
def baseStart_5963963 : Nat := 118140960795 + 5963963 * 2 ^ 59
def prefixEnd_5963963 : Nat := 4983230072969 + 3 ^ 40 * 5963963 * 2
def baseEnd_5963963 : Nat := 113421467578909433371657

theorem tailTrace_5963963 : CollatzResearch.WordTrace tailWord_5963963 prefixEnd_5963963 113421467578909433371657 := by
  unfold tailWord_5963963
  simp only [CollatzResearch.WordTrace]
  refine ⟨217523600892588089633504543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145015733928392059755669695 217523600892588089633504543)
  ·
    refine ⟨326285401338882134450256815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217523600892588089633504543 326285401338882134450256815)
    ·
      refine ⟨489428102008323201675385223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326285401338882134450256815 489428102008323201675385223)
      ·
        refine ⟨734142153012484802513077835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489428102008323201675385223 734142153012484802513077835)
        ·
          refine ⟨1101213229518727203769616753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734142153012484802513077835 1101213229518727203769616753)
          ·
            refine ⟨825909922139045402827212565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101213229518727203769616753 825909922139045402827212565)
            ·
              refine ⟨38714527600267753257525589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 825909922139045402827212565 38714527600267753257525589)
              ·
                refine ⟨113421467578909433371657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38714527600267753257525589 113421467578909433371657)
                ·
                  rfl

theorem cell23_5963963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 10].length) (baseStart_5963963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963963 prefixEnd_5963963 := by exact prefixLift 5963963
  have htrace : WordTrace (prefixWord ++ tailWord_5963963) baseStart_5963963 baseEnd_5963963 := by
    simpa [prefixWord, tailWord_5963963, baseEnd_5963963] using wordTrace_append hprefix tailTrace_5963963
  have hstable : (prefixWord ++ tailWord_5963963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963963).length < 2 ^ (prefixWord ++ tailWord_5963963).sum := by decide
  have hdescent : baseEnd_5963963 < baseStart_5963963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5963997 : List Nat := [1, 4, 3, 2, 1, 3, 9]
def baseStart_5963997 : Nat := 118140960795 + 5963997 * 2 ^ 59
def prefixEnd_5963997 : Nat := 4983230072969 + 3 ^ 40 * 5963997 * 2
def baseEnd_5963997 : Nat := 37807371394726019358143

theorem tailTrace_5963997 : CollatzResearch.WordTrace tailWord_5963997 prefixEnd_5963997 37807371394726019358143 := by
  unfold tailWord_5963997
  simp only [CollatzResearch.WordTrace]
  refine ⟨217524840974464913440242245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145016560649643275626828163 217524840974464913440242245)
  ·
    refine ⟨40785907682712171270045421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217524840974464913440242245 40785907682712171270045421)
    ·
      refine ⟨15294715381017064226267033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40785907682712171270045421 15294715381017064226267033)
      ·
        refine ⟨11471036535762798169700275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15294715381017064226267033 11471036535762798169700275)
        ·
          refine ⟨17206554803644197254550413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11471036535762798169700275 17206554803644197254550413)
          ·
            refine ⟨6452458051366573970456405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17206554803644197254550413 6452458051366573970456405)
            ·
              refine ⟨37807371394726019358143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6452458051366573970456405 37807371394726019358143)
              ·
                rfl

theorem cell23_5963997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 9].length) (baseStart_5963997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5963997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5963997 prefixEnd_5963997 := by exact prefixLift 5963997
  have htrace : WordTrace (prefixWord ++ tailWord_5963997) baseStart_5963997 baseEnd_5963997 := by
    simpa [prefixWord, tailWord_5963997, baseEnd_5963997] using wordTrace_append hprefix tailTrace_5963997
  have hstable : (prefixWord ++ tailWord_5963997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5963997).length < 2 ^ (prefixWord ++ tailWord_5963997).sum := by decide
  have hdescent : baseEnd_5963997 < baseStart_5963997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5963997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964002 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5964002 : Nat := 118140960795 + 5964002 * 2 ^ 59
def prefixEnd_5964002 : Nat := 4983230072969 + 3 ^ 40 * 5964002 * 2
def baseEnd_5964002 : Nat := 3062399650376080048447061

theorem tailTrace_5964002 : CollatzResearch.WordTrace tailWord_5964002 prefixEnd_5964002 3062399650376080048447061 := by
  unfold tailWord_5964002
  simp only [CollatzResearch.WordTrace]
  refine ⟨54381255834861699823543565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145016682226297866196116173 54381255834861699823543565)
  ·
    refine ⟨20392970938073137433828837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54381255834861699823543565 20392970938073137433828837)
    ·
      refine ⟨3823682050888713268842907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20392970938073137433828837 3823682050888713268842907)
      ·
        refine ⟨5735523076333069903264361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823682050888713268842907 5735523076333069903264361)
        ·
          refine ⟨4301642307249802427448271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5735523076333069903264361 4301642307249802427448271)
          ·
            refine ⟨6452463460874703641172407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301642307249802427448271 6452463460874703641172407)
            ·
              refine ⟨9678695191312055461758611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6452463460874703641172407 9678695191312055461758611)
              ·
                refine ⟨14518042786968083192637917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9678695191312055461758611 14518042786968083192637917)
                ·
                  refine ⟨5444266045113031197239219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14518042786968083192637917 5444266045113031197239219)
                  ·
                    refine ⟨8166399067669546795858829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5444266045113031197239219 8166399067669546795858829)
                    ·
                      refine ⟨3062399650376080048447061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8166399067669546795858829 3062399650376080048447061)
                      ·
                        rfl

theorem cell23_5964002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5964002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964002 prefixEnd_5964002 := by exact prefixLift 5964002
  have htrace : WordTrace (prefixWord ++ tailWord_5964002) baseStart_5964002 baseEnd_5964002 := by
    simpa [prefixWord, tailWord_5964002, baseEnd_5964002] using wordTrace_append hprefix tailTrace_5964002
  have hstable : (prefixWord ++ tailWord_5964002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964002).length < 2 ^ (prefixWord ++ tailWord_5964002).sum := by decide
  have hdescent : baseEnd_5964002 < baseStart_5964002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964010 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_5964010 : Nat := 118140960795 + 5964010 * 2 ^ 59
def prefixEnd_5964010 : Nat := 4983230072969 + 3 ^ 40 * 5964010 * 2
def baseEnd_5964010 : Nat := 1020801252740438672382341

theorem tailTrace_5964010 : CollatzResearch.WordTrace tailWord_5964010 prefixEnd_5964010 1020801252740438672382341 := by
  unfold tailWord_5964010
  simp only [CollatzResearch.WordTrace]
  refine ⟨54381328780854454165116371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145016876748945211106976989 54381328780854454165116371)
  ·
    refine ⟨81571993171281681247674557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54381328780854454165116371 81571993171281681247674557)
    ·
      refine ⟨30589497439230630467877959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81571993171281681247674557 30589497439230630467877959)
      ·
        refine ⟨45884246158845945701816939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30589497439230630467877959 45884246158845945701816939)
        ·
          refine ⟨68826369238268918552725409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45884246158845945701816939 68826369238268918552725409)
          ·
            refine ⟨51619776928701688914544057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68826369238268918552725409 51619776928701688914544057)
            ·
              refine ⟨38714832696526266685908043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51619776928701688914544057 38714832696526266685908043)
              ·
                refine ⟨58072249044789400028862065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38714832696526266685908043 58072249044789400028862065)
                ·
                  refine ⟨43554186783592050021646549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58072249044789400028862065 43554186783592050021646549)
                  ·
                    refine ⟨1020801252740438672382341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43554186783592050021646549 1020801252740438672382341)
                    ·
                      rfl

theorem cell23_5964010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_5964010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964010 prefixEnd_5964010 := by exact prefixLift 5964010
  have htrace : WordTrace (prefixWord ++ tailWord_5964010) baseStart_5964010 baseEnd_5964010 := by
    simpa [prefixWord, tailWord_5964010, baseEnd_5964010] using wordTrace_append hprefix tailTrace_5964010
  have hstable : (prefixWord ++ tailWord_5964010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964010).length < 2 ^ (prefixWord ++ tailWord_5964010).sum := by decide
  have hdescent : baseEnd_5964010 < baseStart_5964010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964060 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5964060 : Nat := 118140960795 + 5964060 * 2 ^ 59
def prefixEnd_5964060 : Nat := 4983230072969 + 3 ^ 40 * 5964060 * 2
def baseEnd_5964060 : Nat := 3062429432254040821521793

theorem tailTrace_5964060 : CollatzResearch.WordTrace tailWord_5964060 prefixEnd_5964060 3062429432254040821521793 := by
  unfold tailWord_5964060
  simp only [CollatzResearch.WordTrace]
  refine ⟨108763569386618337599892817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145018092515491116799857089 108763569386618337599892817)
  ·
    refine ⟨81572677039963753199919613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108763569386618337599892817 81572677039963753199919613)
    ·
      refine ⟨30589753889986407449969855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81572677039963753199919613 30589753889986407449969855)
      ·
        refine ⟨45884630834979611174954783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30589753889986407449969855 45884630834979611174954783)
        ·
          refine ⟨68826946252469416762432175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45884630834979611174954783 68826946252469416762432175)
          ·
            refine ⟨103240419378704125143648263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68826946252469416762432175 103240419378704125143648263)
            ·
              refine ⟨154860629068056187715472395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103240419378704125143648263 154860629068056187715472395)
              ·
                refine ⟨232290943602084281573208593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154860629068056187715472395 232290943602084281573208593)
                ·
                  refine ⟨174218207701563211179906445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232290943602084281573208593 174218207701563211179906445)
                  ·
                    refine ⟨65331827888086204192464917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 174218207701563211179906445 65331827888086204192464917)
                    ·
                      refine ⟨3062429432254040821521793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65331827888086204192464917 3062429432254040821521793)
                      ·
                        rfl

theorem cell23_5964060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5964060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964060 prefixEnd_5964060 := by exact prefixLift 5964060
  have htrace : WordTrace (prefixWord ++ tailWord_5964060) baseStart_5964060 baseEnd_5964060 := by
    simpa [prefixWord, tailWord_5964060, baseEnd_5964060] using wordTrace_append hprefix tailTrace_5964060
  have hstable : (prefixWord ++ tailWord_5964060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964060).length < 2 ^ (prefixWord ++ tailWord_5964060).sum := by decide
  have hdescent : baseEnd_5964060 < baseStart_5964060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964074 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_5964074 : Nat := 118140960795 + 5964074 * 2 ^ 59
def prefixEnd_5964074 : Nat := 4983230072969 + 3 ^ 40 * 5964074 * 2
def baseEnd_5964074 : Nat := 1020812206994401255582243

theorem tailTrace_5964074 : CollatzResearch.WordTrace tailWord_5964074 prefixEnd_5964074 1020812206994401255582243 := by
  unfold tailWord_5964074
  simp only [CollatzResearch.WordTrace]
  refine ⟨54381912348796488897698819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145018432930123970393863517 54381912348796488897698819)
  ·
    refine ⟨81572868523194733346548229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54381912348796488897698819 81572868523194733346548229)
    ·
      refine ⟨15294912848099012502477793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81572868523194733346548229 15294912848099012502477793)
      ·
        refine ⟨11471184636074259376858345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15294912848099012502477793 11471184636074259376858345)
        ·
          refine ⟨8603388477055694532643759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11471184636074259376858345 8603388477055694532643759)
          ·
            refine ⟨12905082715583541798965639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8603388477055694532643759 12905082715583541798965639)
            ·
              refine ⟨19357624073375312698448459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12905082715583541798965639 19357624073375312698448459)
              ·
                refine ⟨29036436110062969047672689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19357624073375312698448459 29036436110062969047672689)
                ·
                  refine ⟨21777327082547226785754517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29036436110062969047672689 21777327082547226785754517)
                  ·
                    refine ⟨1020812206994401255582243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21777327082547226785754517 1020812206994401255582243)
                    ·
                      rfl

theorem cell23_5964074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_5964074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964074 prefixEnd_5964074 := by exact prefixLift 5964074
  have htrace : WordTrace (prefixWord ++ tailWord_5964074) baseStart_5964074 baseEnd_5964074 := by
    simpa [prefixWord, tailWord_5964074, baseEnd_5964074] using wordTrace_append hprefix tailTrace_5964074
  have hstable : (prefixWord ++ tailWord_5964074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964074).length < 2 ^ (prefixWord ++ tailWord_5964074).sum := by decide
  have hdescent : baseEnd_5964074 < baseStart_5964074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964081 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 1, 4, 2]
def baseStart_5964081 : Nat := 118140960795 + 5964081 * 2 ^ 59
def prefixEnd_5964081 : Nat := 4983230072969 + 3 ^ 40 * 5964081 * 2
def baseEnd_5964081 : Nat := 3062440215347785239359197

theorem tailTrace_5964081 : CollatzResearch.WordTrace tailWord_5964081 prefixEnd_5964081 3062440215347785239359197 := by
  unfold tailWord_5964081
  simp only [CollatzResearch.WordTrace]
  refine ⟨217527904706160595786300097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145018603137440397190866731 217527904706160595786300097)
  ·
    refine ⟨163145928529620446839725073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217527904706160595786300097 163145928529620446839725073)
    ·
      refine ⟨122359446397215335129793805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163145928529620446839725073 122359446397215335129793805)
      ·
        refine ⟨45884792398955750673672677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122359446397215335129793805 45884792398955750673672677)
        ·
          refine ⟨8603398574804203251313627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45884792398955750673672677 8603398574804203251313627)
          ·
            refine ⟨12905097862206304876970441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8603398574804203251313627 12905097862206304876970441)
            ·
              refine ⟨9678823396654728657727831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12905097862206304876970441 9678823396654728657727831)
              ·
                refine ⟨14518235094982092986591747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9678823396654728657727831 14518235094982092986591747)
                ·
                  refine ⟨21777352642473139479887621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14518235094982092986591747 21777352642473139479887621)
                  ·
                    refine ⟨4083253620463713652478929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21777352642473139479887621 4083253620463713652478929)
                    ·
                      refine ⟨3062440215347785239359197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083253620463713652478929 3062440215347785239359197)
                      ·
                        rfl

theorem cell23_5964081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_5964081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964081 prefixEnd_5964081 := by exact prefixLift 5964081
  have htrace : WordTrace (prefixWord ++ tailWord_5964081) baseStart_5964081 baseEnd_5964081 := by
    simpa [prefixWord, tailWord_5964081, baseEnd_5964081] using wordTrace_append hprefix tailTrace_5964081
  have hstable : (prefixWord ++ tailWord_5964081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964081).length < 2 ^ (prefixWord ++ tailWord_5964081).sum := by decide
  have hdescent : baseEnd_5964081 < baseStart_5964081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964107 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 1, 7, 2]
def baseStart_5964107 : Nat := 118140960795 + 5964107 * 2 ^ 59
def prefixEnd_5964107 : Nat := 4983230072969 + 3 ^ 40 * 5964107 * 2
def baseEnd_5964107 : Nat := 3062453565844802137634077

theorem tailTrace_5964107 : CollatzResearch.WordTrace tailWord_5964107 prefixEnd_5964107 3062453565844802137634077 := by
  unfold tailWord_5964107
  simp only [CollatzResearch.WordTrace]
  refine ⟨217528853004066402226746575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145019235336044268151164383 217528853004066402226746575)
  ·
    refine ⟨326293279506099603340119863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217528853004066402226746575 326293279506099603340119863)
    ·
      refine ⟨489439919259149405010179795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326293279506099603340119863 489439919259149405010179795)
      ·
        refine ⟨734159878888724107515269693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489439919259149405010179795 734159878888724107515269693)
        ·
          refine ⟨275309954583271540318226135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 734159878888724107515269693 275309954583271540318226135)
          ·
            refine ⟨412964931874907310477339203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275309954583271540318226135 412964931874907310477339203)
            ·
              refine ⟨619447397812360965716008805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412964931874907310477339203 619447397812360965716008805)
              ·
                refine ⟨116146387089817681071751651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619447397812360965716008805 116146387089817681071751651)
                ·
                  refine ⟨174219580634726521607627477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116146387089817681071751651 174219580634726521607627477)
                  ·
                    refine ⟨4083271421126402850178769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 174219580634726521607627477 4083271421126402850178769)
                    ·
                      refine ⟨3062453565844802137634077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083271421126402850178769 3062453565844802137634077)
                      ·
                        rfl

theorem cell23_5964107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 7, 2].length) (baseStart_5964107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964107 prefixEnd_5964107 := by exact prefixLift 5964107
  have htrace : WordTrace (prefixWord ++ tailWord_5964107) baseStart_5964107 baseEnd_5964107 := by
    simpa [prefixWord, tailWord_5964107, baseEnd_5964107] using wordTrace_append hprefix tailTrace_5964107
  have hstable : (prefixWord ++ tailWord_5964107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964107).length < 2 ^ (prefixWord ++ tailWord_5964107).sum := by decide
  have hdescent : baseEnd_5964107 < baseStart_5964107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964194 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 6]
def baseStart_5964194 : Nat := 118140960795 + 5964194 * 2 ^ 59
def prefixEnd_5964194 : Nat := 4983230072969 + 3 ^ 40 * 5964194 * 2
def baseEnd_5964194 : Nat := 340277582073527033027353

theorem tailTrace_5964194 : CollatzResearch.WordTrace tailWord_5964194 prefixEnd_5964194 340277582073527033027353 := by
  unfold tailWord_5964194
  simp only [CollatzResearch.WordTrace]
  refine ⟨54383006538687804021290909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145021350769834144056775757 54383006538687804021290909)
  ·
    refine ⟨20393627452007926507984091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54383006538687804021290909 20393627452007926507984091)
    ·
      refine ⟨30590441178011889761976137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20393627452007926507984091 30590441178011889761976137)
      ·
        refine ⟨22942830883508917321482103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30590441178011889761976137 22942830883508917321482103)
        ·
          refine ⟨34414246325263375982223155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22942830883508917321482103 34414246325263375982223155)
          ·
            refine ⟨51621369487895063973334733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34414246325263375982223155 51621369487895063973334733)
            ·
              refine ⟨19358013557960648990000525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51621369487895063973334733 19358013557960648990000525)
              ·
                refine ⟨7259255084235243371250197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19358013557960648990000525 7259255084235243371250197)
                ·
                  refine ⟨340277582073527033027353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7259255084235243371250197 340277582073527033027353)
                  ·
                    rfl

theorem cell23_5964194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_5964194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964194 prefixEnd_5964194 := by exact prefixLift 5964194
  have htrace : WordTrace (prefixWord ++ tailWord_5964194) baseStart_5964194 baseEnd_5964194 := by
    simpa [prefixWord, tailWord_5964194, baseEnd_5964194] using wordTrace_append hprefix tailTrace_5964194
  have hstable : (prefixWord ++ tailWord_5964194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964194).length < 2 ^ (prefixWord ++ tailWord_5964194).sum := by decide
  have hdescent : baseEnd_5964194 < baseStart_5964194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964204 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 3]
def baseStart_5964204 : Nat := 118140960795 + 5964204 * 2 ^ 59
def prefixEnd_5964204 : Nat := 4983230072969 + 3 ^ 40 * 5964204 * 2
def baseEnd_5964204 : Nat := 3062503373468288258121131

theorem tailTrace_5964204 : CollatzResearch.WordTrace tailWord_5964204 prefixEnd_5964204 3062503373468288258121131 := by
  unfold tailWord_5964204
  simp only [CollatzResearch.WordTrace]
  refine ⟨108766195442357493896513833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145021593923143325195351777 108766195442357493896513833)
  ·
    refine ⟨81574646581768120422385375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108766195442357493896513833 81574646581768120422385375)
    ·
      refine ⟨122361969872652180633578063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81574646581768120422385375 122361969872652180633578063)
      ·
        refine ⟨183542954808978270950367095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122361969872652180633578063 183542954808978270950367095)
        ·
          refine ⟨275314432213467406425550643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183542954808978270950367095 275314432213467406425550643)
          ·
            refine ⟨412971648320201109638325965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275314432213467406425550643 412971648320201109638325965)
            ·
              refine ⟨154864368120075416114372237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412971648320201109638325965 154864368120075416114372237)
              ·
                refine ⟨58074138045028281042889589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154864368120075416114372237 58074138045028281042889589)
                ·
                  refine ⟨5444450441721401347770899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58074138045028281042889589 5444450441721401347770899)
                  ·
                    refine ⟨8166675662582102021656349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5444450441721401347770899 8166675662582102021656349)
                    ·
                      refine ⟨3062503373468288258121131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8166675662582102021656349 3062503373468288258121131)
                      ·
                        rfl

theorem cell23_5964204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_5964204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964204 prefixEnd_5964204 := by exact prefixLift 5964204
  have htrace : WordTrace (prefixWord ++ tailWord_5964204) baseStart_5964204 baseEnd_5964204 := by
    simpa [prefixWord, tailWord_5964204, baseEnd_5964204] using wordTrace_append hprefix tailTrace_5964204
  have hstable : (prefixWord ++ tailWord_5964204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964204).length < 2 ^ (prefixWord ++ tailWord_5964204).sum := by decide
  have hdescent : baseEnd_5964204 < baseStart_5964204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964231 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_5964231 : Nat := 118140960795 + 5964231 * 2 ^ 59
def prefixEnd_5964231 : Nat := 4983230072969 + 3 ^ 40 * 5964231 * 2
def baseEnd_5964231 : Nat := 3062517237445959652483507

theorem tailTrace_5964231 : CollatzResearch.WordTrace tailWord_5964231 prefixEnd_5964231 3062517237445959652483507 := by
  unfold tailWord_5964231
  simp only [CollatzResearch.WordTrace]
  refine ⟨217533375655617171404260547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145022250437078114269507031 217533375655617171404260547)
  ·
    refine ⟨326300063483425757106390821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217533375655617171404260547 326300063483425757106390821)
    ·
      refine ⟨61181261903142329457448279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326300063483425757106390821 61181261903142329457448279)
      ·
        refine ⟨91771892854713494186172419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61181261903142329457448279 91771892854713494186172419)
        ·
          refine ⟨137657839282070241279258629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91771892854713494186172419 137657839282070241279258629)
          ·
            refine ⟨25810844865388170239860993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137657839282070241279258629 25810844865388170239860993)
            ·
              refine ⟨19358133649041127679895745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25810844865388170239860993 19358133649041127679895745)
              ·
                refine ⟨14518600236780845759921809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19358133649041127679895745 14518600236780845759921809)
                ·
                  refine ⟨10888950177585634319941357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14518600236780845759921809 10888950177585634319941357)
                  ·
                    refine ⟨4083356316594612869978009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10888950177585634319941357 4083356316594612869978009)
                    ·
                      refine ⟨3062517237445959652483507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083356316594612869978009 3062517237445959652483507)
                      ·
                        rfl

theorem cell23_5964231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_5964231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964231 prefixEnd_5964231 := by exact prefixLift 5964231
  have htrace : WordTrace (prefixWord ++ tailWord_5964231) baseStart_5964231 baseEnd_5964231 := by
    simpa [prefixWord, tailWord_5964231, baseEnd_5964231] using wordTrace_append hprefix tailTrace_5964231
  have hstable : (prefixWord ++ tailWord_5964231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964231).length < 2 ^ (prefixWord ++ tailWord_5964231).sum := by decide
  have hdescent : baseEnd_5964231 < baseStart_5964231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964278 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_5964278 : Nat := 118140960795 + 5964278 * 2 ^ 59
def prefixEnd_5964278 : Nat := 4983230072969 + 3 ^ 40 * 5964278 * 2
def baseEnd_5964278 : Nat := 3062541371036720968595791

theorem tailTrace_5964278 : CollatzResearch.WordTrace tailWord_5964278 prefixEnd_5964278 3062541371036720968595791 := by
  unfold tailWord_5964278
  simp only [CollatzResearch.WordTrace]
  refine ⟨13595943117902931151951343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145023393257631265620814325 13595943117902931151951343)
  ·
    refine ⟨20393914676854396727927015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13595943117902931151951343 20393914676854396727927015)
    ·
      refine ⟨30590872015281595091890523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20393914676854396727927015 30590872015281595091890523)
      ·
        refine ⟨45886308022922392637835785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30590872015281595091890523 45886308022922392637835785)
        ·
          refine ⟨34414731017191794478376839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45886308022922392637835785 34414731017191794478376839)
          ·
            refine ⟨51622096525787691717565259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34414731017191794478376839 51622096525787691717565259)
            ·
              refine ⟨77433144788681537576347889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51622096525787691717565259 77433144788681537576347889)
              ·
                refine ⟨58074858591511153182260917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77433144788681537576347889 58074858591511153182260917)
                ·
                  refine ⟨5444517992954170610836961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58074858591511153182260917 5444517992954170610836961)
                  ·
                    refine ⟨4083388494715627958127721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5444517992954170610836961 4083388494715627958127721)
                    ·
                      refine ⟨3062541371036720968595791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083388494715627958127721 3062541371036720968595791)
                      ·
                        rfl

theorem cell23_5964278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_5964278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964278 prefixEnd_5964278 := by exact prefixLift 5964278
  have htrace : WordTrace (prefixWord ++ tailWord_5964278) baseStart_5964278 baseEnd_5964278 := by
    simpa [prefixWord, tailWord_5964278, baseEnd_5964278] using wordTrace_append hprefix tailTrace_5964278
  have hstable : (prefixWord ++ tailWord_5964278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964278).length < 2 ^ (prefixWord ++ tailWord_5964278).sum := by decide
  have hdescent : baseEnd_5964278 < baseStart_5964278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964295 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_5964295 : Nat := 118140960795 + 5964295 * 2 ^ 59
def prefixEnd_5964295 : Nat := 4983230072969 + 3 ^ 40 * 5964295 * 2
def baseEnd_5964295 : Nat := 3062550100207847402083213

theorem tailTrace_5964295 : CollatzResearch.WordTrace tailWord_5964295 prefixEnd_5964295 3062550100207847402083213 := by
  unfold tailWord_5964295
  simp only [CollatzResearch.WordTrace]
  refine ⟨217535709927385310334590339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145023806618256873556393559 217535709927385310334590339)
  ·
    refine ⟨326303564891077965501885509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217535709927385310334590339 326303564891077965501885509)
    ·
      refine ⟨61181918417077118531603533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326303564891077965501885509 61181918417077118531603533)
      ·
        refine ⟨22943219406403919449351325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61181918417077118531603533 22943219406403919449351325)
        ·
          refine ⟨8603707277401469793506747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22943219406403919449351325 8603707277401469793506747)
          ·
            refine ⟨12905560916102204690260121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8603707277401469793506747 12905560916102204690260121)
            ·
              refine ⟨9679170687076653517695091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12905560916102204690260121 9679170687076653517695091)
              ·
                refine ⟨14518756030614980276542637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9679170687076653517695091 14518756030614980276542637)
                ·
                  refine ⟨5444533511480617603703489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14518756030614980276542637 5444533511480617603703489)
                  ·
                    refine ⟨4083400133610463202777617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5444533511480617603703489 4083400133610463202777617)
                    ·
                      refine ⟨3062550100207847402083213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083400133610463202777617 3062550100207847402083213)
                      ·
                        rfl

theorem cell23_5964295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_5964295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964295 prefixEnd_5964295 := by exact prefixLift 5964295
  have htrace : WordTrace (prefixWord ++ tailWord_5964295) baseStart_5964295 baseEnd_5964295 := by
    simpa [prefixWord, tailWord_5964295, baseEnd_5964295] using wordTrace_append hprefix tailTrace_5964295
  have hstable : (prefixWord ++ tailWord_5964295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964295).length < 2 ^ (prefixWord ++ tailWord_5964295).sum := by decide
  have hdescent : baseEnd_5964295 < baseStart_5964295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964297 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 2, 7]
def baseStart_5964297 : Nat := 118140960795 + 5964297 * 2 ^ 59
def prefixEnd_5964297 : Nat := 4983230072969 + 3 ^ 40 * 5964297 * 2
def baseEnd_5964297 : Nat := 1020850375723052131419401

theorem tailTrace_5964297 : CollatzResearch.WordTrace tailWord_5964297 prefixEnd_5964297 1020850375723052131419401 := by
  unfold tailWord_5964297
  simp only [CollatzResearch.WordTrace]
  refine ⟨217535782873378064676163145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145023855248918709784108763 217535782873378064676163145)
  ·
    refine ⟨163151837155033548507122359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217535782873378064676163145 163151837155033548507122359)
    ·
      refine ⟨244727755732550322760683539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163151837155033548507122359 244727755732550322760683539)
      ·
        refine ⟨367091633598825484141025309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244727755732550322760683539 367091633598825484141025309)
        ·
          refine ⟨137659362599559556552884491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367091633598825484141025309 137659362599559556552884491)
          ·
            refine ⟨206489043899339334829326737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137659362599559556552884491 206489043899339334829326737)
            ·
              refine ⟨154866782924504501121995053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206489043899339334829326737 154866782924504501121995053)
              ·
                refine ⟨58075043596689187920748145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154866782924504501121995053 58075043596689187920748145)
                ·
                  refine ⟨43556282697516890940561109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58075043596689187920748145 43556282697516890940561109)
                  ·
                    refine ⟨1020850375723052131419401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43556282697516890940561109 1020850375723052131419401)
                    ·
                      rfl

theorem cell23_5964297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_5964297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964297 prefixEnd_5964297 := by exact prefixLift 5964297
  have htrace : WordTrace (prefixWord ++ tailWord_5964297) baseStart_5964297 baseEnd_5964297 := by
    simpa [prefixWord, tailWord_5964297, baseEnd_5964297] using wordTrace_append hprefix tailTrace_5964297
  have hstable : (prefixWord ++ tailWord_5964297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964297).length < 2 ^ (prefixWord ++ tailWord_5964297).sum := by decide
  have hdescent : baseEnd_5964297 < baseStart_5964297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964308 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_5964308 : Nat := 118140960795 + 5964308 * 2 ^ 59
def prefixEnd_5964308 : Nat := 4983230072969 + 3 ^ 40 * 5964308 * 2
def baseEnd_5964308 : Nat := 3062556775456355851220653

theorem tailTrace_5964308 : CollatzResearch.WordTrace tailWord_5964308 prefixEnd_5964308 3062556775456355851220653 := by
  unfold tailWord_5964308
  simp only [CollatzResearch.WordTrace]
  refine ⟨108768092038169106777406789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145024122717558809036542385 108768092038169106777406789)
  ·
    refine ⟨20394017257156707520763773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108768092038169106777406789 20394017257156707520763773)
    ·
      refine ⟨7647756471433765320286415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20394017257156707520763773 7647756471433765320286415)
      ·
        refine ⟨11471634707150647980429623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7647756471433765320286415 11471634707150647980429623)
        ·
          refine ⟨17207452060725971970644435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11471634707150647980429623 17207452060725971970644435)
          ·
            refine ⟨25811178091088957955966653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17207452060725971970644435 25811178091088957955966653)
            ·
              refine ⟨9679191784158359233487495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25811178091088957955966653 9679191784158359233487495)
              ·
                refine ⟨14518787676237538850231243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9679191784158359233487495 14518787676237538850231243)
                ·
                  refine ⟨21778181514356308275346865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14518787676237538850231243 21778181514356308275346865)
                  ·
                    refine ⟨16333636135767231206510149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21778181514356308275346865 16333636135767231206510149)
                    ·
                      refine ⟨3062556775456355851220653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16333636135767231206510149 3062556775456355851220653)
                      ·
                        rfl

theorem cell23_5964308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_5964308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964308 prefixEnd_5964308 := by exact prefixLift 5964308
  have htrace : WordTrace (prefixWord ++ tailWord_5964308) baseStart_5964308 baseEnd_5964308 := by
    simpa [prefixWord, tailWord_5964308, baseEnd_5964308] using wordTrace_append hprefix tailTrace_5964308
  have hstable : (prefixWord ++ tailWord_5964308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964308).length < 2 ^ (prefixWord ++ tailWord_5964308).sum := by decide
  have hdescent : baseEnd_5964308 < baseStart_5964308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964328 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_5964328 : Nat := 118140960795 + 5964328 * 2 ^ 59
def prefixEnd_5964328 : Nat := 4983230072969 + 3 ^ 40 * 5964328 * 2
def baseEnd_5964328 : Nat := 3062567045069445772970561

theorem tailTrace_5964328 : CollatzResearch.WordTrace tailWord_5964328 prefixEnd_5964328 3062567045069445772970561 := by
  unfold tailWord_5964328
  simp only [CollatzResearch.WordTrace]
  refine ⟨108768456768132878485270819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145024609024177171313694425 108768456768132878485270819)
  ·
    refine ⟨163152685152199317727906229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108768456768132878485270819 163152685152199317727906229)
    ·
      refine ⟨15295564233018686036991209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 163152685152199317727906229 15295564233018686036991209)
      ·
        refine ⟨11471673174764014527743407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15295564233018686036991209 11471673174764014527743407)
        ·
          refine ⟨17207509762146021791615111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11471673174764014527743407 17207509762146021791615111)
          ·
            refine ⟨25811264643219032687422667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17207509762146021791615111 25811264643219032687422667)
            ·
              refine ⟨38716896964828549031134001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25811264643219032687422667 38716896964828549031134001)
              ·
                refine ⟨29037672723621411773350501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38716896964828549031134001 29037672723621411773350501)
                ·
                  refine ⟨5444563635679014707503219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29037672723621411773350501 5444563635679014707503219)
                  ·
                    refine ⟨8166845453518522061254829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5444563635679014707503219 8166845453518522061254829)
                    ·
                      refine ⟨3062567045069445772970561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8166845453518522061254829 3062567045069445772970561)
                      ·
                        rfl

theorem cell23_5964328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_5964328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964328 prefixEnd_5964328 := by exact prefixLift 5964328
  have htrace : WordTrace (prefixWord ++ tailWord_5964328) baseStart_5964328 baseEnd_5964328 := by
    simpa [prefixWord, tailWord_5964328, baseEnd_5964328] using wordTrace_append hprefix tailTrace_5964328
  have hstable : (prefixWord ++ tailWord_5964328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964328).length < 2 ^ (prefixWord ++ tailWord_5964328).sum := by decide
  have hdescent : baseEnd_5964328 < baseStart_5964328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964338 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_5964338 : Nat := 118140960795 + 5964338 * 2 ^ 59
def prefixEnd_5964338 : Nat := 4983230072969 + 3 ^ 40 * 5964338 * 2
def baseEnd_5964338 : Nat := 3062572179875990733845515

theorem tailTrace_5964338 : CollatzResearch.WordTrace tailWord_5964338 prefixEnd_5964338 3062572179875990733845515 := by
  unfold tailWord_5964338
  simp only [CollatzResearch.WordTrace]
  refine ⟨54384319566557382169601417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145024852177486352452270445 54384319566557382169601417)
  ·
    refine ⟨40788239674918036627201063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54384319566557382169601417 40788239674918036627201063)
    ·
      refine ⟨61182359512377054940801595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40788239674918036627201063 61182359512377054940801595)
      ·
        refine ⟨91773539268565582411202393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61182359512377054940801595 91773539268565582411202393)
        ·
          refine ⟨68830154451424186808401795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91773539268565582411202393 68830154451424186808401795)
          ·
            refine ⟨103245231677136280212602693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68830154451424186808401795 103245231677136280212602693)
            ·
              refine ⟨19358480939463052539863005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103245231677136280212602693 19358480939463052539863005)
              ·
                refine ⟨7259430352298644702448627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19358480939463052539863005 7259430352298644702448627)
                ·
                  refine ⟨10889145528447967053672941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7259430352298644702448627 10889145528447967053672941)
                  ·
                    refine ⟨4083429573167987645127353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10889145528447967053672941 4083429573167987645127353)
                    ·
                      refine ⟨3062572179875990733845515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083429573167987645127353 3062572179875990733845515)
                      ·
                        rfl

theorem cell23_5964338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_5964338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964338 prefixEnd_5964338 := by exact prefixLift 5964338
  have htrace : WordTrace (prefixWord ++ tailWord_5964338) baseStart_5964338 baseEnd_5964338 := by
    simpa [prefixWord, tailWord_5964338, baseEnd_5964338] using wordTrace_append hprefix tailTrace_5964338
  have hstable : (prefixWord ++ tailWord_5964338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964338).length < 2 ^ (prefixWord ++ tailWord_5964338).sum := by decide
  have hdescent : baseEnd_5964338 < baseStart_5964338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964356 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5964356 : Nat := 118140960795 + 5964356 * 2 ^ 59
def prefixEnd_5964356 : Nat := 4983230072969 + 3 ^ 40 * 5964356 * 2
def baseEnd_5964356 : Nat := 1020860474175923887806811

theorem tailTrace_5964356 : CollatzResearch.WordTrace tailWord_5964356 prefixEnd_5964356 1020860474175923887806811 := by
  unfold tailWord_5964356
  simp only [CollatzResearch.WordTrace]
  refine ⟨108768967390082158876280461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145025289853442878501707281 108768967390082158876280461)
  ·
    refine ⟨40788362771280809578605173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108768967390082158876280461 40788362771280809578605173)
    ·
      refine ⟨3823909009807575897994235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40788362771280809578605173 3823909009807575897994235)
      ·
        refine ⟨5735863514711363846991353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823909009807575897994235 5735863514711363846991353)
        ·
          refine ⟨4301897636033522885243515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5735863514711363846991353 4301897636033522885243515)
          ·
            refine ⟨6452846454050284327865273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301897636033522885243515 6452846454050284327865273)
            ·
              refine ⟨4839634840537713245898955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6452846454050284327865273 4839634840537713245898955)
              ·
                refine ⟨7259452260806569868848433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839634840537713245898955 7259452260806569868848433)
                ·
                  refine ⟨5444589195604927401636325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7259452260806569868848433 5444589195604927401636325)
                  ·
                    refine ⟨1020860474175923887806811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5444589195604927401636325 1020860474175923887806811)
                    ·
                      rfl

theorem cell23_5964356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5964356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964356 prefixEnd_5964356 := by exact prefixLift 5964356
  have htrace : WordTrace (prefixWord ++ tailWord_5964356) baseStart_5964356 baseEnd_5964356 := by
    simpa [prefixWord, tailWord_5964356, baseEnd_5964356] using wordTrace_append hprefix tailTrace_5964356
  have hstable : (prefixWord ++ tailWord_5964356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964356).length < 2 ^ (prefixWord ++ tailWord_5964356).sum := by decide
  have hdescent : baseEnd_5964356 < baseStart_5964356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964364 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_5964364 : Nat := 118140960795 + 5964364 * 2 ^ 59
def prefixEnd_5964364 : Nat := 4983230072969 + 3 ^ 40 * 5964364 * 2
def baseEnd_5964364 : Nat := 3062585530373007632120395

theorem tailTrace_5964364 : CollatzResearch.WordTrace tailWord_5964364 prefixEnd_5964364 3062585530373007632120395 := by
  unfold tailWord_5964364
  simp only [CollatzResearch.WordTrace]
  refine ⟨108769113282067667559426073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145025484376090223412568097 108769113282067667559426073)
  ·
    refine ⟨81576834961550750669569555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108769113282067667559426073 81576834961550750669569555)
    ·
      refine ⟨122365252442326126004354333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81576834961550750669569555 122365252442326126004354333)
      ·
        refine ⟨45886969665872297251632875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122365252442326126004354333 45886969665872297251632875)
        ·
          refine ⟨68830454498808445877449313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45886969665872297251632875 68830454498808445877449313)
          ·
            refine ⟨51622840874106334408086985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68830454498808445877449313 51622840874106334408086985)
            ·
              refine ⟨38717130655579750806065239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51622840874106334408086985 38717130655579750806065239)
              ·
                refine ⟨58075695983369626209097859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38717130655579750806065239 58075695983369626209097859)
                ·
                  refine ⟨87113543975054439313646789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58075695983369626209097859 87113543975054439313646789)
                  ·
                    refine ⟨16333789495322707371308773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87113543975054439313646789 16333789495322707371308773)
                    ·
                      refine ⟨3062585530373007632120395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16333789495322707371308773 3062585530373007632120395)
                      ·
                        rfl

theorem cell23_5964364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_5964364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964364 prefixEnd_5964364 := by exact prefixLift 5964364
  have htrace : WordTrace (prefixWord ++ tailWord_5964364) baseStart_5964364 baseEnd_5964364 := by
    simpa [prefixWord, tailWord_5964364, baseEnd_5964364] using wordTrace_append hprefix tailTrace_5964364
  have hstable : (prefixWord ++ tailWord_5964364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964364).length < 2 ^ (prefixWord ++ tailWord_5964364).sum := by decide
  have hdescent : baseEnd_5964364 < baseStart_5964364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964391 : List Nat := [1, 1, 5, 1, 1, 1, 1, 7, 5]
def baseStart_5964391 : Nat := 118140960795 + 5964391 * 2 ^ 59
def prefixEnd_5964391 : Nat := 4983230072969 + 3 ^ 40 * 5964391 * 2
def baseEnd_5964391 : Nat := 340288821594519891831419

theorem tailTrace_5964391 : CollatzResearch.WordTrace tailWord_5964391 prefixEnd_5964391 340288821594519891831419 := by
  unfold tailWord_5964391
  simp only [CollatzResearch.WordTrace]
  refine ⟨217539211335037518730085027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145026140890025012486723351 217539211335037518730085027)
  ·
    refine ⟨326308817002556278095127541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217539211335037518730085027 326308817002556278095127541)
    ·
      refine ⟨30591451593989651071418207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 326308817002556278095127541 30591451593989651071418207)
      ·
        refine ⟨45887177390984476607127311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30591451593989651071418207 45887177390984476607127311)
        ·
          refine ⟨68830766086476714910690967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45887177390984476607127311 68830766086476714910690967)
          ·
            refine ⟨103246149129715072366036451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68830766086476714910690967 103246149129715072366036451)
            ·
              refine ⟨154869223694572608549054677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103246149129715072366036451 154869223694572608549054677)
              ·
                refine ⟨3629747430341545512868469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154869223694572608549054677 3629747430341545512868469)
                ·
                  refine ⟨340288821594519891831419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3629747430341545512868469 340288821594519891831419)
                  ·
                    rfl

theorem cell23_5964391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 5].length) (baseStart_5964391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964391 prefixEnd_5964391 := by exact prefixLift 5964391
  have htrace : WordTrace (prefixWord ++ tailWord_5964391) baseStart_5964391 baseEnd_5964391 := by
    simpa [prefixWord, tailWord_5964391, baseEnd_5964391] using wordTrace_append hprefix tailTrace_5964391
  have hstable : (prefixWord ++ tailWord_5964391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964391).length < 2 ^ (prefixWord ++ tailWord_5964391).sum := by decide
  have hdescent : baseEnd_5964391 < baseStart_5964391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964402 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_5964402 : Nat := 118140960795 + 5964402 * 2 ^ 59
def prefixEnd_5964402 : Nat := 4983230072969 + 3 ^ 40 * 5964402 * 2
def baseEnd_5964402 : Nat := 3062605042637878483445221

theorem tailTrace_5964402 : CollatzResearch.WordTrace tailWord_5964402 prefixEnd_5964402 3062605042637878483445221 := by
  unfold tailWord_5964402
  simp only [CollatzResearch.WordTrace]
  refine ⟨54384903134499416902183865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145026408358665111739156973 54384903134499416902183865)
  ·
    refine ⟨40788677350874562676637899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54384903134499416902183865 40788677350874562676637899)
    ·
      refine ⟨61183016026311844014956849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40788677350874562676637899 61183016026311844014956849)
      ·
        refine ⟨45887262019733883011217637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61183016026311844014956849 45887262019733883011217637)
        ·
          refine ⟨8603861628700103064603307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45887262019733883011217637 8603861628700103064603307)
          ·
            refine ⟨12905792443050154596904961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8603861628700103064603307 12905792443050154596904961)
            ·
              refine ⟨9679344332287615947678721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12905792443050154596904961 9679344332287615947678721)
              ·
                refine ⟨7259508249215711960759041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9679344332287615947678721 7259508249215711960759041)
                ·
                  refine ⟨5444631186911783970569281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7259508249215711960759041 5444631186911783970569281)
                  ·
                    refine ⟨4083473390183837977926961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5444631186911783970569281 4083473390183837977926961)
                    ·
                      refine ⟨3062605042637878483445221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083473390183837977926961 3062605042637878483445221)
                      ·
                        rfl

theorem cell23_5964402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_5964402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964402 prefixEnd_5964402 := by exact prefixLift 5964402
  have htrace : WordTrace (prefixWord ++ tailWord_5964402) baseStart_5964402 baseEnd_5964402 := by
    simpa [prefixWord, tailWord_5964402, baseEnd_5964402] using wordTrace_append hprefix tailTrace_5964402
  have hstable : (prefixWord ++ tailWord_5964402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964402).length < 2 ^ (prefixWord ++ tailWord_5964402).sum := by decide
  have hdescent : baseEnd_5964402 < baseStart_5964402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964441 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 1, 6, 2]
def baseStart_5964441 : Nat := 118140960795 + 5964441 * 2 ^ 59
def prefixEnd_5964441 : Nat := 4983230072969 + 3 ^ 40 * 5964441 * 2
def baseEnd_5964441 : Nat := 3062625068383403830857541

theorem tailTrace_5964441 : CollatzResearch.WordTrace tailWord_5964441 prefixEnd_5964441 3062625068383403830857541 := by
  unfold tailWord_5964441
  simp only [CollatzResearch.WordTrace]
  refine ⟨217541034984856377269405177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145027356656570918179603451 217541034984856377269405177)
  ·
    refine ⟨163155776238642282952053883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217541034984856377269405177 163155776238642282952053883)
    ·
      refine ⟨244733664357963424428080825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163155776238642282952053883 244733664357963424428080825)
      ·
        refine ⟨183550248268472568321060619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244733664357963424428080825 183550248268472568321060619)
        ·
          refine ⟨275325372402708852481590929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183550248268472568321060619 275325372402708852481590929)
          ·
            refine ⟨206494029302031639361193197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275325372402708852481590929 206494029302031639361193197)
            ·
              refine ⟨77435260988261864760447449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206494029302031639361193197 77435260988261864760447449)
              ·
                refine ⟨58076445741196398570335587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77435260988261864760447449 58076445741196398570335587)
                ·
                  refine ⟨87114668611794597855503381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58076445741196398570335587 87114668611794597855503381)
                  ·
                    refine ⟨4083500091177871774476721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87114668611794597855503381 4083500091177871774476721)
                    ·
                      refine ⟨3062625068383403830857541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083500091177871774476721 3062625068383403830857541)
                      ·
                        rfl

theorem cell23_5964441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_5964441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964441 prefixEnd_5964441 := by exact prefixLift 5964441
  have htrace : WordTrace (prefixWord ++ tailWord_5964441) baseStart_5964441 baseEnd_5964441 := by
    simpa [prefixWord, tailWord_5964441, baseEnd_5964441] using wordTrace_append hprefix tailTrace_5964441
  have hstable : (prefixWord ++ tailWord_5964441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964441).length < 2 ^ (prefixWord ++ tailWord_5964441).sum := by decide
  have hdescent : baseEnd_5964441 < baseStart_5964441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964531 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 4]
def baseStart_5964531 : Nat := 118140960795 + 5964531 * 2 ^ 59
def prefixEnd_5964531 : Nat := 4983230072969 + 3 ^ 40 * 5964531 * 2
def baseEnd_5964531 : Nat := 3062671281642308478732127

theorem tailTrace_5964531 : CollatzResearch.WordTrace tailWord_5964531 prefixEnd_5964531 3062671281642308478732127 := by
  unfold tailWord_5964531
  simp only [CollatzResearch.WordTrace]
  refine ⟨217544317554530322640181447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145029545036353548426787631 217544317554530322640181447)
  ·
    refine ⟨326316476331795483960272171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217544317554530322640181447 326316476331795483960272171)
    ·
      refine ⟨489474714497693225940408257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326316476331795483960272171 489474714497693225940408257)
      ·
        refine ⟨367106035873269919455306193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489474714497693225940408257 367106035873269919455306193)
        ·
          refine ⟨275329526904952439591479645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367106035873269919455306193 275329526904952439591479645)
          ·
            refine ⟨103248572589357164846804867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275329526904952439591479645 103248572589357164846804867)
            ·
              refine ⟨154872858884035747270207301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103248572589357164846804867 154872858884035747270207301)
              ·
                refine ⟨29038661040756702613163869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154872858884035747270207301 29038661040756702613163869)
                ·
                  refine ⟨10889497890283763479936451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29038661040756702613163869 10889497890283763479936451)
                  ·
                    refine ⟨16334246835425645219904677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10889497890283763479936451 16334246835425645219904677)
                    ·
                      refine ⟨3062671281642308478732127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16334246835425645219904677 3062671281642308478732127)
                      ·
                        rfl

theorem cell23_5964531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_5964531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964531 prefixEnd_5964531 := by exact prefixLift 5964531
  have htrace : WordTrace (prefixWord ++ tailWord_5964531) baseStart_5964531 baseEnd_5964531 := by
    simpa [prefixWord, tailWord_5964531, baseEnd_5964531] using wordTrace_append hprefix tailTrace_5964531
  have hstable : (prefixWord ++ tailWord_5964531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964531).length < 2 ^ (prefixWord ++ tailWord_5964531).sum := by decide
  have hdescent : baseEnd_5964531 < baseStart_5964531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964532 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 6]
def baseStart_5964532 : Nat := 118140960795 + 5964532 * 2 ^ 59
def prefixEnd_5964532 : Nat := 4983230072969 + 3 ^ 40 * 5964532 * 2
def baseEnd_5964532 : Nat := 340296866124773663868847

theorem tailTrace_5964532 : CollatzResearch.WordTrace tailWord_5964532 prefixEnd_5964532 340296866124773663868847 := by
  unfold tailWord_5964532
  simp only [CollatzResearch.WordTrace]
  refine ⟨108772177013763349905483925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145029569351684466540645233 108772177013763349905483925)
  ·
    refine ⟨5098695797520157026819559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108772177013763349905483925 5098695797520157026819559)
    ·
      refine ⟨7648043696280235540229339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5098695797520157026819559 7648043696280235540229339)
      ·
        refine ⟨11472065544420353310344009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7648043696280235540229339 11472065544420353310344009)
        ·
          refine ⟨8604049158315264982758007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11472065544420353310344009 8604049158315264982758007)
          ·
            refine ⟨12906073737472897474137011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8604049158315264982758007 12906073737472897474137011)
            ·
              refine ⟨19359110606209346211205517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12906073737472897474137011 19359110606209346211205517)
              ·
                refine ⟨7259666477328504829202069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19359110606209346211205517 7259666477328504829202069)
                ·
                  refine ⟨340296866124773663868847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7259666477328504829202069 340296866124773663868847)
                  ·
                    rfl

theorem cell23_5964532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_5964532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964532 prefixEnd_5964532 := by exact prefixLift 5964532
  have htrace : WordTrace (prefixWord ++ tailWord_5964532) baseStart_5964532 baseEnd_5964532 := by
    simpa [prefixWord, tailWord_5964532, baseEnd_5964532] using wordTrace_append hprefix tailTrace_5964532
  have hstable : (prefixWord ++ tailWord_5964532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964532).length < 2 ^ (prefixWord ++ tailWord_5964532).sum := by decide
  have hdescent : baseEnd_5964532 < baseStart_5964532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964541 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_5964541 : Nat := 118140960795 + 5964541 * 2 ^ 59
def prefixEnd_5964541 : Nat := 4983230072969 + 3 ^ 40 * 5964541 * 2
def baseEnd_5964541 : Nat := 1020892138816284479869027

theorem tailTrace_5964541 : CollatzResearch.WordTrace tailWord_5964541 prefixEnd_5964541 1020892138816284479869027 := by
  unfold tailWord_5964541
  simp only [CollatzResearch.WordTrace]
  refine ⟨217544682284494094348045477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145029788189662729565363651 217544682284494094348045477)
  ·
    refine ⟨40789627928342642690258527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217544682284494094348045477 40789627928342642690258527)
    ·
      refine ⟨61184441892513964035387791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40789627928342642690258527 61184441892513964035387791)
      ·
        refine ⟨91776662838770946053081687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61184441892513964035387791 91776662838770946053081687)
        ·
          refine ⟨137664994258156419079622531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91776662838770946053081687 137664994258156419079622531)
          ·
            refine ⟨206497491387234628619433797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137664994258156419079622531 206497491387234628619433797)
            ·
              refine ⟨38718279635106492866143837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206497491387234628619433797 38718279635106492866143837)
              ·
                refine ⟨14519354863164934824803939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38718279635106492866143837 14519354863164934824803939)
                ·
                  refine ⟨21779032294747402237205909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14519354863164934824803939 21779032294747402237205909)
                  ·
                    refine ⟨1020892138816284479869027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21779032294747402237205909 1020892138816284479869027)
                    ·
                      rfl

theorem cell23_5964541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_5964541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964541 prefixEnd_5964541 := by exact prefixLift 5964541
  have htrace : WordTrace (prefixWord ++ tailWord_5964541) baseStart_5964541 baseEnd_5964541 := by
    simpa [prefixWord, tailWord_5964541, baseEnd_5964541] using wordTrace_append hprefix tailTrace_5964541
  have hstable : (prefixWord ++ tailWord_5964541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964541).length < 2 ^ (prefixWord ++ tailWord_5964541).sum := by decide
  have hdescent : baseEnd_5964541 < baseStart_5964541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964548 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_5964548 : Nat := 118140960795 + 5964548 * 2 ^ 59
def prefixEnd_5964548 : Nat := 4983230072969 + 3 ^ 40 * 5964548 * 2
def baseEnd_5964548 : Nat := 3062680010813434912219549

theorem tailTrace_5964548 : CollatzResearch.WordTrace tailWord_5964548 prefixEnd_5964548 3062680010813434912219549 := by
  unfold tailWord_5964548
  simp only [CollatzResearch.WordTrace]
  refine ⟨108772468797734367271775149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145029958396979156362366865 108772468797734367271775149)
  ·
    refine ⟨40789675799150387726915681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108772468797734367271775149 40789675799150387726915681)
    ·
      refine ⟨30592256849362790795186761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40789675799150387726915681 30592256849362790795186761)
      ·
        refine ⟨22944192637022093096390071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30592256849362790795186761 22944192637022093096390071)
        ·
          refine ⟨34416288955533139644585107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22944192637022093096390071 34416288955533139644585107)
          ·
            refine ⟨51624433433299709466877661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34416288955533139644585107 51624433433299709466877661)
            ·
              refine ⟨19359162537487391050079123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51624433433299709466877661 19359162537487391050079123)
              ·
                refine ⟨29038743806231086575118685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19359162537487391050079123 29038743806231086575118685)
                ·
                  refine ⟨10889528927336657465669507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29038743806231086575118685 10889528927336657465669507)
                  ·
                    refine ⟨16334293391004986198504261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10889528927336657465669507 16334293391004986198504261)
                    ·
                      refine ⟨3062680010813434912219549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16334293391004986198504261 3062680010813434912219549)
                      ·
                        rfl

theorem cell23_5964548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_5964548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964548 prefixEnd_5964548 := by exact prefixLift 5964548
  have htrace : WordTrace (prefixWord ++ tailWord_5964548) baseStart_5964548 baseEnd_5964548 := by
    simpa [prefixWord, tailWord_5964548, baseEnd_5964548] using wordTrace_append hprefix tailTrace_5964548
  have hstable : (prefixWord ++ tailWord_5964548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964548).length < 2 ^ (prefixWord ++ tailWord_5964548).sum := by decide
  have hdescent : baseEnd_5964548 < baseStart_5964548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964561 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_5964561 : Nat := 118140960795 + 5964561 * 2 ^ 59
def prefixEnd_5964561 : Nat := 4983230072969 + 3 ^ 40 * 5964561 * 2
def baseEnd_5964561 : Nat := 3062686686061943361356989

theorem tailTrace_5964561 : CollatzResearch.WordTrace tailWord_5964561 prefixEnd_5964561 3062686686061943361356989 := by
  unfold tailWord_5964561
  simp only [CollatzResearch.WordTrace]
  refine ⟨217545411744421637763773537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145030274496281091842515691 217545411744421637763773537)
  ·
    refine ⟨163159058808316228322830153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217545411744421637763773537 163159058808316228322830153)
    ·
      refine ⟨122369294106237171242122615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163159058808316228322830153 122369294106237171242122615)
      ·
        refine ⟨183553941159355756863183923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122369294106237171242122615 183553941159355756863183923)
        ·
          refine ⟨275330911739033635294775885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183553941159355756863183923 275330911739033635294775885)
          ·
            refine ⟨103249091902137613235540957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275330911739033635294775885 103249091902137613235540957)
            ·
              refine ⟨38718409463301604963327859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103249091902137613235540957 38718409463301604963327859)
              ·
                refine ⟨58077614194952407444991789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38718409463301604963327859 58077614194952407444991789)
                ·
                  refine ⟨21779105323107152791871921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58077614194952407444991789 21779105323107152791871921)
                  ·
                    refine ⟨16334328992330364593903941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21779105323107152791871921 16334328992330364593903941)
                    ·
                      refine ⟨3062686686061943361356989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16334328992330364593903941 3062686686061943361356989)
                      ·
                        rfl

theorem cell23_5964561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_5964561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964561 prefixEnd_5964561 := by exact prefixLift 5964561
  have htrace : WordTrace (prefixWord ++ tailWord_5964561) baseStart_5964561 baseEnd_5964561 := by
    simpa [prefixWord, tailWord_5964561, baseEnd_5964561] using wordTrace_append hprefix tailTrace_5964561
  have hstable : (prefixWord ++ tailWord_5964561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964561).length < 2 ^ (prefixWord ++ tailWord_5964561).sum := by decide
  have hdescent : baseEnd_5964561 < baseStart_5964561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964565 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_5964565 : Nat := 118140960795 + 5964565 * 2 ^ 59
def prefixEnd_5964565 : Nat := 4983230072969 + 3 ^ 40 * 5964565 * 2
def baseEnd_5964565 : Nat := 3062688739984561345706971

theorem tailTrace_5964565 : CollatzResearch.WordTrace tailWord_5964565 prefixEnd_5964565 3062688739984561345706971 := by
  unfold tailWord_5964565
  simp only [CollatzResearch.WordTrace]
  refine ⟨217545557636407146446919149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145030371757604764297946099 217545557636407146446919149)
  ·
    refine ⟨81579584113652679917594681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217545557636407146446919149 81579584113652679917594681)
    ·
      refine ⟨61184688085239509938196011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81579584113652679917594681 61184688085239509938196011)
      ·
        refine ⟨91777032127859264907294017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61184688085239509938196011 91777032127859264907294017)
        ·
          refine ⟨68832774095894448680470513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91777032127859264907294017 68832774095894448680470513)
          ·
            refine ⟨51624580571920836510352885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68832774095894448680470513 51624580571920836510352885)
            ·
              refine ⟨4839804428617578422845583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51624580571920836510352885 4839804428617578422845583)
              ·
                refine ⟨7259706642926367634268375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839804428617578422845583 7259706642926367634268375)
                ·
                  refine ⟨10889559964389551451402563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7259706642926367634268375 10889559964389551451402563)
                  ·
                    refine ⟨16334339946584327177103845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10889559964389551451402563 16334339946584327177103845)
                    ·
                      refine ⟨3062688739984561345706971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16334339946584327177103845 3062688739984561345706971)
                      ·
                        rfl

theorem cell23_5964565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_5964565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964565 prefixEnd_5964565 := by exact prefixLift 5964565
  have htrace : WordTrace (prefixWord ++ tailWord_5964565) baseStart_5964565 baseEnd_5964565 := by
    simpa [prefixWord, tailWord_5964565, baseEnd_5964565] using wordTrace_append hprefix tailTrace_5964565
  have hstable : (prefixWord ++ tailWord_5964565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964565).length < 2 ^ (prefixWord ++ tailWord_5964565).sum := by decide
  have hdescent : baseEnd_5964565 < baseStart_5964565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964575 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 2, 4]
def baseStart_5964575 : Nat := 118140960795 + 5964575 * 2 ^ 59
def prefixEnd_5964575 : Nat := 4983230072969 + 3 ^ 40 * 5964575 * 2
def baseEnd_5964575 : Nat := 1020897958263702102193975

theorem tailTrace_5964575 : CollatzResearch.WordTrace tailWord_5964575 prefixEnd_5964575 1020897958263702102193975 := by
  unfold tailWord_5964575
  simp only [CollatzResearch.WordTrace]
  refine ⟨217545922366370918154783179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145030614910913945436522119 217545922366370918154783179)
  ·
    refine ⟨326318883549556377232174769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217545922366370918154783179 326318883549556377232174769)
    ·
      refine ⟨244739162662167282924131077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326318883549556377232174769 244739162662167282924131077)
      ·
        refine ⟨45888592999156365548274577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244739162662167282924131077 45888592999156365548274577)
        ·
          refine ⟨34416444749367274161205933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45888592999156365548274577 34416444749367274161205933)
          ·
            refine ⟨12906166781012727810452225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34416444749367274161205933 12906166781012727810452225)
            ·
              refine ⟨9679625085759545857839169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12906166781012727810452225 9679625085759545857839169)
              ·
                refine ⟨7259718814319659393379377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9679625085759545857839169 7259718814319659393379377)
                ·
                  refine ⟨5444789110739744545034533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7259718814319659393379377 5444789110739744545034533)
                  ·
                    refine ⟨1020897958263702102193975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5444789110739744545034533 1020897958263702102193975)
                    ·
                      rfl

theorem cell23_5964575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 4].length) (baseStart_5964575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964575 prefixEnd_5964575 := by exact prefixLift 5964575
  have htrace : WordTrace (prefixWord ++ tailWord_5964575) baseStart_5964575 baseEnd_5964575 := by
    simpa [prefixWord, tailWord_5964575, baseEnd_5964575] using wordTrace_append hprefix tailTrace_5964575
  have hstable : (prefixWord ++ tailWord_5964575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964575).length < 2 ^ (prefixWord ++ tailWord_5964575).sum := by decide
  have hdescent : baseEnd_5964575 < baseStart_5964575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964605 : List Nat := [1, 4, 1, 4, 2, 1, 3, 7]
def baseStart_5964605 : Nat := 118140960795 + 5964605 * 2 ^ 59
def prefixEnd_5964605 : Nat := 4983230072969 + 3 ^ 40 * 5964605 * 2
def baseEnd_5964605 : Nat := 113433677007805229229881

theorem tailTrace_5964605 : CollatzResearch.WordTrace tailWord_5964605 prefixEnd_5964605 113433677007805229229881 := by
  unfold tailWord_5964605
  simp only [CollatzResearch.WordTrace]
  refine ⟨217547016556262233278375269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145031344370841488852250179 217547016556262233278375269)
  ·
    refine ⟨40790065604299168739695363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217547016556262233278375269 40790065604299168739695363)
    ·
      refine ⟨61185098406448753109543045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40790065604299168739695363 61185098406448753109543045)
      ·
        refine ⟨11472205951209141208039321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61185098406448753109543045 11472205951209141208039321)
        ·
          refine ⟨8604154463406855906029491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11472205951209141208039321 8604154463406855906029491)
          ·
            refine ⟨12906231695110283859044237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8604154463406855906029491 12906231695110283859044237)
            ·
              refine ⟨4839836885666356447141589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12906231695110283859044237 4839836885666356447141589)
              ·
                refine ⟨113433677007805229229881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4839836885666356447141589 113433677007805229229881)
                ·
                  rfl

theorem cell23_5964605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 7].length) (baseStart_5964605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964605 prefixEnd_5964605 := by exact prefixLift 5964605
  have htrace : WordTrace (prefixWord ++ tailWord_5964605) baseStart_5964605 baseEnd_5964605 := by
    simpa [prefixWord, tailWord_5964605, baseEnd_5964605] using wordTrace_append hprefix tailTrace_5964605
  have hstable : (prefixWord ++ tailWord_5964605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964605).length < 2 ^ (prefixWord ++ tailWord_5964605).sum := by decide
  have hdescent : baseEnd_5964605 < baseStart_5964605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964611 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 5]
def baseStart_5964611 : Nat := 118140960795 + 5964611 * 2 ^ 59
def prefixEnd_5964611 : Nat := 4983230072969 + 3 ^ 40 * 5964611 * 2
def baseEnd_5964611 : Nat := 3062712360094668165731759

theorem tailTrace_5964611 : CollatzResearch.WordTrace tailWord_5964611 prefixEnd_5964611 3062712360094668165731759 := by
  unfold tailWord_5964611
  simp only [CollatzResearch.WordTrace]
  refine ⟨217547235394240496303093687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145031490262826997535395791 217547235394240496303093687)
  ·
    refine ⟨326320853091360744454640531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217547235394240496303093687 326320853091360744454640531)
    ·
      refine ⟨489481279637041116681960797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326320853091360744454640531 489481279637041116681960797)
      ·
        refine ⟨183555479863890418755735299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489481279637041116681960797 183555479863890418755735299)
        ·
          refine ⟨275333219795835628133602949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183555479863890418755735299 275333219795835628133602949)
          ·
            refine ⟨51624978711719180275050553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275333219795835628133602949 51624978711719180275050553)
            ·
              refine ⟨38718734033789385206287915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51624978711719180275050553 38718734033789385206287915)
              ·
                refine ⟨58078101050684077809431873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38718734033789385206287915 58078101050684077809431873)
                ·
                  refine ⟨43558575788013058357073905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58078101050684077809431873 43558575788013058357073905)
                  ·
                    refine ⟨32668931841009793767805429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43558575788013058357073905 32668931841009793767805429)
                    ·
                      refine ⟨3062712360094668165731759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32668931841009793767805429 3062712360094668165731759)
                      ·
                        rfl

theorem cell23_5964611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_5964611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964611 prefixEnd_5964611 := by exact prefixLift 5964611
  have htrace : WordTrace (prefixWord ++ tailWord_5964611) baseStart_5964611 baseEnd_5964611 := by
    simpa [prefixWord, tailWord_5964611, baseEnd_5964611] using wordTrace_append hprefix tailTrace_5964611
  have hstable : (prefixWord ++ tailWord_5964611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964611).length < 2 ^ (prefixWord ++ tailWord_5964611).sum := by decide
  have hdescent : baseEnd_5964611 < baseStart_5964611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964641 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_5964641 : Nat := 118140960795 + 5964641 * 2 ^ 59
def prefixEnd_5964641 : Nat := 4983230072969 + 3 ^ 40 * 5964641 * 2
def baseEnd_5964641 : Nat := 3062727764514303048356621

theorem tailTrace_5964641 : CollatzResearch.WordTrace tailWord_5964641 prefixEnd_5964641 3062727764514303048356621 := by
  unfold tailWord_5964641
  simp only [CollatzResearch.WordTrace]
  refine ⟨217548329584131811426685777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145032219722754540951123851 217548329584131811426685777)
  ·
    refine ⟨163161247188098858570014333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217548329584131811426685777 163161247188098858570014333)
    ·
      refine ⟨61185467695537071963755375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163161247188098858570014333 61185467695537071963755375)
      ·
        refine ⟨91778201543305607945633063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61185467695537071963755375 91778201543305607945633063)
        ·
          refine ⟨137667302314958411918449595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91778201543305607945633063 137667302314958411918449595)
          ·
            refine ⟨206500953472437617877674393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137667302314958411918449595 206500953472437617877674393)
            ·
              refine ⟨154875715104328213408255795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206500953472437617877674393 154875715104328213408255795)
              ·
                refine ⟨232313572656492320112383693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154875715104328213408255795 232313572656492320112383693)
                ·
                  refine ⟨87117589746184620042143885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 232313572656492320112383693 87117589746184620042143885)
                  ·
                    refine ⟨32669096154819232515803957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87117589746184620042143885 32669096154819232515803957)
                    ·
                      refine ⟨3062727764514303048356621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32669096154819232515803957 3062727764514303048356621)
                      ·
                        rfl

theorem cell23_5964641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_5964641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964641 prefixEnd_5964641 := by exact prefixLift 5964641
  have htrace : WordTrace (prefixWord ++ tailWord_5964641) baseStart_5964641 baseEnd_5964641 := by
    simpa [prefixWord, tailWord_5964641, baseEnd_5964641] using wordTrace_append hprefix tailTrace_5964641
  have hstable : (prefixWord ++ tailWord_5964641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964641).length < 2 ^ (prefixWord ++ tailWord_5964641).sum := by decide
  have hdescent : baseEnd_5964641 < baseStart_5964641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964648 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 2, 6]
def baseStart_5964648 : Nat := 118140960795 + 5964648 * 2 ^ 59
def prefixEnd_5964648 : Nat := 4983230072969 + 3 ^ 40 * 5964648 * 2
def baseEnd_5964648 : Nat := 1020910452959628173656363

theorem tailTrace_5964648 : CollatzResearch.WordTrace tailWord_5964648 prefixEnd_5964648 1020910452959628173656363 := by
  unfold tailWord_5964648
  simp only [CollatzResearch.WordTrace]
  refine ⟨108774292447553225811095299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145032389930070967748127065 108774292447553225811095299)
  ·
    refine ⟨163161438671329838716642949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108774292447553225811095299 163161438671329838716642949)
    ·
      refine ⟨30592769750874344759370553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163161438671329838716642949 30592769750874344759370553)
      ·
        refine ⟨22944577313155758569527915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30592769750874344759370553 22944577313155758569527915)
        ·
          refine ⟨34416865969733637854291873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22944577313155758569527915 34416865969733637854291873)
          ·
            refine ⟨25812649477300228390718905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34416865969733637854291873 25812649477300228390718905)
            ·
              refine ⟨19359487107975171293039179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25812649477300228390718905 19359487107975171293039179)
              ·
                refine ⟨29039230661962756939558769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19359487107975171293039179 29039230661962756939558769)
                ·
                  refine ⟨21779422996472067704669077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29039230661962756939558769 21779422996472067704669077)
                  ·
                    refine ⟨1020910452959628173656363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21779422996472067704669077 1020910452959628173656363)
                    ·
                      rfl

theorem cell23_5964648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_5964648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964648 prefixEnd_5964648 := by exact prefixLift 5964648
  have htrace : WordTrace (prefixWord ++ tailWord_5964648) baseStart_5964648 baseEnd_5964648 := by
    simpa [prefixWord, tailWord_5964648, baseEnd_5964648] using wordTrace_append hprefix tailTrace_5964648
  have hstable : (prefixWord ++ tailWord_5964648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964648).length < 2 ^ (prefixWord ++ tailWord_5964648).sum := by decide
  have hdescent : baseEnd_5964648 < baseStart_5964648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964658 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_5964658 : Nat := 118140960795 + 5964658 * 2 ^ 59
def prefixEnd_5964658 : Nat := 4983230072969 + 3 ^ 40 * 5964658 * 2
def baseEnd_5964658 : Nat := 3062736493685429481844043

theorem tailTrace_5964658 : CollatzResearch.WordTrace tailWord_5964658 prefixEnd_5964658 3062736493685429481844043 := by
  unfold tailWord_5964658
  simp only [CollatzResearch.WordTrace]
  refine ⟨54387237406267555832513657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145032633083380148886703085 54387237406267555832513657)
  ·
    refine ⟨40790428054700666874385243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54387237406267555832513657 40790428054700666874385243)
    ·
      refine ⟨61185642082051000311577865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40790428054700666874385243 61185642082051000311577865)
      ·
        refine ⟨45889231561538250233683399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61185642082051000311577865 45889231561538250233683399)
        ·
          refine ⟨68833847342307375350525099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45889231561538250233683399 68833847342307375350525099)
          ·
            refine ⟨103250771013461063025787649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68833847342307375350525099 103250771013461063025787649)
            ·
              refine ⟨77438078260095797269340737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103250771013461063025787649 77438078260095797269340737)
              ·
                refine ⟨58078558695071847952005553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77438078260095797269340737 58078558695071847952005553)
                ·
                  refine ⟨43558919021303885964004165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58078558695071847952005553 43558919021303885964004165)
                  ·
                    refine ⟨8167297316494478618250781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43558919021303885964004165 8167297316494478618250781)
                    ·
                      refine ⟨3062736493685429481844043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8167297316494478618250781 3062736493685429481844043)
                      ·
                        rfl

theorem cell23_5964658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_5964658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964658 prefixEnd_5964658 := by exact prefixLift 5964658
  have htrace : WordTrace (prefixWord ++ tailWord_5964658) baseStart_5964658 baseEnd_5964658 := by
    simpa [prefixWord, tailWord_5964658, baseEnd_5964658] using wordTrace_append hprefix tailTrace_5964658
  have hstable : (prefixWord ++ tailWord_5964658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964658).length < 2 ^ (prefixWord ++ tailWord_5964658).sum := by decide
  have hdescent : baseEnd_5964658 < baseStart_5964658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964691 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 3, 7]
def baseStart_5964691 : Nat := 118140960795 + 5964691 * 2 ^ 59
def prefixEnd_5964691 : Nat := 4983230072969 + 3 ^ 40 * 5964691 * 2
def baseEnd_5964691 : Nat := 1020917812849009284243797

theorem tailTrace_5964691 : CollatzResearch.WordTrace tailWord_5964691 prefixEnd_5964691 1020917812849009284243797 := by
  unfold tailWord_5964691
  simp only [CollatzResearch.WordTrace]
  refine ⟨217550153233950669966005927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145033435489300446644003951 217550153233950669966005927)
  ·
    refine ⟨326325229850926004949008891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217550153233950669966005927 326325229850926004949008891)
    ·
      refine ⟨489487844776389007423513337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326325229850926004949008891 489487844776389007423513337)
      ·
        refine ⟨367115883582291755567635003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489487844776389007423513337 367115883582291755567635003)
        ·
          refine ⟨550673825373437633351452505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367115883582291755567635003 550673825373437633351452505)
          ·
            refine ⟨413005369030078225013589379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550673825373437633351452505 413005369030078225013589379)
            ·
              refine ⟨619508053545117337520384069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413005369030078225013589379 619508053545117337520384069)
              ·
                refine ⟨116157760039709500785072013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619508053545117337520384069 116157760039709500785072013)
                ·
                  refine ⟨43559160014891062794402005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116157760039709500785072013 43559160014891062794402005)
                  ·
                    refine ⟨1020917812849009284243797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43559160014891062794402005 1020917812849009284243797)
                    ·
                      rfl

theorem cell23_5964691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 7].length) (baseStart_5964691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964691 prefixEnd_5964691 := by exact prefixLift 5964691
  have htrace : WordTrace (prefixWord ++ tailWord_5964691) baseStart_5964691 baseEnd_5964691 := by
    simpa [prefixWord, tailWord_5964691, baseEnd_5964691] using wordTrace_append hprefix tailTrace_5964691
  have hstable : (prefixWord ++ tailWord_5964691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964691).length < 2 ^ (prefixWord ++ tailWord_5964691).sum := by decide
  have hdescent : baseEnd_5964691 < baseStart_5964691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964706 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_5964706 : Nat := 118140960795 + 5964706 * 2 ^ 59
def prefixEnd_5964706 : Nat := 4983230072969 + 3 ^ 40 * 5964706 * 2
def baseEnd_5964706 : Nat := 3062761140756845294043823

theorem tailTrace_5964706 : CollatzResearch.WordTrace tailWord_5964706 prefixEnd_5964706 3062761140756845294043823 := by
  unfold tailWord_5964706
  simp only [CollatzResearch.WordTrace]
  refine ⟨54387675082224081881950493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145033800219264218351867981 54387675082224081881950493)
  ·
    refine ⟨20395378155834030705731435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54387675082224081881950493 20395378155834030705731435)
    ·
      refine ⟨30593067233751046058597153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20395378155834030705731435 30593067233751046058597153)
      ·
        refine ⟨22944800425313284543947865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30593067233751046058597153 22944800425313284543947865)
        ·
          refine ⟨17208600318984963407960899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22944800425313284543947865 17208600318984963407960899)
          ·
            refine ⟨25812900478477445111941349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17208600318984963407960899 25812900478477445111941349)
            ·
              refine ⟨4839918839714520958489003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25812900478477445111941349 4839918839714520958489003)
              ·
                refine ⟨7259878259571781437733505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839918839714520958489003 7259878259571781437733505)
                ·
                  refine ⟨5444908694678836078300129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7259878259571781437733505 5444908694678836078300129)
                  ·
                    refine ⟨4083681521009127058725097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5444908694678836078300129 4083681521009127058725097)
                    ·
                      refine ⟨3062761140756845294043823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083681521009127058725097 3062761140756845294043823)
                      ·
                        rfl

theorem cell23_5964706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_5964706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964706 prefixEnd_5964706 := by exact prefixLift 5964706
  have htrace : WordTrace (prefixWord ++ tailWord_5964706) baseStart_5964706 baseEnd_5964706 := by
    simpa [prefixWord, tailWord_5964706, baseEnd_5964706] using wordTrace_append hprefix tailTrace_5964706
  have hstable : (prefixWord ++ tailWord_5964706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964706).length < 2 ^ (prefixWord ++ tailWord_5964706).sum := by decide
  have hdescent : baseEnd_5964706 < baseStart_5964706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964708 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_5964708 : Nat := 118140960795 + 5964708 * 2 ^ 59
def prefixEnd_5964708 : Nat := 4983230072969 + 3 ^ 40 * 5964708 * 2
def baseEnd_5964708 : Nat := 1020920722572718095406271

theorem tailTrace_5964708 : CollatzResearch.WordTrace tailWord_5964708 prefixEnd_5964708 1020920722572718095406271 := by
  unfold tailWord_5964708
  simp only [CollatzResearch.WordTrace]
  refine ⟨108775386637444540934687389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145033848849926054579583185 108775386637444540934687389)
  ·
    refine ⟨40790769989041702850507771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108775386637444540934687389 40790769989041702850507771)
    ·
      refine ⟨61186154983562554275761657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40790769989041702850507771 61186154983562554275761657)
      ·
        refine ⟨45889616237671915706821243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61186154983562554275761657 45889616237671915706821243)
        ·
          refine ⟨68834424356507873560231865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45889616237671915706821243 68834424356507873560231865)
          ·
            refine ⟨51625818267380905170173899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68834424356507873560231865 51625818267380905170173899)
            ·
              refine ⟨77438727401071357755260849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51625818267380905170173899 77438727401071357755260849)
              ·
                refine ⟨58079045550803518316445637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77438727401071357755260849 58079045550803518316445637)
                ·
                  refine ⟨10889821040775659684333557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58079045550803518316445637 10889821040775659684333557)
                  ·
                    refine ⟨1020920722572718095406271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10889821040775659684333557 1020920722572718095406271)
                    ·
                      rfl

theorem cell23_5964708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_5964708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964708 prefixEnd_5964708 := by exact prefixLift 5964708
  have htrace : WordTrace (prefixWord ++ tailWord_5964708) baseStart_5964708 baseEnd_5964708 := by
    simpa [prefixWord, tailWord_5964708, baseEnd_5964708] using wordTrace_append hprefix tailTrace_5964708
  have hstable : (prefixWord ++ tailWord_5964708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964708).length < 2 ^ (prefixWord ++ tailWord_5964708).sum := by decide
  have hdescent : baseEnd_5964708 < baseStart_5964708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964725 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_5964725 : Nat := 118140960795 + 5964725 * 2 ^ 59
def prefixEnd_5964725 : Nat := 4983230072969 + 3 ^ 40 * 5964725 * 2
def baseEnd_5964725 : Nat := 1020923632296426906568745

theorem tailTrace_5964725 : CollatzResearch.WordTrace tailWord_5964725 prefixEnd_5964725 1020923632296426906568745 := by
  unfold tailWord_5964725
  simp only [CollatzResearch.WordTrace]
  refine ⟨217551393315827493772743629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145034262210551662515162419 217551393315827493772743629)
  ·
    refine ⟨81581772493435310164778861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217551393315827493772743629 81581772493435310164778861)
    ·
      refine ⟨30593164685038241311792073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81581772493435310164778861 30593164685038241311792073)
      ·
        refine ⟨22944873513778680983844055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30593164685038241311792073 22944873513778680983844055)
        ·
          refine ⟨34417310270668021475766083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22944873513778680983844055 34417310270668021475766083)
          ·
            refine ⟨51625965406002032213649125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34417310270668021475766083 51625965406002032213649125)
            ·
              refine ⟨9679868513625381040059211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51625965406002032213649125 9679868513625381040059211)
              ·
                refine ⟨14519802770438071560088817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9679868513625381040059211 14519802770438071560088817)
                ·
                  refine ⟨10889852077828553670066613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14519802770438071560088817 10889852077828553670066613)
                  ·
                    refine ⟨1020923632296426906568745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10889852077828553670066613 1020923632296426906568745)
                    ·
                      rfl

theorem cell23_5964725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_5964725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964725 prefixEnd_5964725 := by exact prefixLift 5964725
  have htrace : WordTrace (prefixWord ++ tailWord_5964725) baseStart_5964725 baseEnd_5964725 := by
    simpa [prefixWord, tailWord_5964725, baseEnd_5964725] using wordTrace_append hprefix tailTrace_5964725
  have hstable : (prefixWord ++ tailWord_5964725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964725).length < 2 ^ (prefixWord ++ tailWord_5964725).sum := by decide
  have hdescent : baseEnd_5964725 < baseStart_5964725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964748 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5964748 : Nat := 118140960795 + 5964748 * 2 ^ 59
def prefixEnd_5964748 : Nat := 4983230072969 + 3 ^ 40 * 5964748 * 2
def baseEnd_5964748 : Nat := 3062782706944334129718629

theorem tailTrace_5964748 : CollatzResearch.WordTrace tailWord_5964748 prefixEnd_5964748 3062782706944334129718629 := by
  unfold tailWord_5964748
  simp only [CollatzResearch.WordTrace]
  refine ⟨108776116097372084350415449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145034821463162779133887265 108776116097372084350415449)
  ·
    refine ⟨81582087073029063262811587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108776116097372084350415449 81582087073029063262811587)
    ·
      refine ⟨122373130609543594894217381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81582087073029063262811587 122373130609543594894217381)
      ·
        refine ⟨22944961989289424042665759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122373130609543594894217381 22944961989289424042665759)
        ·
          refine ⟨34417442983934136063998639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22944961989289424042665759 34417442983934136063998639)
          ·
            refine ⟨51626164475901204095997959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34417442983934136063998639 51626164475901204095997959)
            ·
              refine ⟨77439246713851806143996939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51626164475901204095997959 77439246713851806143996939)
              ·
                refine ⟨116158870070777709215995409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77439246713851806143996939 116158870070777709215995409)
                ·
                  refine ⟨87119152553083281911996557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116158870070777709215995409 87119152553083281911996557)
                  ·
                    refine ⟨32669682207406230716998709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87119152553083281911996557 32669682207406230716998709)
                    ·
                      refine ⟨3062782706944334129718629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32669682207406230716998709 3062782706944334129718629)
                      ·
                        rfl

theorem cell23_5964748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5964748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964748 prefixEnd_5964748 := by exact prefixLift 5964748
  have htrace : WordTrace (prefixWord ++ tailWord_5964748) baseStart_5964748 baseEnd_5964748 := by
    simpa [prefixWord, tailWord_5964748, baseEnd_5964748] using wordTrace_append hprefix tailTrace_5964748
  have hstable : (prefixWord ++ tailWord_5964748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964748).length < 2 ^ (prefixWord ++ tailWord_5964748).sum := by decide
  have hdescent : baseEnd_5964748 < baseStart_5964748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964762 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2]
def baseStart_5964762 : Nat := 118140960795 + 5964762 * 2 ^ 59
def prefixEnd_5964762 : Nat := 4983230072969 + 3 ^ 40 * 5964762 * 2
def baseEnd_5964762 : Nat := 3062789895673497074943565

theorem tailTrace_5964762 : CollatzResearch.WordTrace tailWord_5964762 prefixEnd_5964762 3062789895673497074943565 := by
  unfold tailWord_5964762
  simp only [CollatzResearch.WordTrace]
  refine ⟨54388185704173362272960135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145035161877795632727893693 54388185704173362272960135)
  ·
    refine ⟨81582278556260043409440203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54388185704173362272960135 81582278556260043409440203)
    ·
      refine ⟨122373417834390065114160305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81582278556260043409440203 122373417834390065114160305)
      ·
        refine ⟨91780063375792548835620229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122373417834390065114160305 91780063375792548835620229)
        ·
          refine ⟨17208761882961102906678793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91780063375792548835620229 17208761882961102906678793)
          ·
            refine ⟨12906571412220827180009095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17208761882961102906678793 12906571412220827180009095)
            ·
              refine ⟨19359857118331240770013643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12906571412220827180009095 19359857118331240770013643)
              ·
                refine ⟨29039785677496861155020465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19359857118331240770013643 29039785677496861155020465)
                ·
                  refine ⟨21779839258122645866265349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29039785677496861155020465 21779839258122645866265349)
                  ·
                    refine ⟨4083719860897996099924753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21779839258122645866265349 4083719860897996099924753)
                    ·
                      refine ⟨3062789895673497074943565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083719860897996099924753 3062789895673497074943565)
                      ·
                        rfl

theorem cell23_5964762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_5964762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964762 prefixEnd_5964762 := by exact prefixLift 5964762
  have htrace : WordTrace (prefixWord ++ tailWord_5964762) baseStart_5964762 baseEnd_5964762 := by
    simpa [prefixWord, tailWord_5964762, baseEnd_5964762] using wordTrace_append hprefix tailTrace_5964762
  have hstable : (prefixWord ++ tailWord_5964762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964762).length < 2 ^ (prefixWord ++ tailWord_5964762).sum := by decide
  have hdescent : baseEnd_5964762 < baseStart_5964762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964782 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_5964782 : Nat := 118140960795 + 5964782 * 2 ^ 59
def prefixEnd_5964782 : Nat := 4983230072969 + 3 ^ 40 * 5964782 * 2
def baseEnd_5964782 : Nat := 3062800165286586996693473

theorem tailTrace_5964782 : CollatzResearch.WordTrace tailWord_5964782 prefixEnd_5964782 3062800165286586996693473 := by
  unfold tailWord_5964782
  simp only [CollatzResearch.WordTrace]
  refine ⟨27194184034577624063446075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145035648184413995005045733 27194184034577624063446075)
  ·
    refine ⟨40791276051866436095169113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27194184034577624063446075 40791276051866436095169113)
    ·
      refine ⟨30593457038899827071376835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40791276051866436095169113 30593457038899827071376835)
      ·
        refine ⟨45890185558349740607065253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30593457038899827071376835 45890185558349740607065253)
        ·
          refine ⟨8604409792190576363824735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45890185558349740607065253 8604409792190576363824735)
          ·
            refine ⟨12906614688285864545737103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8604409792190576363824735 12906614688285864545737103)
            ·
              refine ⟨19359922032428796818605655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12906614688285864545737103 19359922032428796818605655)
              ·
                refine ⟨29039883048643195227908483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19359922032428796818605655 29039883048643195227908483)
                ·
                  refine ⟨43559824572964792841862725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29039883048643195227908483 43559824572964792841862725)
                  ·
                    refine ⟨8167467107430898657849261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43559824572964792841862725 8167467107430898657849261)
                    ·
                      refine ⟨3062800165286586996693473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8167467107430898657849261 3062800165286586996693473)
                      ·
                        rfl

theorem cell23_5964782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_5964782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964782 prefixEnd_5964782 := by exact prefixLift 5964782
  have htrace : WordTrace (prefixWord ++ tailWord_5964782) baseStart_5964782 baseEnd_5964782 := by
    simpa [prefixWord, tailWord_5964782, baseEnd_5964782] using wordTrace_append hprefix tailTrace_5964782
  have hstable : (prefixWord ++ tailWord_5964782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964782).length < 2 ^ (prefixWord ++ tailWord_5964782).sum := by decide
  have hdescent : baseEnd_5964782 < baseStart_5964782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964795 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 3]
def baseStart_5964795 : Nat := 118140960795 + 5964795 * 2 ^ 59
def prefixEnd_5964795 : Nat := 4983230072969 + 3 ^ 40 * 5964795 * 2
def baseEnd_5964795 : Nat := 3062806840535095445830913

theorem tailTrace_5964795 : CollatzResearch.WordTrace tailWord_5964795 prefixEnd_5964795 3062806840535095445830913 := by
  unfold tailWord_5964795
  simp only [CollatzResearch.WordTrace]
  refine ⟨217553946425573895727791839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145035964283715930485194559 217553946425573895727791839)
  ·
    refine ⟨326330919638360843591687759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217553946425573895727791839 326330919638360843591687759)
    ·
      refine ⟨489496379457541265387531639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326330919638360843591687759 489496379457541265387531639)
      ·
        refine ⟨734244569186311898081297459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489496379457541265387531639 734244569186311898081297459)
        ·
          refine ⟨1101366853779467847121946189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734244569186311898081297459 1101366853779467847121946189)
          ·
            refine ⟨413012570167300442670729821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1101366853779467847121946189 413012570167300442670729821)
            ·
              refine ⟨154879713812737666001523683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413012570167300442670729821 154879713812737666001523683)
              ·
                refine ⟨232319570719106499002285525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154879713812737666001523683 232319570719106499002285525)
                ·
                  refine ⟨5444989938729058570366067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 232319570719106499002285525 5444989938729058570366067)
                  ·
                    refine ⟨8167484908093587855549101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5444989938729058570366067 8167484908093587855549101)
                    ·
                      refine ⟨3062806840535095445830913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8167484908093587855549101 3062806840535095445830913)
                      ·
                        rfl

theorem cell23_5964795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 1, 3].length) (baseStart_5964795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964795 prefixEnd_5964795 := by exact prefixLift 5964795
  have htrace : WordTrace (prefixWord ++ tailWord_5964795) baseStart_5964795 baseEnd_5964795 := by
    simpa [prefixWord, tailWord_5964795, baseEnd_5964795] using wordTrace_append hprefix tailTrace_5964795
  have hstable : (prefixWord ++ tailWord_5964795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964795).length < 2 ^ (prefixWord ++ tailWord_5964795).sum := by decide
  have hdescent : baseEnd_5964795 < baseStart_5964795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964812 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 3, 1, 3]
def baseStart_5964812 : Nat := 118140960795 + 5964812 * 2 ^ 59
def prefixEnd_5964812 : Nat := 4983230072969 + 3 ^ 40 * 5964812 * 2
def baseEnd_5964812 : Nat := 3062815569706221879318335

theorem tailTrace_5964812 : CollatzResearch.WordTrace tailWord_5964812 prefixEnd_5964812 3062815569706221879318335 := by
  unfold tailWord_5964812
  simp only [CollatzResearch.WordTrace]
  refine ⟨108777283233256153815580345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145036377644341538420773793 108777283233256153815580345)
  ·
    refine ⟨81582962424942115361685259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108777283233256153815580345 81582962424942115361685259)
    ·
      refine ⟨122374443637413173042527889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81582962424942115361685259 122374443637413173042527889)
      ·
        refine ⟨91780832728059879781895917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122374443637413173042527889 91780832728059879781895917)
        ·
          refine ⟨34417812273022454918210969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91780832728059879781895917 34417812273022454918210969)
          ·
            refine ⟨25813359204766841188658227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34417812273022454918210969 25813359204766841188658227)
            ·
              refine ⟨38720038807150261782987341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25813359204766841188658227 38720038807150261782987341)
              ·
                refine ⟨14520014552681348168620253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38720038807150261782987341 14520014552681348168620253)
                ·
                  refine ⟨5445005457255505563232595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14520014552681348168620253 5445005457255505563232595)
                  ·
                    refine ⟨8167508185883258344848893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5445005457255505563232595 8167508185883258344848893)
                    ·
                      refine ⟨3062815569706221879318335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8167508185883258344848893 3062815569706221879318335)
                      ·
                        rfl

theorem cell23_5964812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_5964812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964812 prefixEnd_5964812 := by exact prefixLift 5964812
  have htrace : WordTrace (prefixWord ++ tailWord_5964812) baseStart_5964812 baseEnd_5964812 := by
    simpa [prefixWord, tailWord_5964812, baseEnd_5964812] using wordTrace_append hprefix tailTrace_5964812
  have hstable : (prefixWord ++ tailWord_5964812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964812).length < 2 ^ (prefixWord ++ tailWord_5964812).sum := by decide
  have hdescent : baseEnd_5964812 < baseStart_5964812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964839 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_5964839 : Nat := 118140960795 + 5964839 * 2 ^ 59
def prefixEnd_5964839 : Nat := 4983230072969 + 3 ^ 40 * 5964839 * 2
def baseEnd_5964839 : Nat := 3062829433683893273680711

theorem tailTrace_5964839 : CollatzResearch.WordTrace tailWord_5964839 prefixEnd_5964839 3062829433683893273680711 := by
  unfold tailWord_5964839
  simp only [CollatzResearch.WordTrace]
  refine ⟨217555551237414491242393571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145037034158276327494929047 217555551237414491242393571)
  ·
    refine ⟨326333326856121736863590357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217555551237414491242393571 326333326856121736863590357)
    ·
      refine ⟨7648437348190353207740399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 326333326856121736863590357 7648437348190353207740399)
      ·
        refine ⟨11472656022285529811610599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7648437348190353207740399 11472656022285529811610599)
        ·
          refine ⟨17208984033428294717415899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11472656022285529811610599 17208984033428294717415899)
          ·
            refine ⟨25813476050142442076123849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17208984033428294717415899 25813476050142442076123849)
            ·
              refine ⟨19360107037606831557092887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25813476050142442076123849 19360107037606831557092887)
              ·
                refine ⟨29040160556410247335639331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19360107037606831557092887 29040160556410247335639331)
                ·
                  refine ⟨43560240834615371003458997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29040160556410247335639331 43560240834615371003458997)
                  ·
                    refine ⟨4083772578245191031574281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43560240834615371003458997 4083772578245191031574281)
                    ·
                      refine ⟨3062829433683893273680711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083772578245191031574281 3062829433683893273680711)
                      ·
                        rfl

theorem cell23_5964839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_5964839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964839 prefixEnd_5964839 := by exact prefixLift 5964839
  have htrace : WordTrace (prefixWord ++ tailWord_5964839) baseStart_5964839 baseEnd_5964839 := by
    simpa [prefixWord, tailWord_5964839, baseEnd_5964839] using wordTrace_append hprefix tailTrace_5964839
  have hstable : (prefixWord ++ tailWord_5964839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964839).length < 2 ^ (prefixWord ++ tailWord_5964839).sum := by decide
  have hdescent : baseEnd_5964839 < baseStart_5964839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964855 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_5964855 : Nat := 118140960795 + 5964855 * 2 ^ 59
def prefixEnd_5964855 : Nat := 4983230072969 + 3 ^ 40 * 5964855 * 2
def baseEnd_5964855 : Nat := 3062837649374365211080637

theorem tailTrace_5964855 : CollatzResearch.WordTrace tailWord_5964855 prefixEnd_5964855 3062837649374365211080637 := by
  unfold tailWord_5964855
  simp only [CollatzResearch.WordTrace]
  refine ⟨217556134805356525974976019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145037423203571017316650679 217556134805356525974976019)
  ·
    refine ⟨326334202208034788962464029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217556134805356525974976019 326334202208034788962464029)
    ·
      refine ⟨122375325828013045860924011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326334202208034788962464029 122375325828013045860924011)
      ·
        refine ⟨183562988742019568791386017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122375325828013045860924011 183562988742019568791386017)
        ·
          refine ⟨137672241556514676593539513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183562988742019568791386017 137672241556514676593539513)
          ·
            refine ⟨103254181167386007445154635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137672241556514676593539513 103254181167386007445154635)
            ·
              refine ⟨154881271751079011167731953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103254181167386007445154635 154881271751079011167731953)
              ·
                refine ⟨116160953813309258375798965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154881271751079011167731953 116160953813309258375798965)
                ·
                  refine ⟨10890089419997742972731153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116160953813309258375798965 10890089419997742972731153)
                  ·
                    refine ⟨8167567064998307229548365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10890089419997742972731153 8167567064998307229548365)
                    ·
                      refine ⟨3062837649374365211080637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8167567064998307229548365 3062837649374365211080637)
                      ·
                        rfl

theorem cell23_5964855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_5964855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964855 prefixEnd_5964855 := by exact prefixLift 5964855
  have htrace : WordTrace (prefixWord ++ tailWord_5964855) baseStart_5964855 baseEnd_5964855 := by
    simpa [prefixWord, tailWord_5964855, baseEnd_5964855] using wordTrace_append hprefix tailTrace_5964855
  have hstable : (prefixWord ++ tailWord_5964855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964855).length < 2 ^ (prefixWord ++ tailWord_5964855).sum := by decide
  have hdescent : baseEnd_5964855 < baseStart_5964855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964858 : List Nat := [3, 1, 1, 1, 3, 1, 13]
def baseStart_5964858 : Nat := 118140960795 + 5964858 * 2 ^ 59
def prefixEnd_5964858 : Nat := 4983230072969 + 3 ^ 40 * 5964858 * 2
def baseEnd_5964858 : Nat := 37812829503905292584483

theorem tailTrace_5964858 : CollatzResearch.WordTrace tailWord_5964858 prefixEnd_5964858 37812829503905292584483 := by
  unfold tailWord_5964858
  simp only [CollatzResearch.WordTrace]
  refine ⟨54389061056086414371833807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145037496149563771658223485 54389061056086414371833807)
  ·
    refine ⟨81583591584129621557750711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54389061056086414371833807 81583591584129621557750711)
    ·
      refine ⟨122375387376194432336626067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81583591584129621557750711 122375387376194432336626067)
      ·
        refine ⟨183563081064291648504939101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122375387376194432336626067 183563081064291648504939101)
        ·
          refine ⟨68836155399109368189352163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183563081064291648504939101 68836155399109368189352163)
          ·
            refine ⟨103254233098664052284028245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68836155399109368189352163 103254233098664052284028245)
            ·
              refine ⟨37812829503905292584483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 103254233098664052284028245 37812829503905292584483)
              ·
                rfl

theorem cell23_5964858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 13].length) (baseStart_5964858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964858 prefixEnd_5964858 := by exact prefixLift 5964858
  have htrace : WordTrace (prefixWord ++ tailWord_5964858) baseStart_5964858 baseEnd_5964858 := by
    simpa [prefixWord, tailWord_5964858, baseEnd_5964858] using wordTrace_append hprefix tailTrace_5964858
  have hstable : (prefixWord ++ tailWord_5964858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964858).length < 2 ^ (prefixWord ++ tailWord_5964858).sum := by decide
  have hdescent : baseEnd_5964858 < baseStart_5964858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964869 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 3, 2, 2]
def baseStart_5964869 : Nat := 118140960795 + 5964869 * 2 ^ 59
def prefixEnd_5964869 : Nat := 4983230072969 + 3 ^ 40 * 5964869 * 2
def baseEnd_5964869 : Nat := 3062844838103528156305573

theorem tailTrace_5964869 : CollatzResearch.WordTrace tailWord_5964869 prefixEnd_5964869 3062844838103528156305573 := by
  unfold tailWord_5964869
  simp only [CollatzResearch.WordTrace]
  refine ⟨217556645427305806365985661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145037763618203870910657107 217556645427305806365985661)
  ·
    refine ⟨81583742035239677387244623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217556645427305806365985661 81583742035239677387244623)
    ·
      refine ⟨122375613052859516080866935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81583742035239677387244623 122375613052859516080866935)
      ·
        refine ⟨183563419579289274121300403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122375613052859516080866935 183563419579289274121300403)
        ·
          refine ⟨275345129368933911181950605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183563419579289274121300403 275345129368933911181950605)
          ·
            refine ⟨103254423513350216693231477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275345129368933911181950605 103254423513350216693231477)
            ·
              refine ⟨9680102204376582814990451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103254423513350216693231477 9680102204376582814990451)
              ·
                refine ⟨14520153306564874222485677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9680102204376582814990451 14520153306564874222485677)
                ·
                  refine ⟨5445057489961827833432129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14520153306564874222485677 5445057489961827833432129)
                  ·
                    refine ⟨4083793117471370875074097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5445057489961827833432129 4083793117471370875074097)
                    ·
                      refine ⟨3062844838103528156305573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083793117471370875074097 3062844838103528156305573)
                      ·
                        rfl

theorem cell23_5964869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_5964869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964869 prefixEnd_5964869 := by exact prefixLift 5964869
  have htrace : WordTrace (prefixWord ++ tailWord_5964869) baseStart_5964869 baseEnd_5964869 := by
    simpa [prefixWord, tailWord_5964869, baseEnd_5964869] using wordTrace_append hprefix tailTrace_5964869
  have hstable : (prefixWord ++ tailWord_5964869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964869).length < 2 ^ (prefixWord ++ tailWord_5964869).sum := by decide
  have hdescent : baseEnd_5964869 < baseStart_5964869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964886 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_5964886 : Nat := 118140960795 + 5964886 * 2 ^ 59
def prefixEnd_5964886 : Nat := 4983230072969 + 3 ^ 40 * 5964886 * 2
def baseEnd_5964886 : Nat := 3062853567274654589792995

theorem tailTrace_5964886 : CollatzResearch.WordTrace tailWord_5964886 prefixEnd_5964886 3062853567274654589792995 := by
  unfold tailWord_5964886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13597329091765263641834657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145038176978829478846236341 13597329091765263641834657)
  ·
    refine ⟨10197996818823947731375993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13597329091765263641834657 10197996818823947731375993)
    ·
      refine ⟨7648497614117960798531995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10197996818823947731375993 7648497614117960798531995)
      ·
        refine ⟨11472746421176941197797993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7648497614117960798531995 11472746421176941197797993)
        ·
          refine ⟨8604559815882705898348495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11472746421176941197797993 8604559815882705898348495)
          ·
            refine ⟨12906839723824058847522743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8604559815882705898348495 12906839723824058847522743)
            ·
              refine ⟨19360259585736088271284115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12906839723824058847522743 19360259585736088271284115)
              ·
                refine ⟨29040389378604132406926173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19360259585736088271284115 29040389378604132406926173)
                ·
                  refine ⟨10890146016976549652597315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29040389378604132406926173 10890146016976549652597315)
                  ·
                    refine ⟨16335219025464824478895973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10890146016976549652597315 16335219025464824478895973)
                    ·
                      refine ⟨3062853567274654589792995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16335219025464824478895973 3062853567274654589792995)
                      ·
                        rfl

theorem cell23_5964886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_5964886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964886 prefixEnd_5964886 := by exact prefixLift 5964886
  have htrace : WordTrace (prefixWord ++ tailWord_5964886) baseStart_5964886 baseEnd_5964886 := by
    simpa [prefixWord, tailWord_5964886, baseEnd_5964886] using wordTrace_append hprefix tailTrace_5964886
  have hstable : (prefixWord ++ tailWord_5964886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964886).length < 2 ^ (prefixWord ++ tailWord_5964886).sum := by decide
  have hdescent : baseEnd_5964886 < baseStart_5964886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964906 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_5964906 : Nat := 118140960795 + 5964906 * 2 ^ 59
def prefixEnd_5964906 : Nat := 4983230072969 + 3 ^ 40 * 5964906 * 2
def baseEnd_5964906 : Nat := 3062863836887744511542903

theorem tailTrace_5964906 : CollatzResearch.WordTrace tailWord_5964906 prefixEnd_5964906 3062863836887744511542903 := by
  unfold tailWord_5964906
  simp only [CollatzResearch.WordTrace]
  refine ⟨54389498732042940421270643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145038663285447841123388381 54389498732042940421270643)
  ·
    refine ⟨81584248098064410631905965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54389498732042940421270643 81584248098064410631905965)
    ·
      refine ⟨30594093036774153986964737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81584248098064410631905965 30594093036774153986964737)
      ·
        refine ⟨22945569777580615490223553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30594093036774153986964737 22945569777580615490223553)
        ·
          refine ⟨17209177333185461617667665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22945569777580615490223553 17209177333185461617667665)
          ·
            refine ⟨12906882999889096213250749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17209177333185461617667665 12906882999889096213250749)
            ·
              refine ⟨4840081124958411079969031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12906882999889096213250749 4840081124958411079969031)
              ·
                refine ⟨7260121687437616619953547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4840081124958411079969031 7260121687437616619953547)
                ·
                  refine ⟨10890182531156424929930321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7260121687437616619953547 10890182531156424929930321)
                  ·
                    refine ⟨8167636898367318697447741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10890182531156424929930321 8167636898367318697447741)
                    ·
                      refine ⟨3062863836887744511542903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8167636898367318697447741 3062863836887744511542903)
                      ·
                        rfl

theorem cell23_5964906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_5964906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964906 prefixEnd_5964906 := by exact prefixLift 5964906
  have htrace : WordTrace (prefixWord ++ tailWord_5964906) baseStart_5964906 baseEnd_5964906 := by
    simpa [prefixWord, tailWord_5964906, baseEnd_5964906] using wordTrace_append hprefix tailTrace_5964906
  have hstable : (prefixWord ++ tailWord_5964906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964906).length < 2 ^ (prefixWord ++ tailWord_5964906).sum := by decide
  have hdescent : baseEnd_5964906 < baseStart_5964906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964919 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 3]
def baseStart_5964919 : Nat := 118140960795 + 5964919 * 2 ^ 59
def prefixEnd_5964919 : Nat := 4983230072969 + 3 ^ 40 * 5964919 * 2
def baseEnd_5964919 : Nat := 3062870512136252960680343

theorem tailTrace_5964919 : CollatzResearch.WordTrace tailWord_5964919 prefixEnd_5964919 3062870512136252960680343 := by
  unfold tailWord_5964919
  simp only [CollatzResearch.WordTrace]
  refine ⟨217558469077124664905305811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145038979384749776603537207 217558469077124664905305811)
  ·
    refine ⟨326337703615686997357958717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217558469077124664905305811 326337703615686997357958717)
    ·
      refine ⟨122376638855882624009234519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326337703615686997357958717 122376638855882624009234519)
      ·
        refine ⟨183564958283823936013851779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122376638855882624009234519 183564958283823936013851779)
        ·
          refine ⟨275347437425735904020777669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183564958283823936013851779 275347437425735904020777669)
          ·
            refine ⟨51627644517325482003895813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275347437425735904020777669 51627644517325482003895813)
            ·
              refine ⟨9680183346998527875730465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51627644517325482003895813 9680183346998527875730465)
              ·
                refine ⟨7260137510248895906797849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9680183346998527875730465 7260137510248895906797849)
                ·
                  refine ⟨5445103132686671930098387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7260137510248895906797849 5445103132686671930098387)
                  ·
                    refine ⟨8167654699030007895147581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5445103132686671930098387 8167654699030007895147581)
                    ·
                      refine ⟨3062870512136252960680343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8167654699030007895147581 3062870512136252960680343)
                      ·
                        rfl

theorem cell23_5964919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_5964919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964919 prefixEnd_5964919 := by exact prefixLift 5964919
  have htrace : WordTrace (prefixWord ++ tailWord_5964919) baseStart_5964919 baseEnd_5964919 := by
    simpa [prefixWord, tailWord_5964919, baseEnd_5964919] using wordTrace_append hprefix tailTrace_5964919
  have hstable : (prefixWord ++ tailWord_5964919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964919).length < 2 ^ (prefixWord ++ tailWord_5964919).sum := by decide
  have hdescent : baseEnd_5964919 < baseStart_5964919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964925 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_5964925 : Nat := 118140960795 + 5964925 * 2 ^ 59
def prefixEnd_5964925 : Nat := 4983230072969 + 3 ^ 40 * 5964925 * 2
def baseEnd_5964925 : Nat := 3062873593020179937205315

theorem tailTrace_5964925 : CollatzResearch.WordTrace tailWord_5964925 prefixEnd_5964925 3062873593020179937205315 := by
  unfold tailWord_5964925
  simp only [CollatzResearch.WordTrace]
  refine ⟨217558687915102927930024229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145039125276735285286682819 217558687915102927930024229)
  ·
    refine ⟨40792253984081798986879543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217558687915102927930024229 40792253984081798986879543)
    ·
      refine ⟨61188380976122698480319315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40792253984081798986879543 61188380976122698480319315)
      ·
        refine ⟨91782571464184047720478973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61188380976122698480319315 91782571464184047720478973)
        ·
          refine ⟨34418464299069017895179615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91782571464184047720478973 34418464299069017895179615)
          ·
            refine ⟨51627696448603526842769423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34418464299069017895179615 51627696448603526842769423)
            ·
              refine ⟨77441544672905290264154135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51627696448603526842769423 77441544672905290264154135)
              ·
                refine ⟨116162317009357935396231203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77441544672905290264154135 116162317009357935396231203)
                ·
                  refine ⟨174243475514036903094346805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116162317009357935396231203 174243475514036903094346805)
                  ·
                    refine ⟨16335325829440959665095013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174243475514036903094346805 16335325829440959665095013)
                    ·
                      refine ⟨3062873593020179937205315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16335325829440959665095013 3062873593020179937205315)
                      ·
                        rfl

theorem cell23_5964925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_5964925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964925 prefixEnd_5964925 := by exact prefixLift 5964925
  have htrace : WordTrace (prefixWord ++ tailWord_5964925) baseStart_5964925 baseEnd_5964925 := by
    simpa [prefixWord, tailWord_5964925, baseEnd_5964925] using wordTrace_append hprefix tailTrace_5964925
  have hstable : (prefixWord ++ tailWord_5964925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964925).length < 2 ^ (prefixWord ++ tailWord_5964925).sum := by decide
  have hdescent : baseEnd_5964925 < baseStart_5964925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964929 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_5964929 : Nat := 118140960795 + 5964929 * 2 ^ 59
def prefixEnd_5964929 : Nat := 4983230072969 + 3 ^ 40 * 5964929 * 2
def baseEnd_5964929 : Nat := 3062875646942797921555297

theorem tailTrace_5964929 : CollatzResearch.WordTrace tailWord_5964929 prefixEnd_5964929 3062875646942797921555297 := by
  unfold tailWord_5964929
  simp only [CollatzResearch.WordTrace]
  refine ⟨217558833807088436613169841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145039222538058957742113227 217558833807088436613169841)
  ·
    refine ⟨163169125355316327459877381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217558833807088436613169841 163169125355316327459877381)
    ·
      refine ⟨30594211004121811398727009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163169125355316327459877381 30594211004121811398727009)
      ·
        refine ⟨22945658253091358549045257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30594211004121811398727009 22945658253091358549045257)
        ·
          refine ⟨17209243689818518911783943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22945658253091358549045257 17209243689818518911783943)
          ·
            refine ⟨25813865534727778367675915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17209243689818518911783943 25813865534727778367675915)
            ·
              refine ⟨38720798302091667551513873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25813865534727778367675915 38720798302091667551513873)
              ·
                refine ⟨29040598726568750663635405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38720798302091667551513873 29040598726568750663635405)
                ·
                  refine ⟨10890224522463281498863277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29040598726568750663635405 10890224522463281498863277)
                  ·
                    refine ⟨4083834195923730562073729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10890224522463281498863277 4083834195923730562073729)
                    ·
                      refine ⟨3062875646942797921555297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083834195923730562073729 3062875646942797921555297)
                      ·
                        rfl

theorem cell23_5964929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_5964929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964929 prefixEnd_5964929 := by exact prefixLift 5964929
  have htrace : WordTrace (prefixWord ++ tailWord_5964929) baseStart_5964929 baseEnd_5964929 := by
    simpa [prefixWord, tailWord_5964929, baseEnd_5964929] using wordTrace_append hprefix tailTrace_5964929
  have hstable : (prefixWord ++ tailWord_5964929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964929).length < 2 ^ (prefixWord ++ tailWord_5964929).sum := by decide
  have hdescent : baseEnd_5964929 < baseStart_5964929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964993 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_5964993 : Nat := 118140960795 + 5964993 * 2 ^ 59
def prefixEnd_5964993 : Nat := 4983230072969 + 3 ^ 40 * 5964993 * 2
def baseEnd_5964993 : Nat := 3062908509704685671155003

theorem tailTrace_5964993 : CollatzResearch.WordTrace tailWord_5964993 prefixEnd_5964993 3062908509704685671155003 := by
  unfold tailWord_5964993
  simp only [CollatzResearch.WordTrace]
  refine ⟨217561168078856575543499633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145040778719237717028999755 217561168078856575543499633)
  ·
    refine ⟨163170876059142431657624725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217561168078856575543499633 163170876059142431657624725)
    ·
      refine ⟨7648634815272301483951159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163170876059142431657624725 7648634815272301483951159)
      ·
        refine ⟨11472952222908452225926739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7648634815272301483951159 11472952222908452225926739)
        ·
          refine ⟨17209428334362678338890109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11472952222908452225926739 17209428334362678338890109)
          ·
            refine ⟨6453535625386004377083791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17209428334362678338890109 6453535625386004377083791)
            ·
              refine ⟨9680303438079006565625687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453535625386004377083791 9680303438079006565625687)
              ·
                refine ⟨14520455157118509848438531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9680303438079006565625687 14520455157118509848438531)
                ·
                  refine ⟨21780682735677764772657797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14520455157118509848438531 21780682735677764772657797)
                  ·
                    refine ⟨4083878012939580894873337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21780682735677764772657797 4083878012939580894873337)
                    ·
                      refine ⟨3062908509704685671155003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4083878012939580894873337 3062908509704685671155003)
                      ·
                        rfl

theorem cell23_5964993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_5964993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964993 prefixEnd_5964993 := by exact prefixLift 5964993
  have htrace : WordTrace (prefixWord ++ tailWord_5964993) baseStart_5964993 baseEnd_5964993 := by
    simpa [prefixWord, tailWord_5964993, baseEnd_5964993] using wordTrace_append hprefix tailTrace_5964993
  have hstable : (prefixWord ++ tailWord_5964993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964993).length < 2 ^ (prefixWord ++ tailWord_5964993).sum := by decide
  have hdescent : baseEnd_5964993 < baseStart_5964993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5964995 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 6, 5]
def baseStart_5964995 : Nat := 118140960795 + 5964995 * 2 ^ 59
def prefixEnd_5964995 : Nat := 4983230072969 + 3 ^ 40 * 5964995 * 2
def baseEnd_5964995 : Nat := 1020969845555331554443331

theorem tailTrace_5964995 : CollatzResearch.WordTrace tailWord_5964995 prefixEnd_5964995 1020969845555331554443331 := by
  unfold tailWord_5964995
  simp only [CollatzResearch.WordTrace]
  refine ⟨217561241024849329885072439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145040827349899553256714959 217561241024849329885072439)
  ·
    refine ⟨326341861537273994827608659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217561241024849329885072439 326341861537273994827608659)
    ·
      refine ⟨489512792305910992241412989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326341861537273994827608659 489512792305910992241412989)
      ·
        refine ⟨183567297114716622090529871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489512792305910992241412989 183567297114716622090529871)
        ·
          refine ⟨275350945672074933135794807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183567297114716622090529871 275350945672074933135794807)
          ·
            refine ⟨413026418508112399703692211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275350945672074933135794807 413026418508112399703692211)
            ·
              refine ⟨619539627762168599555538317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413026418508112399703692211 619539627762168599555538317)
              ·
                refine ⟨232327360410813224833326869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 619539627762168599555538317 232327360410813224833326869)
                ·
                  refine ⟨10890345019256869914062197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 232327360410813224833326869 10890345019256869914062197)
                  ·
                    refine ⟨1020969845555331554443331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10890345019256869914062197 1020969845555331554443331)
                    ·
                      rfl

theorem cell23_5964995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 5].length) (baseStart_5964995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5964995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5964995 prefixEnd_5964995 := by exact prefixLift 5964995
  have htrace : WordTrace (prefixWord ++ tailWord_5964995) baseStart_5964995 baseEnd_5964995 := by
    simpa [prefixWord, tailWord_5964995, baseEnd_5964995] using wordTrace_append hprefix tailTrace_5964995
  have hstable : (prefixWord ++ tailWord_5964995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5964995).length < 2 ^ (prefixWord ++ tailWord_5964995).sum := by decide
  have hdescent : baseEnd_5964995 < baseStart_5964995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5964995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965016 : List Nat := [2, 1, 2, 2, 5, 2, 1, 3, 5]
def baseStart_5965016 : Nat := 118140960795 + 5965016 * 2 ^ 59
def prefixEnd_5965016 : Nat := 4983230072969 + 3 ^ 40 * 5965016 * 2
def baseEnd_5965016 : Nat := 340324479973304342351933

theorem tailTrace_5965016 : CollatzResearch.WordTrace tailWord_5965016 prefixEnd_5965016 340324479973304342351933 := by
  unfold tailWord_5965016
  simp only [CollatzResearch.WordTrace]
  refine ⟨108781003478886625235793451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145041337971848833647724601 108781003478886625235793451)
  ·
    refine ⟨163171505218329937853690177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108781003478886625235793451 163171505218329937853690177)
    ·
      refine ⟨122378628913747453390267633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163171505218329937853690177 122378628913747453390267633)
      ·
        refine ⟨91783971685310590042700725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122378628913747453390267633 91783971685310590042700725)
        ·
          refine ⟨8604747345497867816503193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91783971685310590042700725 8604747345497867816503193)
          ·
            refine ⟨6453560509123400862377395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8604747345497867816503193 6453560509123400862377395)
            ·
              refine ⟨9680340763685101293566093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453560509123400862377395 9680340763685101293566093)
              ·
                refine ⟨3630127786381912985087285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9680340763685101293566093 3630127786381912985087285)
                ·
                  refine ⟨340324479973304342351933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3630127786381912985087285 340324479973304342351933)
                  ·
                    rfl

theorem cell23_5965016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 5].length) (baseStart_5965016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965016 prefixEnd_5965016 := by exact prefixLift 5965016
  have htrace : WordTrace (prefixWord ++ tailWord_5965016) baseStart_5965016 baseEnd_5965016 := by
    simpa [prefixWord, tailWord_5965016, baseEnd_5965016] using wordTrace_append hprefix tailTrace_5965016
  have hstable : (prefixWord ++ tailWord_5965016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965016).length < 2 ^ (prefixWord ++ tailWord_5965016).sum := by decide
  have hdescent : baseEnd_5965016 < baseStart_5965016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965029 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_5965029 : Nat := 118140960795 + 5965029 * 2 ^ 59
def prefixEnd_5965029 : Nat := 4983230072969 + 3 ^ 40 * 5965029 * 2
def baseEnd_5965029 : Nat := 1020975665002749176768279

theorem tailTrace_5965029 : CollatzResearch.WordTrace tailWord_5965029 prefixEnd_5965029 1020975665002749176768279 := by
  unfold tailWord_5965029
  simp only [CollatzResearch.WordTrace]
  refine ⟨217562481106726153691810141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145041654071150769127873427 217562481106726153691810141)
  ·
    refine ⟨81585930415022307634428803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217562481106726153691810141 81585930415022307634428803)
    ·
      refine ⟨122378895622533461451643205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81585930415022307634428803 122378895622533461451643205)
      ·
        refine ⟨22946042929225024022183101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122378895622533461451643205 22946042929225024022183101)
        ·
          refine ⟨8604766098459384008318663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22946042929225024022183101 8604766098459384008318663)
          ·
            refine ⟨12907149147689076012477995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8604766098459384008318663 12907149147689076012477995)
            ·
              refine ⟨19360723721533614018716993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12907149147689076012477995 19360723721533614018716993)
              ·
                refine ⟨14520542791150210514037745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19360723721533614018716993 14520542791150210514037745)
                ·
                  refine ⟨10890407093362657885528309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14520542791150210514037745 10890407093362657885528309)
                  ·
                    refine ⟨1020975665002749176768279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10890407093362657885528309 1020975665002749176768279)
                    ·
                      rfl

theorem cell23_5965029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_5965029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965029 prefixEnd_5965029 := by exact prefixLift 5965029
  have htrace : WordTrace (prefixWord ++ tailWord_5965029) baseStart_5965029 baseEnd_5965029 := by
    simpa [prefixWord, tailWord_5965029, baseEnd_5965029] using wordTrace_append hprefix tailTrace_5965029
  have hstable : (prefixWord ++ tailWord_5965029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965029).length < 2 ^ (prefixWord ++ tailWord_5965029).sum := by decide
  have hdescent : baseEnd_5965029 < baseStart_5965029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965075 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 8]
def baseStart_5965075 : Nat := 118140960795 + 5965075 * 2 ^ 59
def prefixEnd_5965075 : Nat := 4983230072969 + 3 ^ 40 * 5965075 * 2
def baseEnd_5965075 : Nat := 3062950615118354350329625

theorem tailTrace_5965075 : CollatzResearch.WordTrace tailWord_5965075 prefixEnd_5965075 3062950615118354350329625 := by
  unfold tailWord_5965075
  simp only [CollatzResearch.WordTrace]
  refine ⟨217564158864559503547984679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145042772576373002365323119 217564158864559503547984679)
  ·
    refine ⟨326346238296839255321977019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217564158864559503547984679 326346238296839255321977019)
    ·
      refine ⟨489519357445258882982965529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326346238296839255321977019 489519357445258882982965529)
      ·
        refine ⟨367139518083944162237224147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489519357445258882982965529 367139518083944162237224147)
        ·
          refine ⟨550709277125916243355836221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367139518083944162237224147 550709277125916243355836221)
          ·
            refine ⟨206515978922218591258438583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 550709277125916243355836221 206515978922218591258438583)
            ·
              refine ⟨309773968383327886887657875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206515978922218591258438583 309773968383327886887657875)
              ·
                refine ⟨464660952574991830331486813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309773968383327886887657875 464660952574991830331486813)
                ·
                  refine ⟨174247857215621936374307555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464660952574991830331486813 174247857215621936374307555)
                  ·
                    refine ⟨261371785823432904561461333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 174247857215621936374307555 261371785823432904561461333)
                    ·
                      refine ⟨3062950615118354350329625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 261371785823432904561461333 3062950615118354350329625)
                      ·
                        rfl

theorem cell23_5965075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_5965075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965075 prefixEnd_5965075 := by exact prefixLift 5965075
  have htrace : WordTrace (prefixWord ++ tailWord_5965075) baseStart_5965075 baseEnd_5965075 := by
    simpa [prefixWord, tailWord_5965075, baseEnd_5965075] using wordTrace_append hprefix tailTrace_5965075
  have hstable : (prefixWord ++ tailWord_5965075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965075).length < 2 ^ (prefixWord ++ tailWord_5965075).sum := by decide
  have hdescent : baseEnd_5965075 < baseStart_5965075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965092 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_5965092 : Nat := 118140960795 + 5965092 * 2 ^ 59
def prefixEnd_5965092 : Nat := 4983230072969 + 3 ^ 40 * 5965092 * 2
def baseEnd_5965092 : Nat := 3062959344289480783817047

theorem tailTrace_5965092 : CollatzResearch.WordTrace tailWord_5965092 prefixEnd_5965092 3062959344289480783817047 := by
  unfold tailWord_5965092
  simp only [CollatzResearch.WordTrace]
  refine ⟨108782389452748957725676765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145043185936998610300902353 108782389452748957725676765)
  ·
    refine ⟨40793396044780859147128787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108782389452748957725676765 40793396044780859147128787)
    ·
      refine ⟨61190094067171288720693181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40793396044780859147128787 61190094067171288720693181)
      ·
        refine ⟨22946285275189233270259943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61190094067171288720693181 22946285275189233270259943)
        ·
          refine ⟨34419427912783849905389915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22946285275189233270259943 34419427912783849905389915)
          ·
            refine ⟨51629141869175774858084873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34419427912783849905389915 51629141869175774858084873)
            ·
              refine ⟨38721856401881831143563655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51629141869175774858084873 38721856401881831143563655)
              ·
                refine ⟨58082784602822746715345483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38721856401881831143563655 58082784602822746715345483)
                ·
                  refine ⟨87124176904234120073018225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58082784602822746715345483 87124176904234120073018225)
                  ·
                    refine ⟨65343132678175590054763669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87124176904234120073018225 65343132678175590054763669)
                    ·
                      refine ⟨3062959344289480783817047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65343132678175590054763669 3062959344289480783817047)
                      ·
                        rfl

theorem cell23_5965092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_5965092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965092 prefixEnd_5965092 := by exact prefixLift 5965092
  have htrace : WordTrace (prefixWord ++ tailWord_5965092) baseStart_5965092 baseEnd_5965092 := by
    simpa [prefixWord, tailWord_5965092, baseEnd_5965092] using wordTrace_append hprefix tailTrace_5965092
  have hstable : (prefixWord ++ tailWord_5965092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965092).length < 2 ^ (prefixWord ++ tailWord_5965092).sum := by decide
  have hdescent : baseEnd_5965092 < baseStart_5965092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965093 : List Nat := [1, 3, 1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_5965093 : Nat := 118140960795 + 5965093 * 2 ^ 59
def prefixEnd_5965093 : Nat := 4983230072969 + 3 ^ 40 * 5965093 * 2
def baseEnd_5965093 : Nat := 1020986619256711759968181

theorem tailTrace_5965093 : CollatzResearch.WordTrace tailWord_5965093 prefixEnd_5965093 1020986619256711759968181 := by
  unfold tailWord_5965093
  simp only [CollatzResearch.WordTrace]
  refine ⟨217564815378494292622139933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145043210252329528414759955 217564815378494292622139933)
  ·
    refine ⟨81586805766935359733302475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217564815378494292622139933 81586805766935359733302475)
    ·
      refine ⟨122380208650403039599953713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81586805766935359733302475 122380208650403039599953713)
      ·
        refine ⟨91785156487802279699965285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122380208650403039599953713 91785156487802279699965285)
        ·
          refine ⟨17209716841462927443743491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91785156487802279699965285 17209716841462927443743491)
          ·
            refine ⟨25814575262194391165615237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17209716841462927443743491 25814575262194391165615237)
            ·
              refine ⟨4840232861661448343552857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25814575262194391165615237 4840232861661448343552857)
              ·
                refine ⟨3630174646246086257664643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4840232861661448343552857 3630174646246086257664643)
                ·
                  refine ⟨5445261969369129386496965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630174646246086257664643 5445261969369129386496965)
                  ·
                    refine ⟨1020986619256711759968181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5445261969369129386496965 1020986619256711759968181)
                    ·
                      rfl

theorem cell23_5965093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_5965093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965093 prefixEnd_5965093 := by exact prefixLift 5965093
  have htrace : WordTrace (prefixWord ++ tailWord_5965093) baseStart_5965093 baseEnd_5965093 := by
    simpa [prefixWord, tailWord_5965093, baseEnd_5965093] using wordTrace_append hprefix tailTrace_5965093
  have hstable : (prefixWord ++ tailWord_5965093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965093).length < 2 ^ (prefixWord ++ tailWord_5965093).sum := by decide
  have hdescent : baseEnd_5965093 < baseStart_5965093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965116 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_5965116 : Nat := 118140960795 + 5965116 * 2 ^ 59
def prefixEnd_5965116 : Nat := 4983230072969 + 3 ^ 40 * 5965116 * 2
def baseEnd_5965116 : Nat := 3062971667825188689916937

theorem tailTrace_5965116 : CollatzResearch.WordTrace tailWord_5965116 prefixEnd_5965116 3062971667825188689916937 := by
  unfold tailWord_5965116
  simp only [CollatzResearch.WordTrace]
  refine ⟨108782827128705483775113601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145043769504940645033484801 108782827128705483775113601)
  ·
    refine ⟨81587120346529112831335201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108782827128705483775113601 81587120346529112831335201)
    ·
      refine ⟨61190340259896834623501401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81587120346529112831335201 61190340259896834623501401)
      ·
        refine ⟨45892755194922625967626051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61190340259896834623501401 45892755194922625967626051)
        ·
          refine ⟨68839132792383938951439077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45892755194922625967626051 68839132792383938951439077)
          ·
            refine ⟨12907337398571988553394827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68839132792383938951439077 12907337398571988553394827)
            ·
              refine ⟨19361006097857982830092241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12907337398571988553394827 19361006097857982830092241)
              ·
                refine ⟨14520754573393487122569181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19361006097857982830092241 14520754573393487122569181)
                ·
                  refine ⟨5445282965022557670963443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14520754573393487122569181 5445282965022557670963443)
                  ·
                    refine ⟨8167924447533836506445165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5445282965022557670963443 8167924447533836506445165)
                    ·
                      refine ⟨3062971667825188689916937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8167924447533836506445165 3062971667825188689916937)
                      ·
                        rfl

theorem cell23_5965116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_5965116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965116 prefixEnd_5965116 := by exact prefixLift 5965116
  have htrace : WordTrace (prefixWord ++ tailWord_5965116) baseStart_5965116 baseEnd_5965116 := by
    simpa [prefixWord, tailWord_5965116, baseEnd_5965116] using wordTrace_append hprefix tailTrace_5965116
  have hstable : (prefixWord ++ tailWord_5965116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965116).length < 2 ^ (prefixWord ++ tailWord_5965116).sum := by decide
  have hdescent : baseEnd_5965116 < baseStart_5965116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965139 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 4]
def baseStart_5965139 : Nat := 118140960795 + 5965139 * 2 ^ 59
def prefixEnd_5965139 : Nat := 4983230072969 + 3 ^ 40 * 5965139 * 2
def baseEnd_5965139 : Nat := 3062983477880242099929331

theorem tailTrace_5965139 : CollatzResearch.WordTrace tailWord_5965139 prefixEnd_5965139 3062983477880242099929331 := by
  unfold tailWord_5965139
  simp only [CollatzResearch.WordTrace]
  refine ⟨217566493136327642478314471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145044328757551761652209647 217566493136327642478314471)
  ·
    refine ⟨326349739704491463717471707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217566493136327642478314471 326349739704491463717471707)
    ·
      refine ⟨489524609556737195576207561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326349739704491463717471707 489524609556737195576207561)
      ·
        refine ⟨367143457167552896682155671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489524609556737195576207561 367143457167552896682155671)
        ·
          refine ⟨550715185751329345023233507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367143457167552896682155671 550715185751329345023233507)
          ·
            refine ⟨826072778626994017534850261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550715185751329345023233507 826072778626994017534850261)
            ·
              refine ⟨19361080749070172285973053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 826072778626994017534850261 19361080749070172285973053)
              ·
                refine ⟨7260405280901314607239895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19361080749070172285973053 7260405280901314607239895)
                ·
                  refine ⟨10890607921351971910859843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7260405280901314607239895 10890607921351971910859843)
                  ·
                    refine ⟨16335911882027957866289765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10890607921351971910859843 16335911882027957866289765)
                    ·
                      refine ⟨3062983477880242099929331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16335911882027957866289765 3062983477880242099929331)
                      ·
                        rfl

theorem cell23_5965139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 1, 4].length) (baseStart_5965139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965139 prefixEnd_5965139 := by exact prefixLift 5965139
  have htrace : WordTrace (prefixWord ++ tailWord_5965139) baseStart_5965139 baseEnd_5965139 := by
    simpa [prefixWord, tailWord_5965139, baseEnd_5965139] using wordTrace_append hprefix tailTrace_5965139
  have hstable : (prefixWord ++ tailWord_5965139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965139).length < 2 ^ (prefixWord ++ tailWord_5965139).sum := by decide
  have hdescent : baseEnd_5965139 < baseStart_5965139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965169 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_5965169 : Nat := 118140960795 + 5965169 * 2 ^ 59
def prefixEnd_5965169 : Nat := 4983230072969 + 3 ^ 40 * 5965169 * 2
def baseEnd_5965169 : Nat := 3062998882299876982554193

theorem tailTrace_5965169 : CollatzResearch.WordTrace tailWord_5965169 prefixEnd_5965169 3062998882299876982554193 := by
  unfold tailWord_5965169
  simp only [CollatzResearch.WordTrace]
  refine ⟨217567587326218957601906561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145045058217479305067937707 217567587326218957601906561)
  ·
    refine ⟨163175690494664218201429921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217567587326218957601906561 163175690494664218201429921)
    ·
      refine ⟨122381767870998163651072441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163175690494664218201429921 122381767870998163651072441)
      ·
        refine ⟨91786325903248622738304331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122381767870998163651072441 91786325903248622738304331)
        ·
          refine ⟨137679488854872934107456497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91786325903248622738304331 137679488854872934107456497)
          ·
            refine ⟨103259616641154700580592373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137679488854872934107456497 103259616641154700580592373)
            ·
              refine ⟨9680589060108253179430535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103259616641154700580592373 9680589060108253179430535)
              ·
                refine ⟨14520883590162379769145803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9680589060108253179430535 14520883590162379769145803)
                ·
                  refine ⟨21781325385243569653718705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14520883590162379769145803 21781325385243569653718705)
                  ·
                    refine ⟨16335994038932677240289029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21781325385243569653718705 16335994038932677240289029)
                    ·
                      refine ⟨3062998882299876982554193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16335994038932677240289029 3062998882299876982554193)
                      ·
                        rfl

theorem cell23_5965169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_5965169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965169 prefixEnd_5965169 := by exact prefixLift 5965169
  have htrace : WordTrace (prefixWord ++ tailWord_5965169) baseStart_5965169 baseEnd_5965169 := by
    simpa [prefixWord, tailWord_5965169, baseEnd_5965169] using wordTrace_append hprefix tailTrace_5965169
  have hstable : (prefixWord ++ tailWord_5965169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965169).length < 2 ^ (prefixWord ++ tailWord_5965169).sum := by decide
  have hdescent : baseEnd_5965169 < baseStart_5965169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965173 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_5965173 : Nat := 118140960795 + 5965173 * 2 ^ 59
def prefixEnd_5965173 : Nat := 4983230072969 + 3 ^ 40 * 5965173 * 2
def baseEnd_5965173 : Nat := 3063000936222494966904175

theorem tailTrace_5965173 : CollatzResearch.WordTrace tailWord_5965173 prefixEnd_5965173 3063000936222494966904175 := by
  unfold tailWord_5965173
  simp only [CollatzResearch.WordTrace]
  refine ⟨217567733218204466285052173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145045155478802977523368115 217567733218204466285052173)
  ·
    refine ⟨81587899956826674856894565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217567733218204466285052173 81587899956826674856894565)
    ·
      refine ⟨15297731241905001535667731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81587899956826674856894565 15297731241905001535667731)
      ·
        refine ⟨22946596862857502303501597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15297731241905001535667731 22946596862857502303501597)
        ·
          refine ⟨8604973823571563363813099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22946596862857502303501597 8604973823571563363813099)
          ·
            refine ⟨12907460735357345045719649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8604973823571563363813099 12907460735357345045719649)
            ·
              refine ⟨9680595551518008784289737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12907460735357345045719649 9680595551518008784289737)
              ·
                refine ⟨7260446663638506588217303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9680595551518008784289737 7260446663638506588217303)
                ·
                  refine ⟨10890669995457759882325955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7260446663638506588217303 10890669995457759882325955)
                  ·
                    refine ⟨16336004993186639823488933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10890669995457759882325955 16336004993186639823488933)
                    ·
                      refine ⟨3063000936222494966904175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16336004993186639823488933 3063000936222494966904175)
                      ·
                        rfl

theorem cell23_5965173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_5965173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965173 prefixEnd_5965173 := by exact prefixLift 5965173
  have htrace : WordTrace (prefixWord ++ tailWord_5965173) baseStart_5965173 baseEnd_5965173 := by
    simpa [prefixWord, tailWord_5965173, baseEnd_5965173] using wordTrace_append hprefix tailTrace_5965173
  have hstable : (prefixWord ++ tailWord_5965173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965173).length < 2 ^ (prefixWord ++ tailWord_5965173).sum := by decide
  have hdescent : baseEnd_5965173 < baseStart_5965173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965189 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 3]
def baseStart_5965189 : Nat := 118140960795 + 5965189 * 2 ^ 59
def prefixEnd_5965189 : Nat := 4983230072969 + 3 ^ 40 * 5965189 * 2
def baseEnd_5965189 : Nat := 3063009151912966904304101

theorem tailTrace_5965189 : CollatzResearch.WordTrace tailWord_5965189 prefixEnd_5965189 3063009151912966904304101 := by
  unfold tailWord_5965189
  simp only [CollatzResearch.WordTrace]
  refine ⟨217568316786146501017634621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145045544524097667345089747 217568316786146501017634621)
  ·
    refine ⟨81588118794804937881612983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217568316786146501017634621 81588118794804937881612983)
    ·
      refine ⟨122382178192207406822419475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81588118794804937881612983 122382178192207406822419475)
      ·
        refine ⟨183573267288311110233629213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122382178192207406822419475 183573267288311110233629213)
        ·
          refine ⟨68839975233116666337610955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183573267288311110233629213 68839975233116666337610955)
          ·
            refine ⟨103259962849674999506416433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68839975233116666337610955 103259962849674999506416433)
            ·
              refine ⟨77444972137256249629812325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103259962849674999506416433 77444972137256249629812325)
              ·
                refine ⟨14520932275735546805589811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77444972137256249629812325 14520932275735546805589811)
                ·
                  refine ⟨21781398413603320208384717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14520932275735546805589811 21781398413603320208384717)
                  ·
                    refine ⟨8168024405101245078144269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21781398413603320208384717 8168024405101245078144269)
                    ·
                      refine ⟨3063009151912966904304101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8168024405101245078144269 3063009151912966904304101)
                      ·
                        rfl

theorem cell23_5965189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_5965189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965189 prefixEnd_5965189 := by exact prefixLift 5965189
  have htrace : WordTrace (prefixWord ++ tailWord_5965189) baseStart_5965189 baseEnd_5965189 := by
    simpa [prefixWord, tailWord_5965189, baseEnd_5965189] using wordTrace_append hprefix tailTrace_5965189
  have hstable : (prefixWord ++ tailWord_5965189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965189).length < 2 ^ (prefixWord ++ tailWord_5965189).sum := by decide
  have hdescent : baseEnd_5965189 < baseStart_5965189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965216 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 3, 3, 2]
def baseStart_5965216 : Nat := 118140960795 + 5965216 * 2 ^ 59
def prefixEnd_5965216 : Nat := 4983230072969 + 3 ^ 40 * 5965216 * 2
def baseEnd_5965216 : Nat := 3063023015890638298666477

theorem tailTrace_5965216 : CollatzResearch.WordTrace tailWord_5965216 prefixEnd_5965216 3063023015890638298666477 := by
  unfold tailWord_5965216
  simp only [CollatzResearch.WordTrace]
  refine ⟨108784650778524342314433751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145046201038032456419245001 108784650778524342314433751)
  ·
    refine ⟨163176976167786513471650627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108784650778524342314433751 163176976167786513471650627)
    ·
      refine ⟨244765464251679770207475941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163176976167786513471650627 244765464251679770207475941)
      ·
        refine ⟨45893524547189956913901739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244765464251679770207475941 45893524547189956913901739)
        ·
          refine ⟨68840286820784935370852609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45893524547189956913901739 68840286820784935370852609)
          ·
            refine ⟨51630215115588701528139457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68840286820784935370852609 51630215115588701528139457)
            ·
              refine ⟨38722661336691526146104593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51630215115588701528139457 38722661336691526146104593)
              ·
                refine ⟨29041996002518644609578445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38722661336691526146104593 29041996002518644609578445)
                ·
                  refine ⟨10890748500944491728591917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29041996002518644609578445 10890748500944491728591917)
                  ·
                    refine ⟨4084030687854184398221969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10890748500944491728591917 4084030687854184398221969)
                    ·
                      refine ⟨3063023015890638298666477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084030687854184398221969 3063023015890638298666477)
                      ·
                        rfl

theorem cell23_5965216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_5965216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965216 prefixEnd_5965216 := by exact prefixLift 5965216
  have htrace : WordTrace (prefixWord ++ tailWord_5965216) baseStart_5965216 baseEnd_5965216 := by
    simpa [prefixWord, tailWord_5965216, baseEnd_5965216] using wordTrace_append hprefix tailTrace_5965216
  have hstable : (prefixWord ++ tailWord_5965216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965216).length < 2 ^ (prefixWord ++ tailWord_5965216).sum := by decide
  have hdescent : baseEnd_5965216 < baseStart_5965216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965223 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_5965223 : Nat := 118140960795 + 5965223 * 2 ^ 59
def prefixEnd_5965223 : Nat := 4983230072969 + 3 ^ 40 * 5965223 * 2
def baseEnd_5965223 : Nat := 3063026610255219771278945

theorem tailTrace_5965223 : CollatzResearch.WordTrace tailWord_5965223 prefixEnd_5965223 3063026610255219771278945 := by
  unfold tailWord_5965223
  simp only [CollatzResearch.WordTrace]
  refine ⟨217569556868023324824372323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145046371245348883216248215 217569556868023324824372323)
  ·
    refine ⟨326354335302034987236558485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217569556868023324824372323 326354335302034987236558485)
    ·
      refine ⟨15297859467282890026713679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 326354335302034987236558485 15297859467282890026713679)
      ·
        refine ⟨22946789200924335040070519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15297859467282890026713679 22946789200924335040070519)
        ·
          refine ⟨34420183801386502560105779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22946789200924335040070519 34420183801386502560105779)
          ·
            refine ⟨51630275702079753840158669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34420183801386502560105779 51630275702079753840158669)
            ·
              refine ⟨19361353388279907690059501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51630275702079753840158669 19361353388279907690059501)
              ·
                refine ⟨7260507520604965383772313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19361353388279907690059501 7260507520604965383772313)
                ·
                  refine ⟨5445380640453724037829235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7260507520604965383772313 5445380640453724037829235)
                  ·
                    refine ⟨8168070960680586056743853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5445380640453724037829235 8168070960680586056743853)
                    ·
                      refine ⟨3063026610255219771278945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8168070960680586056743853 3063026610255219771278945)
                      ·
                        rfl

theorem cell23_5965223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_5965223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965223 prefixEnd_5965223 := by exact prefixLift 5965223
  have htrace : WordTrace (prefixWord ++ tailWord_5965223) baseStart_5965223 baseEnd_5965223 := by
    simpa [prefixWord, tailWord_5965223, baseEnd_5965223] using wordTrace_append hprefix tailTrace_5965223
  have hstable : (prefixWord ++ tailWord_5965223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965223).length < 2 ^ (prefixWord ++ tailWord_5965223).sum := by decide
  have hdescent : baseEnd_5965223 < baseStart_5965223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965263 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 2, 2, 2]
def baseStart_5965263 : Nat := 118140960795 + 5965263 * 2 ^ 59
def prefixEnd_5965263 : Nat := 4983230072969 + 3 ^ 40 * 5965263 * 2
def baseEnd_5965263 : Nat := 3063047149481399614778761

theorem tailTrace_5965263 : CollatzResearch.WordTrace tailWord_5965263 prefixEnd_5965263 3063047149481399614778761 := by
  unfold tailWord_5965263
  simp only [CollatzResearch.WordTrace]
  refine ⟨217571015787878411655828443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145047343858585607770552295 217571015787878411655828443)
  ·
    refine ⟨326356523681817617483742665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217571015787878411655828443 326356523681817617483742665)
    ·
      refine ⟨244767392761363213112806999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326356523681817617483742665 244767392761363213112806999)
      ·
        refine ⟨367151089142044819669210499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244767392761363213112806999 367151089142044819669210499)
        ·
          refine ⟨550726633713067229503815749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367151089142044819669210499 550726633713067229503815749)
          ·
            refine ⟨103261243821200105531965453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 550726633713067229503815749 103261243821200105531965453)
            ·
              refine ⟨38722966432950039574487045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103261243821200105531965453 38722966432950039574487045)
              ·
                refine ⟨7260556206178132420216321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38722966432950039574487045 7260556206178132420216321)
                ·
                  refine ⟨5445417154633599315162241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7260556206178132420216321 5445417154633599315162241)
                  ·
                    refine ⟨4084062865975199486371681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5445417154633599315162241 4084062865975199486371681)
                    ·
                      refine ⟨3063047149481399614778761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084062865975199486371681 3063047149481399614778761)
                      ·
                        rfl

theorem cell23_5965263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 2, 2].length) (baseStart_5965263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965263 prefixEnd_5965263 := by exact prefixLift 5965263
  have htrace : WordTrace (prefixWord ++ tailWord_5965263) baseStart_5965263 baseEnd_5965263 := by
    simpa [prefixWord, tailWord_5965263, baseEnd_5965263] using wordTrace_append hprefix tailTrace_5965263
  have hstable : (prefixWord ++ tailWord_5965263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965263).length < 2 ^ (prefixWord ++ tailWord_5965263).sum := by decide
  have hdescent : baseEnd_5965263 < baseStart_5965263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965269 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 7]
def baseStart_5965269 : Nat := 118140960795 + 5965269 * 2 ^ 59
def prefixEnd_5965269 : Nat := 4983230072969 + 3 ^ 40 * 5965269 * 2
def baseEnd_5965269 : Nat := 340338914485036287922637

theorem tailTrace_5965269 : CollatzResearch.WordTrace tailWord_5965269 prefixEnd_5965269 340338914485036287922637 := by
  unfold tailWord_5965269
  simp only [CollatzResearch.WordTrace]
  refine ⟨217571234625856674680546861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145047489750571116453697907 217571234625856674680546861)
  ·
    refine ⟨81589212984696253005205073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217571234625856674680546861 81589212984696253005205073)
    ·
      refine ⟨61191909738522189753903805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81589212984696253005205073 61191909738522189753903805)
      ·
        refine ⟨22946966151945821157713927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61191909738522189753903805 22946966151945821157713927)
        ·
          refine ⟨34420449227918731736570891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22946966151945821157713927 34420449227918731736570891)
          ·
            refine ⟨51630673841878097604856337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34420449227918731736570891 51630673841878097604856337)
            ·
              refine ⟨38723005381408573203642253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51630673841878097604856337 38723005381408573203642253)
              ·
                refine ⟨14521127018028214951365845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38723005381408573203642253 14521127018028214951365845)
                ·
                  refine ⟨340338914485036287922637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14521127018028214951365845 340338914485036287922637)
                  ·
                    rfl

theorem cell23_5965269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_5965269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965269 prefixEnd_5965269 := by exact prefixLift 5965269
  have htrace : WordTrace (prefixWord ++ tailWord_5965269) baseStart_5965269 baseEnd_5965269 := by
    simpa [prefixWord, tailWord_5965269, baseEnd_5965269] using wordTrace_append hprefix tailTrace_5965269
  have hstable : (prefixWord ++ tailWord_5965269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965269).length < 2 ^ (prefixWord ++ tailWord_5965269).sum := by decide
  have hdescent : baseEnd_5965269 < baseStart_5965269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965299 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 2, 5]
def baseStart_5965299 : Nat := 118140960795 + 5965299 * 2 ^ 59
def prefixEnd_5965299 : Nat := 4983230072969 + 3 ^ 40 * 5965299 * 2
def baseEnd_5965299 : Nat := 1021021878261653824642865

theorem tailTrace_5965299 : CollatzResearch.WordTrace tailWord_5965299 prefixEnd_5965299 1021021878261653824642865 := by
  unfold tailWord_5965299
  simp only [CollatzResearch.WordTrace]
  refine ⟨217572328815747989804138951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145048219210498659869425967 217572328815747989804138951)
  ·
    refine ⟨326358493223621984706208427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217572328815747989804138951 326358493223621984706208427)
    ·
      refine ⟨489537739835432977059312641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326358493223621984706208427 489537739835432977059312641)
      ·
        refine ⟨367153304876574732794484481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489537739835432977059312641 367153304876574732794484481)
        ·
          refine ⟨275364978657431049595863361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367153304876574732794484481 275364978657431049595863361)
          ·
            refine ⟨206523733993073287196897521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275364978657431049595863361 206523733993073287196897521)
            ·
              refine ⟨154892800494804965397673141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206523733993073287196897521 154892800494804965397673141)
              ·
                refine ⟨14521200046387965506031857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154892800494804965397673141 14521200046387965506031857)
                ·
                  refine ⟨10890900034790974129523893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14521200046387965506031857 10890900034790974129523893)
                  ·
                    refine ⟨1021021878261653824642865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10890900034790974129523893 1021021878261653824642865)
                    ·
                      rfl

theorem cell23_5965299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 5].length) (baseStart_5965299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965299 prefixEnd_5965299 := by exact prefixLift 5965299
  have htrace : WordTrace (prefixWord ++ tailWord_5965299) baseStart_5965299 baseEnd_5965299 := by
    simpa [prefixWord, tailWord_5965299, baseEnd_5965299] using wordTrace_append hprefix tailTrace_5965299
  have hstable : (prefixWord ++ tailWord_5965299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965299).length < 2 ^ (prefixWord ++ tailWord_5965299).sum := by decide
  have hdescent : baseEnd_5965299 < baseStart_5965299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965314 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_5965314 : Nat := 118140960795 + 5965314 * 2 ^ 59
def prefixEnd_5965314 : Nat := 4983230072969 + 3 ^ 40 * 5965314 * 2
def baseEnd_5965314 : Nat := 3063073336994778915241027

theorem tailTrace_5965314 : CollatzResearch.WordTrace tailWord_5965314 prefixEnd_5965314 3063073336994778915241027 := by
  unfold tailWord_5965314
  simp only [CollatzResearch.WordTrace]
  refine ⟨54393218977673411841483749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145048583940462431577289997 54393218977673411841483749)
  ·
    refine ⟨10198728558313764720278203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54393218977673411841483749 10198728558313764720278203)
    ·
      refine ⟨15298092837470647080417305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10198728558313764720278203 15298092837470647080417305)
      ·
        refine ⟨11473569628102985310312979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15298092837470647080417305 11473569628102985310312979)
        ·
          refine ⟨17210354442154477965469469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11473569628102985310312979 17210354442154477965469469)
          ·
            refine ⟨6453882915807929237051051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17210354442154477965469469 6453882915807929237051051)
            ·
              refine ⟨9680824373711893855576577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453882915807929237051051 9680824373711893855576577)
              ·
                refine ⟨7260618280283920391682433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9680824373711893855576577 7260618280283920391682433)
                ·
                  refine ⟨5445463710212940293761825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7260618280283920391682433 5445463710212940293761825)
                  ·
                    refine ⟨4084097782659705220321369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5445463710212940293761825 4084097782659705220321369)
                    ·
                      refine ⟨3063073336994778915241027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084097782659705220321369 3063073336994778915241027)
                      ·
                        rfl

theorem cell23_5965314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_5965314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965314 prefixEnd_5965314 := by exact prefixLift 5965314
  have htrace : WordTrace (prefixWord ++ tailWord_5965314) baseStart_5965314 baseEnd_5965314 := by
    simpa [prefixWord, tailWord_5965314, baseEnd_5965314] using wordTrace_append hprefix tailTrace_5965314
  have hstable : (prefixWord ++ tailWord_5965314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965314).length < 2 ^ (prefixWord ++ tailWord_5965314).sum := by decide
  have hdescent : baseEnd_5965314 < baseStart_5965314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965349 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 4]
def baseStart_5965349 : Nat := 118140960795 + 5965349 * 2 ^ 59
def prefixEnd_5965349 : Nat := 4983230072969 + 3 ^ 40 * 5965349 * 2
def baseEnd_5965349 : Nat := 3063091308817686278303365

theorem tailTrace_5965349 : CollatzResearch.WordTrace tailWord_5965349 prefixEnd_5965349 3063091308817686278303365 := by
  unfold tailWord_5965349
  simp only [CollatzResearch.WordTrace]
  refine ⟨217574152465566848343459101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145049434977044565562306067 217574152465566848343459101)
  ·
    refine ⟨81590307174587568128797163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217574152465566848343459101 81590307174587568128797163)
    ·
      refine ⟨122385460761881352193195745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81590307174587568128797163 122385460761881352193195745)
      ·
        refine ⟨91789095571411014144896809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122385460761881352193195745 91789095571411014144896809)
        ·
          refine ⟨68841821678558260608672607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91789095571411014144896809 68841821678558260608672607)
          ·
            refine ⟨103262732517837390913008911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68841821678558260608672607 103262732517837390913008911)
            ·
              refine ⟨154894098776756086369513367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103262732517837390913008911 154894098776756086369513367)
              ·
                refine ⟨232341148165134129554270051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154894098776756086369513367 232341148165134129554270051)
                ·
                  refine ⟨348511722247701194331405077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232341148165134129554270051 348511722247701194331405077)
                  ·
                    refine ⟨16336486980360993484284613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 348511722247701194331405077 16336486980360993484284613)
                    ·
                      refine ⟨3063091308817686278303365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16336486980360993484284613 3063091308817686278303365)
                      ·
                        rfl

theorem cell23_5965349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_5965349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965349 prefixEnd_5965349 := by exact prefixLift 5965349
  have htrace : WordTrace (prefixWord ++ tailWord_5965349) baseStart_5965349 baseEnd_5965349 := by
    simpa [prefixWord, tailWord_5965349, baseEnd_5965349] using wordTrace_append hprefix tailTrace_5965349
  have hstable : (prefixWord ++ tailWord_5965349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965349).length < 2 ^ (prefixWord ++ tailWord_5965349).sum := by decide
  have hdescent : baseEnd_5965349 < baseStart_5965349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965420 : List Nat := [2, 2, 1, 1, 3, 1, 1, 7, 1, 1, 3]
def baseStart_5965420 : Nat := 118140960795 + 5965420 * 2 ^ 59
def prefixEnd_5965420 : Nat := 4983230072969 + 3 ^ 40 * 5965420 * 2
def baseEnd_5965420 : Nat := 3063127765944155500515539

theorem tailTrace_5965420 : CollatzResearch.WordTrace tailWord_5965420 prefixEnd_5965420 3063127765944155500515539 := by
  unfold tailWord_5965420
  simp only [CollatzResearch.WordTrace]
  refine ⟨108788371024154813734646857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145051161365539751646195809 108788371024154813734646857)
  ·
    refine ⟨81591278268116110300985143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108788371024154813734646857 81591278268116110300985143)
    ·
      refine ⟨122386917402174165451477715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81591278268116110300985143 122386917402174165451477715)
      ·
        refine ⟨183580376103261248177216573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122386917402174165451477715 183580376103261248177216573)
        ·
          refine ⟨68842641038722968066456215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183580376103261248177216573 68842641038722968066456215)
          ·
            refine ⟨103263961558084452099684323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68842641038722968066456215 103263961558084452099684323)
            ·
              refine ⟨154895942337126678149526485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103263961558084452099684323 154895942337126678149526485)
              ·
                refine ⟨3630373648526406519129527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154895942337126678149526485 3630373648526406519129527)
                ·
                  refine ⟨5445560472789609778694291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630373648526406519129527 5445560472789609778694291)
                  ·
                    refine ⟨8168340709184414668041437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5445560472789609778694291 8168340709184414668041437)
                    ·
                      refine ⟨3063127765944155500515539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8168340709184414668041437 3063127765944155500515539)
                      ·
                        rfl

theorem cell23_5965420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 1, 3].length) (baseStart_5965420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965420 prefixEnd_5965420 := by exact prefixLift 5965420
  have htrace : WordTrace (prefixWord ++ tailWord_5965420) baseStart_5965420 baseEnd_5965420 := by
    simpa [prefixWord, tailWord_5965420, baseEnd_5965420] using wordTrace_append hprefix tailTrace_5965420
  have hstable : (prefixWord ++ tailWord_5965420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965420).length < 2 ^ (prefixWord ++ tailWord_5965420).sum := by decide
  have hdescent : baseEnd_5965420 < baseStart_5965420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965437 : List Nat := [1, 4, 1, 1, 4, 2, 1, 4, 1, 1, 3]
def baseStart_5965437 : Nat := 118140960795 + 5965437 * 2 ^ 59
def prefixEnd_5965437 : Nat := 4983230072969 + 3 ^ 40 * 5965437 * 2
def baseEnd_5965437 : Nat := 3063136495115281934002961

theorem tailTrace_5965437 : CollatzResearch.WordTrace tailWord_5965437 prefixEnd_5965437 3063136495115281934002961 := by
  unfold tailWord_5965437
  simp only [CollatzResearch.WordTrace]
  refine ⟨217577362089248039372662565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145051574726165359581775043 217577362089248039372662565)
  ·
    refine ⟨40795755391734007382374231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217577362089248039372662565 40795755391734007382374231)
    ·
      refine ⟨61193633087601011073561347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40795755391734007382374231 61193633087601011073561347)
      ·
        refine ⟨91790449631401516610342021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61193633087601011073561347 91790449631401516610342021)
        ·
          refine ⟨17210709305887784364439129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91790449631401516610342021 17210709305887784364439129)
          ·
            refine ⟨12908031979415838273329347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17210709305887784364439129 12908031979415838273329347)
            ·
              refine ⟨19362047969123757409994021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12908031979415838273329347 19362047969123757409994021)
              ·
                refine ⟨3630383994210704514373879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19362047969123757409994021 3630383994210704514373879)
                ·
                  refine ⟨5445575991316056771560819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630383994210704514373879 5445575991316056771560819)
                  ·
                    refine ⟨8168363986974085157341229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5445575991316056771560819 8168363986974085157341229)
                    ·
                      refine ⟨3063136495115281934002961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8168363986974085157341229 3063136495115281934002961)
                      ·
                        rfl

theorem cell23_5965437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_5965437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965437 prefixEnd_5965437 := by exact prefixLift 5965437
  have htrace : WordTrace (prefixWord ++ tailWord_5965437) baseStart_5965437 baseEnd_5965437 := by
    simpa [prefixWord, tailWord_5965437, baseEnd_5965437] using wordTrace_append hprefix tailTrace_5965437
  have hstable : (prefixWord ++ tailWord_5965437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965437).length < 2 ^ (prefixWord ++ tailWord_5965437).sum := by decide
  have hdescent : baseEnd_5965437 < baseStart_5965437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965463 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_5965463 : Nat := 118140960795 + 5965463 * 2 ^ 59
def prefixEnd_5965463 : Nat := 4983230072969 + 3 ^ 40 * 5965463 * 2
def baseEnd_5965463 : Nat := 3063149845612298832277841

theorem tailTrace_5965463 : CollatzResearch.WordTrace tailWord_5965463 prefixEnd_5965463 3063149845612298832277841 := by
  unfold tailWord_5965463
  simp only [CollatzResearch.WordTrace]
  refine ⟨217578310387153845813109043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145052206924769230542072695 217578310387153845813109043)
  ·
    refine ⟨326367465580730768719663565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217578310387153845813109043 326367465580730768719663565)
    ·
      refine ⟨122387799592774038269873837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326367465580730768719663565 122387799592774038269873837)
      ·
        refine ⟨45895424847290264351202689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122387799592774038269873837 45895424847290264351202689)
        ·
          refine ⟨34421568635467698263402017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45895424847290264351202689 34421568635467698263402017)
          ·
            refine ⟨25816176476600773697551513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34421568635467698263402017 25816176476600773697551513)
            ·
              refine ⟨19362132357450580273163635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25816176476600773697551513 19362132357450580273163635)
              ·
                refine ⟨29043198536175870409745453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19362132357450580273163635 29043198536175870409745453)
                ·
                  refine ⟨10891199451065951403654545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29043198536175870409745453 10891199451065951403654545)
                  ·
                    refine ⟨8168399588299463552740909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10891199451065951403654545 8168399588299463552740909)
                    ·
                      refine ⟨3063149845612298832277841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8168399588299463552740909 3063149845612298832277841)
                      ·
                        rfl

theorem cell23_5965463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_5965463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965463 prefixEnd_5965463 := by exact prefixLift 5965463
  have htrace : WordTrace (prefixWord ++ tailWord_5965463) baseStart_5965463 baseEnd_5965463 := by
    simpa [prefixWord, tailWord_5965463, baseEnd_5965463] using wordTrace_append hprefix tailTrace_5965463
  have hstable : (prefixWord ++ tailWord_5965463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965463).length < 2 ^ (prefixWord ++ tailWord_5965463).sum := by decide
  have hdescent : baseEnd_5965463 < baseStart_5965463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965473 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5965473 : Nat := 118140960795 + 5965473 * 2 ^ 59
def prefixEnd_5965473 : Nat := 4983230072969 + 3 ^ 40 * 5965473 * 2
def baseEnd_5965473 : Nat := 3063154980418843793152795

theorem tailTrace_5965473 : CollatzResearch.WordTrace tailWord_5965473 prefixEnd_5965473 3063154980418843793152795 := by
  unfold tailWord_5965473
  simp only [CollatzResearch.WordTrace]
  refine ⟨217578675117117617520973073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145052450078078411680648715 217578675117117617520973073)
  ·
    refine ⟨163184006337838213140729805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217578675117117617520973073 163184006337838213140729805)
    ·
      refine ⟨61194002376689329927773677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163184006337838213140729805 61194002376689329927773677)
      ·
        refine ⟨22947750891258498722915129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61194002376689329927773677 22947750891258498722915129)
        ·
          refine ⟨17210813168443874042186347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22947750891258498722915129 17210813168443874042186347)
          ·
            refine ⟨25816219752665811063279521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17210813168443874042186347 25816219752665811063279521)
            ·
              refine ⟨19362164814499358297459641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25816219752665811063279521 19362164814499358297459641)
              ·
                refine ⟨14521623610874518723094731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19362164814499358297459641 14521623610874518723094731)
                ·
                  refine ⟨21782435416311778084642097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14521623610874518723094731 21782435416311778084642097)
                  ·
                    refine ⟨16336826562233833563481573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21782435416311778084642097 16336826562233833563481573)
                    ·
                      refine ⟨3063154980418843793152795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16336826562233833563481573 3063154980418843793152795)
                      ·
                        rfl

theorem cell23_5965473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5965473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965473 prefixEnd_5965473 := by exact prefixLift 5965473
  have htrace : WordTrace (prefixWord ++ tailWord_5965473) baseStart_5965473 baseEnd_5965473 := by
    simpa [prefixWord, tailWord_5965473, baseEnd_5965473] using wordTrace_append hprefix tailTrace_5965473
  have hstable : (prefixWord ++ tailWord_5965473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965473).length < 2 ^ (prefixWord ++ tailWord_5965473).sum := by decide
  have hdescent : baseEnd_5965473 < baseStart_5965473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965474 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_5965474 : Nat := 118140960795 + 5965474 * 2 ^ 59
def prefixEnd_5965474 : Nat := 4983230072969 + 3 ^ 40 * 5965474 * 2
def baseEnd_5965474 : Nat := 1021051831299832763080097

theorem tailTrace_5965474 : CollatzResearch.WordTrace tailWord_5965474 prefixEnd_5965474 1021051831299832763080097 := by
  unfold tailWord_5965474
  simp only [CollatzResearch.WordTrace]
  refine ⟨54394677897528498672939869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145052474393409329794506317 54394677897528498672939869)
  ·
    refine ⟨20398004211573187002352451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54394677897528498672939869 20398004211573187002352451)
    ·
      refine ⟨30597006317359780503528677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20398004211573187002352451 30597006317359780503528677)
      ·
        refine ⟨5736938684504958844411627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30597006317359780503528677 5736938684504958844411627)
        ·
          refine ⟨8605408026757438266617441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5736938684504958844411627 8605408026757438266617441)
          ·
            refine ⟨6454056020068078699963081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8605408026757438266617441 6454056020068078699963081)
            ·
              refine ⟨4840542015051059024972311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6454056020068078699963081 4840542015051059024972311)
              ·
                refine ⟨7260813022576588537458467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4840542015051059024972311 7260813022576588537458467)
                ·
                  refine ⟨10891219533864882806187701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7260813022576588537458467 10891219533864882806187701)
                  ·
                    refine ⟨1021051831299832763080097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10891219533864882806187701 1021051831299832763080097)
                    ·
                      rfl

theorem cell23_5965474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_5965474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965474 prefixEnd_5965474 := by exact prefixLift 5965474
  have htrace : WordTrace (prefixWord ++ tailWord_5965474) baseStart_5965474 baseEnd_5965474 := by
    simpa [prefixWord, tailWord_5965474, baseEnd_5965474] using wordTrace_append hprefix tailTrace_5965474
  have hstable : (prefixWord ++ tailWord_5965474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965474).length < 2 ^ (prefixWord ++ tailWord_5965474).sum := by decide
  have hdescent : baseEnd_5965474 < baseStart_5965474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965477 : List Nat := [1, 3, 1, 2, 1, 2, 3, 5, 1, 2, 2]
def baseStart_5965477 : Nat := 118140960795 + 5965477 * 2 ^ 59
def prefixEnd_5965477 : Nat := 4983230072969 + 3 ^ 40 * 5965477 * 2
def baseEnd_5965477 : Nat := 3063157034341461777502777

theorem tailTrace_5965477 : CollatzResearch.WordTrace tailWord_5965477 prefixEnd_5965477 3063157034341461777502777 := by
  unfold tailWord_5965477
  simp only [CollatzResearch.WordTrace]
  refine ⟨217578821009103126204118685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145052547339402084136079123 217578821009103126204118685)
  ·
    refine ⟨81592057878413672326544507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217578821009103126204118685 81592057878413672326544507)
    ·
      refine ⟨122388086817620508489816761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81592057878413672326544507 122388086817620508489816761)
      ·
        refine ⟨91791065113215381367362571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122388086817620508489816761 91791065113215381367362571)
        ·
          refine ⟨137686597669823072051043857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91791065113215381367362571 137686597669823072051043857)
          ·
            refine ⟨103264948252367304038282893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137686597669823072051043857 103264948252367304038282893)
            ·
              refine ⟨38724355594637739014356085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103264948252367304038282893 38724355594637739014356085)
              ·
                refine ⟨3630408336997288032595883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38724355594637739014356085 3630408336997288032595883)
                ·
                  refine ⟨5445612505495932048893825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630408336997288032595883 5445612505495932048893825)
                  ·
                    refine ⟨4084209379121949036670369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5445612505495932048893825 4084209379121949036670369)
                    ·
                      refine ⟨3063157034341461777502777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084209379121949036670369 3063157034341461777502777)
                      ·
                        rfl

theorem cell23_5965477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_5965477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965477 prefixEnd_5965477 := by exact prefixLift 5965477
  have htrace : WordTrace (prefixWord ++ tailWord_5965477) baseStart_5965477 baseEnd_5965477 := by
    simpa [prefixWord, tailWord_5965477, baseEnd_5965477] using wordTrace_append hprefix tailTrace_5965477
  have hstable : (prefixWord ++ tailWord_5965477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965477).length < 2 ^ (prefixWord ++ tailWord_5965477).sum := by decide
  have hdescent : baseEnd_5965477 < baseStart_5965477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965494 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_5965494 : Nat := 118140960795 + 5965494 * 2 ^ 59
def prefixEnd_5965494 : Nat := 4983230072969 + 3 ^ 40 * 5965494 * 2
def baseEnd_5965494 : Nat := 3063165763512588210990199

theorem tailTrace_5965494 : CollatzResearch.WordTrace tailWord_5965494 prefixEnd_5965494 3063165763512588210990199 := by
  unfold tailWord_5965494
  simp only [CollatzResearch.WordTrace]
  refine ⟨13598715065627596131717971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145052960700027692071658357 13598715065627596131717971)
  ·
    refine ⟨20398072598441394197576957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13598715065627596131717971 20398072598441394197576957)
    ·
      refine ⟨7649277224415522824091359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20398072598441394197576957 7649277224415522824091359)
      ·
        refine ⟨11473915836623284236137039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649277224415522824091359 11473915836623284236137039)
        ·
          refine ⟨17210873754934926354205559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11473915836623284236137039 17210873754934926354205559)
          ·
            refine ⟨25816310632402389531308339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17210873754934926354205559 25816310632402389531308339)
            ·
              refine ⟨38724465948603584296962509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25816310632402389531308339 38724465948603584296962509)
              ·
                refine ⟨14521674730726344111360941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38724465948603584296962509 14521674730726344111360941)
                ·
                  refine ⟨5445628024022379041760353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14521674730726344111360941 5445628024022379041760353)
                  ·
                    refine ⟨4084221018016784281320265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5445628024022379041760353 4084221018016784281320265)
                    ·
                      refine ⟨3063165763512588210990199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084221018016784281320265 3063165763512588210990199)
                      ·
                        rfl

theorem cell23_5965494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_5965494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965494 prefixEnd_5965494 := by exact prefixLift 5965494
  have htrace : WordTrace (prefixWord ++ tailWord_5965494) baseStart_5965494 baseEnd_5965494 := by
    simpa [prefixWord, tailWord_5965494, baseEnd_5965494] using wordTrace_append hprefix tailTrace_5965494
  have hstable : (prefixWord ++ tailWord_5965494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965494).length < 2 ^ (prefixWord ++ tailWord_5965494).sum := by decide
  have hdescent : baseEnd_5965494 < baseStart_5965494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965517 : List Nat := [1, 6, 2, 1, 1, 3, 2, 7]
def baseStart_5965517 : Nat := 118140960795 + 5965517 * 2 ^ 59
def prefixEnd_5965517 : Nat := 4983230072969 + 3 ^ 40 * 5965517 * 2
def baseEnd_5965517 : Nat := 113451021243245985963059

theorem tailTrace_5965517 : CollatzResearch.WordTrace tailWord_5965517 prefixEnd_5965517 113451021243245985963059 := by
  unfold tailWord_5965517
  simp only [CollatzResearch.WordTrace]
  refine ⟨217580279928958213035574805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145053519952638808690383203 217580279928958213035574805)
  ·
    refine ⟨10199075621669916236042569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 217580279928958213035574805 10199075621669916236042569)
    ·
      refine ⟨7649306716252437177031927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10199075621669916236042569 7649306716252437177031927)
      ·
        refine ⟨11473960074378655765547891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649306716252437177031927 11473960074378655765547891)
        ·
          refine ⟨17210940111567983648321837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11473960074378655765547891 17210940111567983648321837)
          ·
            refine ⟨6454102541837993868120689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17210940111567983648321837 6454102541837993868120689)
            ·
              refine ⟨4840576906378495401090517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6454102541837993868120689 4840576906378495401090517)
              ·
                refine ⟨113451021243245985963059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4840576906378495401090517 113451021243245985963059)
                ·
                  rfl

theorem cell23_5965517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 7].length) (baseStart_5965517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965517 prefixEnd_5965517 := by exact prefixLift 5965517
  have htrace : WordTrace (prefixWord ++ tailWord_5965517) baseStart_5965517 baseEnd_5965517 := by
    simpa [prefixWord, tailWord_5965517, baseEnd_5965517] using wordTrace_append hprefix tailTrace_5965517
  have hstable : (prefixWord ++ tailWord_5965517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965517).length < 2 ^ (prefixWord ++ tailWord_5965517).sum := by decide
  have hdescent : baseEnd_5965517 < baseStart_5965517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965536 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_5965536 : Nat := 118140960795 + 5965536 * 2 ^ 59
def prefixEnd_5965536 : Nat := 4983230072969 + 3 ^ 40 * 5965536 * 2
def baseEnd_5965536 : Nat := 3063187329700077046665005

theorem tailTrace_5965536 : CollatzResearch.WordTrace tailWord_5965536 prefixEnd_5965536 3063187329700077046665005 := by
  unfold tailWord_5965536
  simp only [CollatzResearch.WordTrace]
  refine ⟨108790486457944689640258231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145053981943926252853677641 108790486457944689640258231)
  ·
    refine ⟨163185729686917034460387347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108790486457944689640258231 163185729686917034460387347)
    ·
      refine ⟨244778594530375551690581021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163185729686917034460387347 244778594530375551690581021)
      ·
        refine ⟨91791972948890831883967883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244778594530375551690581021 91791972948890831883967883)
        ·
          refine ⟨137687959423336247825951825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91791972948890831883967883 137687959423336247825951825)
          ·
            refine ⟨103265969567502185869463869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137687959423336247825951825 103265969567502185869463869)
            ·
              refine ⟨38724738587813319701048951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103265969567502185869463869 38724738587813319701048951)
              ·
                refine ⟨58087107881719979551573427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38724738587813319701048951 58087107881719979551573427)
                ·
                  refine ⟨87130661822579969327360141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58087107881719979551573427 87130661822579969327360141)
                  ·
                    refine ⟨32673998183467488497760053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87130661822579969327360141 32673998183467488497760053)
                    ·
                      refine ⟨3063187329700077046665005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32673998183467488497760053 3063187329700077046665005)
                      ·
                        rfl

theorem cell23_5965536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_5965536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965536 prefixEnd_5965536 := by exact prefixLift 5965536
  have htrace : WordTrace (prefixWord ++ tailWord_5965536) baseStart_5965536 baseEnd_5965536 := by
    simpa [prefixWord, tailWord_5965536, baseEnd_5965536] using wordTrace_append hprefix tailTrace_5965536
  have hstable : (prefixWord ++ tailWord_5965536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965536).length < 2 ^ (prefixWord ++ tailWord_5965536).sum := by decide
  have hdescent : baseEnd_5965536 < baseStart_5965536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965603 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 2, 5]
def baseStart_5965603 : Nat := 118140960795 + 5965603 * 2 ^ 59
def prefixEnd_5965603 : Nat := 4983230072969 + 3 ^ 40 * 5965603 * 2
def baseEnd_5965603 : Nat := 1021073910967976094842399

theorem tailTrace_5965603 : CollatzResearch.WordTrace tailWord_5965603 prefixEnd_5965603 1021073910967976094842399 := by
  unfold tailWord_5965603
  simp only [CollatzResearch.WordTrace]
  refine ⟨217583416606646649723205463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145055611071097766482136975 217583416606646649723205463)
  ·
    refine ⟨326375124909969974584808195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217583416606646649723205463 326375124909969974584808195)
    ·
      refine ⟨489562687364954961877212293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326375124909969974584808195 489562687364954961877212293)
      ·
        refine ⟨91793003880929055351977305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 489562687364954961877212293 91793003880929055351977305)
        ·
          refine ⟨68844752910696791513982979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91793003880929055351977305 68844752910696791513982979)
          ·
            refine ⟨103267129366045187270974469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68844752910696791513982979 103267129366045187270974469)
            ·
              refine ⟨19362586756133472613307713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103267129366045187270974469 19362586756133472613307713)
              ·
                refine ⟨14521940067100104459980785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19362586756133472613307713 14521940067100104459980785)
                ·
                  refine ⟨10891455050325078344985589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14521940067100104459980785 10891455050325078344985589)
                  ·
                    refine ⟨1021073910967976094842399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10891455050325078344985589 1021073910967976094842399)
                    ·
                      rfl

theorem cell23_5965603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 5].length) (baseStart_5965603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965603 prefixEnd_5965603 := by exact prefixLift 5965603
  have htrace : WordTrace (prefixWord ++ tailWord_5965603) baseStart_5965603 baseEnd_5965603 := by
    simpa [prefixWord, tailWord_5965603, baseEnd_5965603] using wordTrace_append hprefix tailTrace_5965603
  have hstable : (prefixWord ++ tailWord_5965603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965603).length < 2 ^ (prefixWord ++ tailWord_5965603).sum := by decide
  have hdescent : baseEnd_5965603 < baseStart_5965603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965616 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 4, 8]
def baseStart_5965616 : Nat := 118140960795 + 5965616 * 2 ^ 59
def prefixEnd_5965616 : Nat := 4983230072969 + 3 ^ 40 * 5965616 * 2
def baseEnd_5965616 : Nat := 1021076136050812244554879

theorem tailTrace_5965616 : CollatzResearch.WordTrace tailWord_5965616 prefixEnd_5965616 1021076136050812244554879 := by
  unfold tailWord_5965616
  simp only [CollatzResearch.WordTrace]
  refine ⟨108791945377799776471714351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145055927170399701962285801 108791945377799776471714351)
  ·
    refine ⟨163187918066699664707571527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108791945377799776471714351 163187918066699664707571527)
    ·
      refine ⟨244781877100049497061357291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163187918066699664707571527 244781877100049497061357291)
      ·
        refine ⟨367172815650074245592035937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244781877100049497061357291 367172815650074245592035937)
        ·
          refine ⟨275379611737555684194026953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367172815650074245592035937 275379611737555684194026953)
          ·
            refine ⟨206534708803166763145520215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275379611737555684194026953 206534708803166763145520215)
            ·
              refine ⟨309802063204750144718280323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206534708803166763145520215 309802063204750144718280323)
              ·
                refine ⟨464703094807125217077420485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309802063204750144718280323 464703094807125217077420485)
                ·
                  refine ⟨87131830276335978202016341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 464703094807125217077420485 87131830276335978202016341)
                  ·
                    refine ⟨1021076136050812244554879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87131830276335978202016341 1021076136050812244554879)
                    ·
                      rfl

theorem cell23_5965616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_5965616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965616 prefixEnd_5965616 := by exact prefixLift 5965616
  have htrace : WordTrace (prefixWord ++ tailWord_5965616) baseStart_5965616 baseEnd_5965616 := by
    simpa [prefixWord, tailWord_5965616, baseEnd_5965616] using wordTrace_append hprefix tailTrace_5965616
  have hstable : (prefixWord ++ tailWord_5965616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965616).length < 2 ^ (prefixWord ++ tailWord_5965616).sum := by decide
  have hdescent : baseEnd_5965616 < baseStart_5965616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965640 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_5965640 : Nat := 118140960795 + 5965640 * 2 ^ 59
def prefixEnd_5965640 : Nat := 4983230072969 + 3 ^ 40 * 5965640 * 2
def baseEnd_5965640 : Nat := 3063240731688144639764527

theorem tailTrace_5965640 : CollatzResearch.WordTrace tailWord_5965640 prefixEnd_5965640 3063240731688144639764527 := by
  unfold tailWord_5965640
  simp only [CollatzResearch.WordTrace]
  refine ⟨108792383053756302521151187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145056510738341736694868249 108792383053756302521151187)
  ·
    refine ⟨163188574580634453781726781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108792383053756302521151187 163188574580634453781726781)
    ·
      refine ⟨61195715467737920168147543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163188574580634453781726781 61195715467737920168147543)
      ·
        refine ⟨91793573201606880252221315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61195715467737920168147543 91793573201606880252221315)
        ·
          refine ⟨137690359802410320378331973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91793573201606880252221315 137690359802410320378331973)
          ·
            refine ⟨25816942462951935070937245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137690359802410320378331973 25816942462951935070937245)
            ·
              refine ⟨9681353423606975651601467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25816942462951935070937245 9681353423606975651601467)
              ·
                refine ⟨14522030135410463477402201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681353423606975651601467 14522030135410463477402201)
                ·
                  refine ⟨10891522601557847608051651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14522030135410463477402201 10891522601557847608051651)
                  ·
                    refine ⟨16337283902336771412077477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10891522601557847608051651 16337283902336771412077477)
                    ·
                      refine ⟨3063240731688144639764527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16337283902336771412077477 3063240731688144639764527)
                      ·
                        rfl

theorem cell23_5965640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_5965640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965640 prefixEnd_5965640 := by exact prefixLift 5965640
  have htrace : WordTrace (prefixWord ++ tailWord_5965640) baseStart_5965640 baseEnd_5965640 := by
    simpa [prefixWord, tailWord_5965640, baseEnd_5965640] using wordTrace_append hprefix tailTrace_5965640
  have hstable : (prefixWord ++ tailWord_5965640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965640).length < 2 ^ (prefixWord ++ tailWord_5965640).sum := by decide
  have hdescent : baseEnd_5965640 < baseStart_5965640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965653 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5965653 : Nat := 118140960795 + 5965653 * 2 ^ 59
def prefixEnd_5965653 : Nat := 4983230072969 + 3 ^ 40 * 5965653 * 2
def baseEnd_5965653 : Nat := 3063247406936653088901967

theorem tailTrace_5965653 : CollatzResearch.WordTrace tailWord_5965653 prefixEnd_5965653 3063247406936653088901967 := by
  unfold tailWord_5965653
  simp only [CollatzResearch.WordTrace]
  refine ⟨217585240256465508262525613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145056826837643672175017075 217585240256465508262525613)
  ·
    refine ⟨81594465096174565598447105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217585240256465508262525613 81594465096174565598447105)
    ·
      refine ⟨61195848822130924198835329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81594465096174565598447105 61195848822130924198835329)
      ·
        refine ⟨45896886616598193149126497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61195848822130924198835329 45896886616598193149126497)
        ·
          refine ⟨34422664962448644861844873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45896886616598193149126497 34422664962448644861844873)
          ·
            refine ⟨25816998721836483646383655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34422664962448644861844873 25816998721836483646383655)
            ·
              refine ⟨38725498082754725469575483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25816998721836483646383655 38725498082754725469575483)
              ·
                refine ⟨58088247124132088204363225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38725498082754725469575483 58088247124132088204363225)
                ·
                  refine ⟨43566185343099066153272419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58088247124132088204363225 43566185343099066153272419)
                  ·
                    refine ⟨65349278014648599229908629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43566185343099066153272419 65349278014648599229908629)
                    ·
                      refine ⟨3063247406936653088901967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65349278014648599229908629 3063247406936653088901967)
                      ·
                        rfl

theorem cell23_5965653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5965653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965653 prefixEnd_5965653 := by exact prefixLift 5965653
  have htrace : WordTrace (prefixWord ++ tailWord_5965653) baseStart_5965653 baseEnd_5965653 := by
    simpa [prefixWord, tailWord_5965653, baseEnd_5965653] using wordTrace_append hprefix tailTrace_5965653
  have hstable : (prefixWord ++ tailWord_5965653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965653).length < 2 ^ (prefixWord ++ tailWord_5965653).sum := by decide
  have hdescent : baseEnd_5965653 < baseStart_5965653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965663 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 8]
def baseStart_5965663 : Nat := 118140960795 + 5965663 * 2 ^ 59
def prefixEnd_5965663 : Nat := 4983230072969 + 3 ^ 40 * 5965663 * 2
def baseEnd_5965663 : Nat := 340361393527022005530769

theorem tailTrace_5965663 : CollatzResearch.WordTrace tailWord_5965663 prefixEnd_5965663 340361393527022005530769 := by
  unfold tailWord_5965663
  simp only [CollatzResearch.WordTrace]
  refine ⟨217585604986429279970389643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145057069990952853313593095 217585604986429279970389643)
  ·
    refine ⟨326378407479643919955584465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217585604986429279970389643 326378407479643919955584465)
    ·
      refine ⟨244783805609732939966688349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326378407479643919955584465 244783805609732939966688349)
      ·
        refine ⟨91793927103649852487508131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244783805609732939966688349 91793927103649852487508131)
        ·
          refine ⟨137690890655474778731262197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91793927103649852487508131 137690890655474778731262197)
          ·
            refine ⟨12908520998950760506055831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137690890655474778731262197 12908520998950760506055831)
            ·
              refine ⟨19362781498426140759083747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12908520998950760506055831 19362781498426140759083747)
              ·
                refine ⟨29044172247639211138625621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19362781498426140759083747 29044172247639211138625621)
                ·
                  refine ⟨340361393527022005530769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29044172247639211138625621 340361393527022005530769)
                  ·
                    rfl

theorem cell23_5965663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 8].length) (baseStart_5965663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965663 prefixEnd_5965663 := by exact prefixLift 5965663
  have htrace : WordTrace (prefixWord ++ tailWord_5965663) baseStart_5965663 baseEnd_5965663 := by
    simpa [prefixWord, tailWord_5965663, baseEnd_5965663] using wordTrace_append hprefix tailTrace_5965663
  have hstable : (prefixWord ++ tailWord_5965663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965663).length < 2 ^ (prefixWord ++ tailWord_5965663).sum := by decide
  have hdescent : baseEnd_5965663 < baseStart_5965663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965667 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 3, 4]
def baseStart_5965667 : Nat := 118140960795 + 5965667 * 2 ^ 59
def prefixEnd_5965667 : Nat := 4983230072969 + 3 ^ 40 * 5965667 * 2
def baseEnd_5965667 : Nat := 1021084865221938678042301

theorem tailTrace_5965667 : CollatzResearch.WordTrace tailWord_5965667 prefixEnd_5965667 1021084865221938678042301 := by
  unfold tailWord_5965667
  simp only [CollatzResearch.WordTrace]
  refine ⟨217585750878414788653535255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145057167252276525769023503 217585750878414788653535255)
  ·
    refine ⟨326378626317622182980302883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217585750878414788653535255 326378626317622182980302883)
    ·
      refine ⟨489567939476433274470454325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326378626317622182980302883 489567939476433274470454325)
      ·
        refine ⟨45896994325915619481605093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 489567939476433274470454325 45896994325915619481605093)
        ·
          refine ⟨8605686436109178652800955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45896994325915619481605093 8605686436109178652800955)
          ·
            refine ⟨12908529654163767979201433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8605686436109178652800955 12908529654163767979201433)
            ·
              refine ⟨9681397240622825984401075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12908529654163767979201433 9681397240622825984401075)
              ·
                refine ⟨14522095860934238976601613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681397240622825984401075 14522095860934238976601613)
                ·
                  refine ⟨5445785947850339616225605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14522095860934238976601613 5445785947850339616225605)
                  ·
                    refine ⟨1021084865221938678042301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5445785947850339616225605 1021084865221938678042301)
                    ·
                      rfl

theorem cell23_5965667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 4].length) (baseStart_5965667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965667 prefixEnd_5965667 := by exact prefixLift 5965667
  have htrace : WordTrace (prefixWord ++ tailWord_5965667) baseStart_5965667 baseEnd_5965667 := by
    simpa [prefixWord, tailWord_5965667, baseEnd_5965667] using wordTrace_append hprefix tailTrace_5965667
  have hstable : (prefixWord ++ tailWord_5965667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965667).length < 2 ^ (prefixWord ++ tailWord_5965667).sum := by decide
  have hdescent : baseEnd_5965667 < baseStart_5965667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965717 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_5965717 : Nat := 118140960795 + 5965717 * 2 ^ 59
def prefixEnd_5965717 : Nat := 4983230072969 + 3 ^ 40 * 5965717 * 2
def baseEnd_5965717 : Nat := 3063280269698540838501673

theorem tailTrace_5965717 : CollatzResearch.WordTrace tailWord_5965717 prefixEnd_5965717 3063280269698540838501673 := by
  unfold tailWord_5965717
  simp only [CollatzResearch.WordTrace]
  refine ⟨217587574528233647192855405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145058383018822431461903603 217587574528233647192855405)
  ·
    refine ⟨81595340448087617697320777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217587574528233647192855405 81595340448087617697320777)
    ·
      refine ⟨61196505336065713272990583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81595340448087617697320777 61196505336065713272990583)
      ·
        refine ⟨91794758004098569909485875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61196505336065713272990583 91794758004098569909485875)
        ·
          refine ⟨137692137006147854864228813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91794758004098569909485875 137692137006147854864228813)
          ·
            refine ⟨51634551377305445574085805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137692137006147854864228813 51634551377305445574085805)
            ·
              refine ⟨19362956766489542090282177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51634551377305445574085805 19362956766489542090282177)
              ·
                refine ⟨14522217574867156567711633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19362956766489542090282177 14522217574867156567711633)
                ·
                  refine ⟨10891663181150367425783725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14522217574867156567711633 10891663181150367425783725)
                  ·
                    refine ⟨4084373692931387784668897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10891663181150367425783725 4084373692931387784668897)
                    ·
                      refine ⟨3063280269698540838501673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084373692931387784668897 3063280269698540838501673)
                      ·
                        rfl

theorem cell23_5965717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_5965717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965717 prefixEnd_5965717 := by exact prefixLift 5965717
  have htrace : WordTrace (prefixWord ++ tailWord_5965717) baseStart_5965717 baseEnd_5965717 := by
    simpa [prefixWord, tailWord_5965717, baseEnd_5965717] using wordTrace_append hprefix tailTrace_5965717
  have hstable : (prefixWord ++ tailWord_5965717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965717).length < 2 ^ (prefixWord ++ tailWord_5965717).sum := by decide
  have hdescent : baseEnd_5965717 < baseStart_5965717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965718 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5965718 : Nat := 118140960795 + 5965718 * 2 ^ 59
def prefixEnd_5965718 : Nat := 4983230072969 + 3 ^ 40 * 5965718 * 2
def baseEnd_5965718 : Nat := 1021093594393065111529723

theorem tailTrace_5965718 : CollatzResearch.WordTrace tailWord_5965718 prefixEnd_5965718 1021093594393065111529723 := by
  unfold tailWord_5965718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13599225687576876522727613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145058407334153349575761205 13599225687576876522727613)
  ·
    refine ⟨5099709632841328696022855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13599225687576876522727613 5099709632841328696022855)
    ·
      refine ⟨7649564449261993044034283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5099709632841328696022855 7649564449261993044034283)
      ·
        refine ⟨11474346673892989566051425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649564449261993044034283 11474346673892989566051425)
        ·
          refine ⟨8605760005419742174538569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11474346673892989566051425 8605760005419742174538569)
          ·
            refine ⟨6454320004064806630903927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8605760005419742174538569 6454320004064806630903927)
            ·
              refine ⟨9681480006097209946355891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6454320004064806630903927 9681480006097209946355891)
              ·
                refine ⟨14522220009145814919533837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681480006097209946355891 14522220009145814919533837)
                ·
                  refine ⟨5445832503429680594825189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14522220009145814919533837 5445832503429680594825189)
                  ·
                    refine ⟨1021093594393065111529723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5445832503429680594825189 1021093594393065111529723)
                    ·
                      rfl

theorem cell23_5965718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5965718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965718 prefixEnd_5965718 := by exact prefixLift 5965718
  have htrace : WordTrace (prefixWord ++ tailWord_5965718) baseStart_5965718 baseEnd_5965718 := by
    simpa [prefixWord, tailWord_5965718, baseEnd_5965718] using wordTrace_append hprefix tailTrace_5965718
  have hstable : (prefixWord ++ tailWord_5965718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965718).length < 2 ^ (prefixWord ++ tailWord_5965718).sum := by decide
  have hdescent : baseEnd_5965718 < baseStart_5965718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965724 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5965724 : Nat := 118140960795 + 5965724 * 2 ^ 59
def prefixEnd_5965724 : Nat := 4983230072969 + 3 ^ 40 * 5965724 * 2
def baseEnd_5965724 : Nat := 3063283864063122311114141

theorem tailTrace_5965724 : CollatzResearch.WordTrace tailWord_5965724 prefixEnd_5965724 3063283864063122311114141 := by
  unfold tailWord_5965724
  simp only [CollatzResearch.WordTrace]
  refine ⟨108793914919604143694180113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145058553226138858258906817 108793914919604143694180113)
  ·
    refine ⟨81595436189703107770635085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108793914919604143694180113 81595436189703107770635085)
    ·
      refine ⟨30598288571138665413988157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81595436189703107770635085 30598288571138665413988157)
      ·
        refine ⟨11474358214176999530245559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30598288571138665413988157 11474358214176999530245559)
        ·
          refine ⟨17211537321265499295368339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11474358214176999530245559 17211537321265499295368339)
          ·
            refine ⟨25817305981898248943052509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17211537321265499295368339 25817305981898248943052509)
            ·
              refine ⟨9681489743211843353644691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25817305981898248943052509 9681489743211843353644691)
              ·
                refine ⟨14522234614817765030467037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681489743211843353644691 14522234614817765030467037)
                ·
                  refine ⟨5445837980556661886425139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14522234614817765030467037 5445837980556661886425139)
                  ·
                    refine ⟨8168756970834992829637709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5445837980556661886425139 8168756970834992829637709)
                    ·
                      refine ⟨3063283864063122311114141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8168756970834992829637709 3063283864063122311114141)
                      ·
                        rfl

theorem cell23_5965724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5965724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965724 prefixEnd_5965724 := by exact prefixLift 5965724
  have htrace : WordTrace (prefixWord ++ tailWord_5965724) baseStart_5965724 baseEnd_5965724 := by
    simpa [prefixWord, tailWord_5965724, baseEnd_5965724] using wordTrace_append hprefix tailTrace_5965724
  have hstable : (prefixWord ++ tailWord_5965724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965724).length < 2 ^ (prefixWord ++ tailWord_5965724).sum := by decide
  have hdescent : baseEnd_5965724 < baseStart_5965724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965743 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_5965743 : Nat := 118140960795 + 5965743 * 2 ^ 59
def prefixEnd_5965743 : Nat := 4983230072969 + 3 ^ 40 * 5965743 * 2
def baseEnd_5965743 : Nat := 3063293620195557736776553

theorem tailTrace_5965743 : CollatzResearch.WordTrace tailWord_5965743 prefixEnd_5965743 3063293620195557736776553 := by
  unfold tailWord_5965743
  simp only [CollatzResearch.WordTrace]
  refine ⟨217588522826139453633301883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145059015217426302422201255 217588522826139453633301883)
  ·
    refine ⟨326382784239209180449952825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217588522826139453633301883 326382784239209180449952825)
    ·
      refine ⟨244787088179406885337464619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326382784239209180449952825 244787088179406885337464619)
      ·
        refine ⟨367180632269110328006196929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244787088179406885337464619 367180632269110328006196929)
        ·
          refine ⟨275385474201832746004647697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367180632269110328006196929 275385474201832746004647697)
          ·
            refine ⟨206539105651374559503485773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275385474201832746004647697 206539105651374559503485773)
            ·
              refine ⟨77452164619265459813807165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206539105651374559503485773 77452164619265459813807165)
              ·
                refine ⟨29044561732224547430177687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77452164619265459813807165 29044561732224547430177687)
                ·
                  refine ⟨43566842598336821145266531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29044561732224547430177687 43566842598336821145266531)
                  ·
                    refine ⟨65350263897505231717899797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43566842598336821145266531 65350263897505231717899797)
                    ·
                      refine ⟨3063293620195557736776553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65350263897505231717899797 3063293620195557736776553)
                      ·
                        rfl

theorem cell23_5965743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_5965743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965743 prefixEnd_5965743 := by exact prefixLift 5965743
  have htrace : WordTrace (prefixWord ++ tailWord_5965743) baseStart_5965743 baseEnd_5965743 := by
    simpa [prefixWord, tailWord_5965743, baseEnd_5965743] using wordTrace_append hprefix tailTrace_5965743
  have hstable : (prefixWord ++ tailWord_5965743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965743).length < 2 ^ (prefixWord ++ tailWord_5965743).sum := by decide
  have hdescent : baseEnd_5965743 < baseStart_5965743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965747 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 5, 2, 2]
def baseStart_5965747 : Nat := 118140960795 + 5965747 * 2 ^ 59
def prefixEnd_5965747 : Nat := 4983230072969 + 3 ^ 40 * 5965747 * 2
def baseEnd_5965747 : Nat := 3063295674118175721126535

theorem tailTrace_5965747 : CollatzResearch.WordTrace tailWord_5965747 prefixEnd_5965747 3063295674118175721126535 := by
  unfold tailWord_5965747
  simp only [CollatzResearch.WordTrace]
  refine ⟨217588668718124962316447495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145059112478749974877631663 217588668718124962316447495)
  ·
    refine ⟨326383003077187443474671243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217588668718124962316447495 326383003077187443474671243)
    ·
      refine ⟨489574504615781165212006865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326383003077187443474671243 489574504615781165212006865)
      ·
        refine ⟨367180878461835873909005149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489574504615781165212006865 367180878461835873909005149)
        ·
          refine ⟨137692829423188452715876931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 367180878461835873909005149 137692829423188452715876931)
          ·
            refine ⟨206539244134782679073815397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137692829423188452715876931 206539244134782679073815397)
            ·
              refine ⟨38726108275271752326340387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206539244134782679073815397 38726108275271752326340387)
              ·
                refine ⟨58089162412907628489510581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38726108275271752326340387 58089162412907628489510581)
                ·
                  refine ⟨5445858976210090170891617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58089162412907628489510581 5445858976210090170891617)
                  ·
                    refine ⟨4084394232157567628168713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5445858976210090170891617 4084394232157567628168713)
                    ·
                      refine ⟨3063295674118175721126535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084394232157567628168713 3063295674118175721126535)
                      ·
                        rfl

theorem cell23_5965747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 5, 2, 2].length) (baseStart_5965747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965747 prefixEnd_5965747 := by exact prefixLift 5965747
  have htrace : WordTrace (prefixWord ++ tailWord_5965747) baseStart_5965747 baseEnd_5965747 := by
    simpa [prefixWord, tailWord_5965747, baseEnd_5965747] using wordTrace_append hprefix tailTrace_5965747
  have hstable : (prefixWord ++ tailWord_5965747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965747).length < 2 ^ (prefixWord ++ tailWord_5965747).sum := by decide
  have hdescent : baseEnd_5965747 < baseStart_5965747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965753 : List Nat := [1, 2, 1, 4, 2, 1, 1, 11]
def baseStart_5965753 : Nat := 118140960795 + 5965753 * 2 ^ 59
def prefixEnd_5965753 : Nat := 4983230072969 + 3 ^ 40 * 5965753 * 2
def baseEnd_5965753 : Nat := 113455509444522322135241

theorem tailTrace_5965753 : CollatzResearch.WordTrace tailWord_5965753 prefixEnd_5965753 113455509444522322135241 := by
  unfold tailWord_5965753
  simp only [CollatzResearch.WordTrace]
  refine ⟨217588887556103225341165913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145059258370735483560777275 217588887556103225341165913)
  ·
    refine ⟨163191665667077419005874435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217588887556103225341165913 163191665667077419005874435)
    ·
      refine ⟨244787498500616128508811653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163191665667077419005874435 244787498500616128508811653)
      ·
        refine ⟨45897655968865524095402185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244787498500616128508811653 45897655968865524095402185)
        ·
          refine ⟨34423241976649143071551639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45897655968865524095402185 34423241976649143071551639)
          ·
            refine ⟨51634862964973714607327459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34423241976649143071551639 51634862964973714607327459)
            ·
              refine ⟨77452294447460571910991189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51634862964973714607327459 77452294447460571910991189)
              ·
                refine ⟨113455509444522322135241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 77452294447460571910991189 113455509444522322135241)
                ·
                  rfl

theorem cell23_5965753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 11].length) (baseStart_5965753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965753 prefixEnd_5965753 := by exact prefixLift 5965753
  have htrace : WordTrace (prefixWord ++ tailWord_5965753) baseStart_5965753 baseEnd_5965753 := by
    simpa [prefixWord, tailWord_5965753, baseEnd_5965753] using wordTrace_append hprefix tailTrace_5965753
  have hstable : (prefixWord ++ tailWord_5965753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965753).length < 2 ^ (prefixWord ++ tailWord_5965753).sum := by decide
  have hdescent : baseEnd_5965753 < baseStart_5965753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965760 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_5965760 : Nat := 118140960795 + 5965760 * 2 ^ 59
def prefixEnd_5965760 : Nat := 4983230072969 + 3 ^ 40 * 5965760 * 2
def baseEnd_5965760 : Nat := 3063302349366684170263975

theorem tailTrace_5965760 : CollatzResearch.WordTrace tailWord_5965760 prefixEnd_5965760 3063302349366684170263975 := by
  unfold tailWord_5965760
  simp only [CollatzResearch.WordTrace]
  refine ⟨108794571433538932768335367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145059428578051910357780489 108794571433538932768335367)
  ·
    refine ⟨163191857150308399152503051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108794571433538932768335367 163191857150308399152503051)
    ·
      refine ⟨244787785725462598728754577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163191857150308399152503051 244787785725462598728754577)
      ·
        refine ⟨183590839294096949046565933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244787785725462598728754577 183590839294096949046565933)
        ·
          refine ⟨68846564735286355892462225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183590839294096949046565933 68846564735286355892462225)
          ·
            refine ⟨51634923551464766919346669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68846564735286355892462225 51634923551464766919346669)
            ·
              refine ⟨19363096331799287594755001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51634923551464766919346669 19363096331799287594755001)
              ·
                refine ⟨14522322248849465696066251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19363096331799287594755001 14522322248849465696066251)
                ·
                  refine ⟨21783483373274198544099377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14522322248849465696066251 21783483373274198544099377)
                  ·
                    refine ⟨16337612529955648908074533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21783483373274198544099377 16337612529955648908074533)
                    ·
                      refine ⟨3063302349366684170263975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16337612529955648908074533 3063302349366684170263975)
                      ·
                        rfl

theorem cell23_5965760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_5965760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965760 prefixEnd_5965760 := by exact prefixLift 5965760
  have htrace : WordTrace (prefixWord ++ tailWord_5965760) baseStart_5965760 baseEnd_5965760 := by
    simpa [prefixWord, tailWord_5965760, baseEnd_5965760] using wordTrace_append hprefix tailTrace_5965760
  have hstable : (prefixWord ++ tailWord_5965760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965760).length < 2 ^ (prefixWord ++ tailWord_5965760).sum := by decide
  have hdescent : baseEnd_5965760 < baseStart_5965760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965783 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 1, 9]
def baseStart_5965783 : Nat := 118140960795 + 5965783 * 2 ^ 59
def prefixEnd_5965783 : Nat := 4983230072969 + 3 ^ 40 * 5965783 * 2
def baseEnd_5965783 : Nat := 1021104719807245860092123

theorem tailTrace_5965783 : CollatzResearch.WordTrace tailWord_5965783 prefixEnd_5965783 1021104719807245860092123 := by
  unfold tailWord_5965783
  simp only [CollatzResearch.WordTrace]
  refine ⟨217589981745994540464758003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145059987830663026976505335 217589981745994540464758003)
  ·
    refine ⟨326384972618991810697137005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217589981745994540464758003 326384972618991810697137005)
    ·
      refine ⟨122394364732121929011426377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326384972618991810697137005 122394364732121929011426377)
      ·
        refine ⟨91795773549091446758569783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122394364732121929011426377 91795773549091446758569783)
        ·
          refine ⟨137693660323637170137854675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91795773549091446758569783 137693660323637170137854675)
          ·
            refine ⟨206540490485455755206782013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137693660323637170137854675 206540490485455755206782013)
            ·
              refine ⟨77452683932045908202543255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206540490485455755206782013 77452683932045908202543255)
              ·
                refine ⟨116179025898068862303814883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77452683932045908202543255 116179025898068862303814883)
                ·
                  refine ⟨174268538847103293455722325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116179025898068862303814883 174268538847103293455722325)
                  ·
                    refine ⟨1021104719807245860092123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 174268538847103293455722325 1021104719807245860092123)
                    ·
                      rfl

theorem cell23_5965783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_5965783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965783 prefixEnd_5965783 := by exact prefixLift 5965783
  have htrace : WordTrace (prefixWord ++ tailWord_5965783) baseStart_5965783 baseEnd_5965783 := by
    simpa [prefixWord, tailWord_5965783, baseEnd_5965783] using wordTrace_append hprefix tailTrace_5965783
  have hstable : (prefixWord ++ tailWord_5965783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965783).length < 2 ^ (prefixWord ++ tailWord_5965783).sum := by decide
  have hdescent : baseEnd_5965783 < baseStart_5965783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965807 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 3, 3, 2]
def baseStart_5965807 : Nat := 118140960795 + 5965807 * 2 ^ 59
def prefixEnd_5965807 : Nat := 4983230072969 + 3 ^ 40 * 5965807 * 2
def baseEnd_5965807 : Nat := 3063326482957445486376259

theorem tailTrace_5965807 : CollatzResearch.WordTrace tailWord_5965807 prefixEnd_5965807 3063326482957445486376259 := by
  unfold tailWord_5965807
  simp only [CollatzResearch.WordTrace]
  refine ⟨217590857097907592563631675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145060571398605061709087783 217590857097907592563631675)
  ·
    refine ⟨326386285646861388845447513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217590857097907592563631675 326386285646861388845447513)
    ·
      refine ⟨244789714235146041634085635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326386285646861388845447513 244789714235146041634085635)
      ·
        refine ⟨367184571352719062451128453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244789714235146041634085635 367184571352719062451128453)
        ·
          refine ⟨68847107128634824209586585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367184571352719062451128453 68847107128634824209586585)
          ·
            refine ⟨51635330346476118157189939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68847107128634824209586585 51635330346476118157189939)
            ·
              refine ⟨77452995519714177235784909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51635330346476118157189939 77452995519714177235784909)
              ·
                refine ⟨29044873319892816463419341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77452995519714177235784909 29044873319892816463419341)
                ·
                  refine ⟨10891827494959806173782253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29044873319892816463419341 10891827494959806173782253)
                  ·
                    refine ⟨4084435310609927315168345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10891827494959806173782253 4084435310609927315168345)
                    ·
                      refine ⟨3063326482957445486376259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084435310609927315168345 3063326482957445486376259)
                      ·
                        rfl

theorem cell23_5965807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 3, 2].length) (baseStart_5965807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965807 prefixEnd_5965807 := by exact prefixLift 5965807
  have htrace : WordTrace (prefixWord ++ tailWord_5965807) baseStart_5965807 baseEnd_5965807 := by
    simpa [prefixWord, tailWord_5965807, baseEnd_5965807] using wordTrace_append hprefix tailTrace_5965807
  have hstable : (prefixWord ++ tailWord_5965807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965807).length < 2 ^ (prefixWord ++ tailWord_5965807).sum := by decide
  have hdescent : baseEnd_5965807 < baseStart_5965807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965831 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_5965831 : Nat := 118140960795 + 5965831 * 2 ^ 59
def prefixEnd_5965831 : Nat := 4983230072969 + 3 ^ 40 * 5965831 * 2
def baseEnd_5965831 : Nat := 3063338806493153392476149

theorem tailTrace_5965831 : CollatzResearch.WordTrace tailWord_5965831 prefixEnd_5965831 3063338806493153392476149 := by
  unfold tailWord_5965831
  simp only [CollatzResearch.WordTrace]
  refine ⟨217591732449820644662505347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145061154966547096441670231 217591732449820644662505347)
  ·
    refine ⟨326387598674730966993758021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217591732449820644662505347 326387598674730966993758021)
    ·
      refine ⟨61197674751512056311329629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 326387598674730966993758021 61197674751512056311329629)
      ·
        refine ⟨22949128031817021116748611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61197674751512056311329629 22949128031817021116748611)
        ·
          refine ⟨34423692047725531675122917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22949128031817021116748611 34423692047725531675122917)
          ·
            refine ⟨6454442258948537189085547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34423692047725531675122917 6454442258948537189085547)
            ·
              refine ⟨9681663388422805783628321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6454442258948537189085547 9681663388422805783628321)
              ·
                refine ⟨7261247541317104337721241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9681663388422805783628321 7261247541317104337721241)
                ·
                  refine ⟨5445935655987828253290931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7261247541317104337721241 5445935655987828253290931)
                  ·
                    refine ⟨8168903483981742379936397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5445935655987828253290931 8168903483981742379936397)
                    ·
                      refine ⟨3063338806493153392476149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8168903483981742379936397 3063338806493153392476149)
                      ·
                        rfl

theorem cell23_5965831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_5965831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965831 prefixEnd_5965831 := by exact prefixLift 5965831
  have htrace : WordTrace (prefixWord ++ tailWord_5965831) baseStart_5965831 baseEnd_5965831 := by
    simpa [prefixWord, tailWord_5965831, baseEnd_5965831] using wordTrace_append hprefix tailTrace_5965831
  have hstable : (prefixWord ++ tailWord_5965831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965831).length < 2 ^ (prefixWord ++ tailWord_5965831).sum := by decide
  have hdescent : baseEnd_5965831 < baseStart_5965831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965897 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 2, 5, 2]
def baseStart_5965897 : Nat := 118140960795 + 5965897 * 2 ^ 59
def prefixEnd_5965897 : Nat := 4983230072969 + 3 ^ 40 * 5965897 * 2
def baseEnd_5965897 : Nat := 3063372696216350134250845

theorem tailTrace_5965897 : CollatzResearch.WordTrace tailWord_5965897 prefixEnd_5965897 3063372696216350134250845 := by
  unfold tailWord_5965897
  simp only [CollatzResearch.WordTrace]
  refine ⟨217594139667581537934407945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145062759778387691956271963 217594139667581537934407945)
  ·
    refine ⟨163195604750686153450805959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217594139667581537934407945 163195604750686153450805959)
    ·
      refine ⟨244793407126029230176208939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163195604750686153450805959 244793407126029230176208939)
      ·
        refine ⟨367190110689043845264313409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244793407126029230176208939 367190110689043845264313409)
        ·
          refine ⟨275392583016782883948235057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367190110689043845264313409 275392583016782883948235057)
          ·
            refine ⟨206544437262587162961176293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275392583016782883948235057 206544437262587162961176293)
            ·
              refine ⟨38727081986735093055220555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 206544437262587162961176293 38727081986735093055220555)
              ·
                refine ⟨58090622980102639582830833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38727081986735093055220555 58090622980102639582830833)
                ·
                  refine ⟨43567967235076979687123125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58090622980102639582830833 43567967235076979687123125)
                  ·
                    refine ⟨4084496928288466845667793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43567967235076979687123125 4084496928288466845667793)
                    ·
                      refine ⟨3063372696216350134250845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084496928288466845667793 3063372696216350134250845)
                      ·
                        rfl

theorem cell23_5965897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 5, 2].length) (baseStart_5965897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965897 prefixEnd_5965897 := by exact prefixLift 5965897
  have htrace : WordTrace (prefixWord ++ tailWord_5965897) baseStart_5965897 baseEnd_5965897 := by
    simpa [prefixWord, tailWord_5965897, baseEnd_5965897] using wordTrace_append hprefix tailTrace_5965897
  have hstable : (prefixWord ++ tailWord_5965897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965897).length < 2 ^ (prefixWord ++ tailWord_5965897).sum := by decide
  have hdescent : baseEnd_5965897 < baseStart_5965897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965900 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_5965900 : Nat := 118140960795 + 5965900 * 2 ^ 59
def prefixEnd_5965900 : Nat := 4983230072969 + 3 ^ 40 * 5965900 * 2
def baseEnd_5965900 : Nat := 3063374236658313622513331

theorem tailTrace_5965900 : CollatzResearch.WordTrace tailWord_5965900 prefixEnd_5965900 3063374236658313622513331 := by
  unfold tailWord_5965900
  simp only [CollatzResearch.WordTrace]
  refine ⟨108797124543285334723383577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145062832724380446297844769 108797124543285334723383577)
  ·
    refine ⟨81597843407464001042537683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108797124543285334723383577 81597843407464001042537683)
    ·
      refine ⟨122396765111196001563806525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81597843407464001042537683 122396765111196001563806525)
      ·
        refine ⟨45898786916698500586427447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122396765111196001563806525 45898786916698500586427447)
        ·
          refine ⟨68848180375047750879641171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45898786916698500586427447 68848180375047750879641171)
          ·
            refine ⟨103272270562571626319461757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68848180375047750879641171 103272270562571626319461757)
            ·
              refine ⟨38727101460964359869798159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103272270562571626319461757 38727101460964359869798159)
              ·
                refine ⟨58090652191446539804697239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38727101460964359869798159 58090652191446539804697239)
                ·
                  refine ⟨87135978287169809707045859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58090652191446539804697239 87135978287169809707045859)
                  ·
                    refine ⟨130703967430754714560568789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87135978287169809707045859 130703967430754714560568789)
                    ·
                      refine ⟨3063374236658313622513331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130703967430754714560568789 3063374236658313622513331)
                      ·
                        rfl

theorem cell23_5965900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_5965900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965900 prefixEnd_5965900 := by exact prefixLift 5965900
  have htrace : WordTrace (prefixWord ++ tailWord_5965900) baseStart_5965900 baseEnd_5965900 := by
    simpa [prefixWord, tailWord_5965900, baseEnd_5965900] using wordTrace_append hprefix tailTrace_5965900
  have hstable : (prefixWord ++ tailWord_5965900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965900).length < 2 ^ (prefixWord ++ tailWord_5965900).sum := by decide
  have hdescent : baseEnd_5965900 < baseStart_5965900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965978 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4]
def baseStart_5965978 : Nat := 118140960795 + 5965978 * 2 ^ 59
def prefixEnd_5965978 : Nat := 4983230072969 + 3 ^ 40 * 5965978 * 2
def baseEnd_5965978 : Nat := 3063414288149364317337973

theorem tailTrace_5965978 : CollatzResearch.WordTrace tailWord_5965978 prefixEnd_5965978 3063414288149364317337973 := by
  unfold tailWord_5965978
  simp only [CollatzResearch.WordTrace]
  refine ⟨54399273495072022192026647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145064729320192059178737725 54399273495072022192026647)
  ·
    refine ⟨81598910242608033288039971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54399273495072022192026647 81598910242608033288039971)
    ·
      refine ⟨122398365363912049932059957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81598910242608033288039971 122398365363912049932059957)
      ·
        refine ⟨11474846752866754681130621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122398365363912049932059957 11474846752866754681130621)
        ·
          refine ⟨4303067532325033005423983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11474846752866754681130621 4303067532325033005423983)
          ·
            refine ⟨6454601298487549508135975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303067532325033005423983 6454601298487549508135975)
            ·
              refine ⟨9681901947731324262203963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6454601298487549508135975 9681901947731324262203963)
              ·
                refine ⟨14522852921596986393305945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681901947731324262203963 14522852921596986393305945)
                ·
                  refine ⟨10892139691197739794979459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14522852921596986393305945 10892139691197739794979459)
                  ·
                    refine ⟨16338209536796609692469189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10892139691197739794979459 16338209536796609692469189)
                    ·
                      refine ⟨3063414288149364317337973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16338209536796609692469189 3063414288149364317337973)
                      ·
                        rfl

theorem cell23_5965978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_5965978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965978 prefixEnd_5965978 := by exact prefixLift 5965978
  have htrace : WordTrace (prefixWord ++ tailWord_5965978) baseStart_5965978 baseEnd_5965978 := by
    simpa [prefixWord, tailWord_5965978, baseEnd_5965978] using wordTrace_append hprefix tailTrace_5965978
  have hstable : (prefixWord ++ tailWord_5965978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965978).length < 2 ^ (prefixWord ++ tailWord_5965978).sum := by decide
  have hdescent : baseEnd_5965978 < baseStart_5965978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965981 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_5965981 : Nat := 118140960795 + 5965981 * 2 ^ 59
def prefixEnd_5965981 : Nat := 4983230072969 + 3 ^ 40 * 5965981 * 2
def baseEnd_5965981 : Nat := 3063415828591327805600459

theorem tailTrace_5965981 : CollatzResearch.WordTrace tailWord_5965981 prefixEnd_5965981 3063415828591327805600459 := by
  unfold tailWord_5965981
  simp only [CollatzResearch.WordTrace]
  refine ⟨217597203399277220280465797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145064802266184813520310531 217597203399277220280465797)
  ·
    refine ⟨40799475637364478802587337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217597203399277220280465797 40799475637364478802587337)
    ·
      refine ⟨30599606728023359101940503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40799475637364478802587337 30599606728023359101940503)
      ·
        refine ⟨45899410092035038652910755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30599606728023359101940503 45899410092035038652910755)
        ·
          refine ⟨68849115138052557979366133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45899410092035038652910755 68849115138052557979366133)
          ·
            refine ⟨6454604544192427310565575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68849115138052557979366133 6454604544192427310565575)
            ·
              refine ⟨9681906816288640965848363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6454604544192427310565575 9681906816288640965848363)
              ·
                refine ⟨14522860224432961448772545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681906816288640965848363 14522860224432961448772545)
                ·
                  refine ⟨10892145168324721086579409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14522860224432961448772545 10892145168324721086579409)
                  ·
                    refine ⟨8169108876243540814934557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10892145168324721086579409 8169108876243540814934557)
                    ·
                      refine ⟨3063415828591327805600459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8169108876243540814934557 3063415828591327805600459)
                      ·
                        rfl

theorem cell23_5965981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_5965981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965981 prefixEnd_5965981 := by exact prefixLift 5965981
  have htrace : WordTrace (prefixWord ++ tailWord_5965981) baseStart_5965981 baseEnd_5965981 := by
    simpa [prefixWord, tailWord_5965981, baseEnd_5965981] using wordTrace_append hprefix tailTrace_5965981
  have hstable : (prefixWord ++ tailWord_5965981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965981).length < 2 ^ (prefixWord ++ tailWord_5965981).sum := by decide
  have hdescent : baseEnd_5965981 < baseStart_5965981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5965988 : List Nat := [2, 3, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_5965988 : Nat := 118140960795 + 5965988 * 2 ^ 59
def prefixEnd_5965988 : Nat := 4983230072969 + 3 ^ 40 * 5965988 * 2
def baseEnd_5965988 : Nat := 1021139807651969759404309

theorem tailTrace_5965988 : CollatzResearch.WordTrace tailWord_5965988 prefixEnd_5965988 1021139807651969759404309 := by
  unfold tailWord_5965988
  simp only [CollatzResearch.WordTrace]
  refine ⟨108798729355125930237985309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145064972473501240317313745 108798729355125930237985309)
  ·
    refine ⟨40799523508172223839244491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108798729355125930237985309 40799523508172223839244491)
    ·
      refine ⟨61199285262258335758866737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40799523508172223839244491 61199285262258335758866737)
      ·
        refine ⟨45899463946693751819150053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61199285262258335758866737 45899463946693751819150053)
        ·
          refine ⟨8606149490005078466090635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45899463946693751819150053 8606149490005078466090635)
          ·
            refine ⟨12909224235007617699135953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8606149490005078466090635 12909224235007617699135953)
            ·
              refine ⟨9681918176255713274351965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12909224235007617699135953 9681918176255713274351965)
              ·
                refine ⟨3630719316095892477881987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9681918176255713274351965 3630719316095892477881987)
                ·
                  refine ⟨5446078974143838716822981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630719316095892477881987 5446078974143838716822981)
                  ·
                    refine ⟨1021139807651969759404309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446078974143838716822981 1021139807651969759404309)
                    ·
                      rfl

theorem cell23_5965988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_5965988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5965988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5965988 prefixEnd_5965988 := by exact prefixLift 5965988
  have htrace : WordTrace (prefixWord ++ tailWord_5965988) baseStart_5965988 baseEnd_5965988 := by
    simpa [prefixWord, tailWord_5965988, baseEnd_5965988] using wordTrace_append hprefix tailTrace_5965988
  have hstable : (prefixWord ++ tailWord_5965988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5965988).length < 2 ^ (prefixWord ++ tailWord_5965988).sum := by decide
  have hdescent : baseEnd_5965988 < baseStart_5965988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5965988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966001 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 6]
def baseStart_5966001 : Nat := 118140960795 + 5966001 * 2 ^ 59
def prefixEnd_5966001 : Nat := 4983230072969 + 3 ^ 40 * 5966001 * 2
def baseEnd_5966001 : Nat := 340380677578268636372263

theorem tailTrace_5966001 : CollatzResearch.WordTrace tailWord_5966001 prefixEnd_5966001 340380677578268636372263 := by
  unfold tailWord_5966001
  simp only [CollatzResearch.WordTrace]
  refine ⟨217597932859204763696193857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145065288572803175797462571 217597932859204763696193857)
  ·
    refine ⟨163198449644403572772145393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217597932859204763696193857 163198449644403572772145393)
    ·
      refine ⟨122398837233302679579109045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163198449644403572772145393 122398837233302679579109045)
      ·
        refine ⟨11474890990622126210541473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122398837233302679579109045 11474890990622126210541473)
        ·
          refine ⟨8606168242966594657906105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11474890990622126210541473 8606168242966594657906105)
          ·
            refine ⟨6454626182224945993429579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8606168242966594657906105 6454626182224945993429579)
            ·
              refine ⟨9681939273337418990144369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6454626182224945993429579 9681939273337418990144369)
              ·
                refine ⟨7261454455003064242608277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9681939273337418990144369 7261454455003064242608277)
                ·
                  refine ⟨340380677578268636372263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7261454455003064242608277 340380677578268636372263)
                  ·
                    rfl

theorem cell23_5966001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 6].length) (baseStart_5966001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966001 prefixEnd_5966001 := by exact prefixLift 5966001
  have htrace : WordTrace (prefixWord ++ tailWord_5966001) baseStart_5966001 baseEnd_5966001 := by
    simpa [prefixWord, tailWord_5966001, baseEnd_5966001] using wordTrace_append hprefix tailTrace_5966001
  have hstable : (prefixWord ++ tailWord_5966001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966001).length < 2 ^ (prefixWord ++ tailWord_5966001).sum := by decide
  have hdescent : baseEnd_5966001 < baseStart_5966001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966011 : List Nat := [1, 1, 1, 1, 1, 2, 5, 6, 1, 1, 3]
def baseStart_5966011 : Nat := 118140960795 + 5966011 * 2 ^ 59
def prefixEnd_5966011 : Nat := 4983230072969 + 3 ^ 40 * 5966011 * 2
def baseEnd_5966011 : Nat := 3063431233010962688225321

theorem tailTrace_5966011 : CollatzResearch.WordTrace tailWord_5966011 prefixEnd_5966011 3063431233010962688225321 := by
  unfold tailWord_5966011
  simp only [CollatzResearch.WordTrace]
  refine ⟨217598297589168535404057887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145065531726112356936038591 217598297589168535404057887)
  ·
    refine ⟨326397446383752803106086831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217598297589168535404057887 326397446383752803106086831)
    ·
      refine ⟨489596169575629204659130247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326397446383752803106086831 489596169575629204659130247)
      ·
        refine ⟨734394254363443806988695371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489596169575629204659130247 734394254363443806988695371)
        ·
          refine ⟨1101591381545165710483043057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734394254363443806988695371 1101591381545165710483043057)
          ·
            refine ⟨826193536158874282862282293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101591381545165710483043057 826193536158874282862282293)
            ·
              refine ⟨77455644014894464018338965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 826193536158874282862282293 77455644014894464018338965)
              ·
                refine ⟨3630733313198178000859639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77455644014894464018338965 3630733313198178000859639)
                ·
                  refine ⟨5446099969797267001289459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630733313198178000859639 5446099969797267001289459)
                  ·
                    refine ⟨8169149954695900501934189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5446099969797267001289459 8169149954695900501934189)
                    ·
                      refine ⟨3063431233010962688225321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8169149954695900501934189 3063431233010962688225321)
                      ·
                        rfl

theorem cell23_5966011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 1, 3].length) (baseStart_5966011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966011 prefixEnd_5966011 := by exact prefixLift 5966011
  have htrace : WordTrace (prefixWord ++ tailWord_5966011) baseStart_5966011 baseEnd_5966011 := by
    simpa [prefixWord, tailWord_5966011, baseEnd_5966011] using wordTrace_append hprefix tailTrace_5966011
  have hstable : (prefixWord ++ tailWord_5966011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966011).length < 2 ^ (prefixWord ++ tailWord_5966011).sum := by decide
  have hdescent : baseEnd_5966011 < baseStart_5966011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966038 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_5966038 : Nat := 118140960795 + 5966038 * 2 ^ 59
def prefixEnd_5966038 : Nat := 4983230072969 + 3 ^ 40 * 5966038 * 2
def baseEnd_5966038 : Nat := 3063445096988634082587697

theorem tailTrace_5966038 : CollatzResearch.WordTrace tailWord_5966038 prefixEnd_5966038 3063445096988634082587697 := by
  unfold tailWord_5966038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13599955147504419938455673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145066188240047146010193845 13599955147504419938455673)
  ·
    refine ⟨10199966360628314953841755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13599955147504419938455673 10199966360628314953841755)
    ·
      refine ⟨15299949540942472430762633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10199966360628314953841755 15299949540942472430762633)
      ·
        refine ⟨11474962155706854323071975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15299949540942472430762633 11474962155706854323071975)
        ·
          refine ⟨17212443233560281484607963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11474962155706854323071975 17212443233560281484607963)
          ·
            refine ⟨25818664850340422226911945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17212443233560281484607963 25818664850340422226911945)
            ·
              refine ⟨19363998637755316670183959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25818664850340422226911945 19363998637755316670183959)
              ·
                refine ⟨29045997956632975005275939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19363998637755316670183959 29045997956632975005275939)
                ·
                  refine ⟨43568996934949462507913909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29045997956632975005275939 43568996934949462507913909)
                  ·
                    refine ⟨4084593462651512110116929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43568996934949462507913909 4084593462651512110116929)
                    ·
                      refine ⟨3063445096988634082587697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084593462651512110116929 3063445096988634082587697)
                      ·
                        rfl

theorem cell23_5966038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_5966038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966038 prefixEnd_5966038 := by exact prefixLift 5966038
  have htrace : WordTrace (prefixWord ++ tailWord_5966038) baseStart_5966038 baseEnd_5966038 := by
    simpa [prefixWord, tailWord_5966038, baseEnd_5966038] using wordTrace_append hprefix tailTrace_5966038
  have hstable : (prefixWord ++ tailWord_5966038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966038).length < 2 ^ (prefixWord ++ tailWord_5966038).sum := by decide
  have hdescent : baseEnd_5966038 < baseStart_5966038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966045 : List Nat := [1, 4, 3, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5966045 : Nat := 118140960795 + 5966045 * 2 ^ 59
def prefixEnd_5966045 : Nat := 4983230072969 + 3 ^ 40 * 5966045 * 2
def baseEnd_5966045 : Nat := 3063448691353215555200165

theorem tailTrace_5966045 : CollatzResearch.WordTrace tailWord_5966045 prefixEnd_5966045 3063448691353215555200165 := by
  unfold tailWord_5966045
  simp only [CollatzResearch.WordTrace]
  refine ⟨217599537671045359210795589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145066358447363572807197059 217599537671045359210795589)
  ·
    refine ⟨40799913313321004852024173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217599537671045359210795589 40799913313321004852024173)
    ·
      refine ⟨15299967492495376819509065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40799913313321004852024173 15299967492495376819509065)
      ·
        refine ⟨11474975619371532614631799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15299967492495376819509065 11474975619371532614631799)
        ·
          refine ⟨17212463429057298921947699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11474975619371532614631799 17212463429057298921947699)
          ·
            refine ⟨25818695143585948382921549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17212463429057298921947699 25818695143585948382921549)
            ·
              refine ⟨9682010678844730643595581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25818695143585948382921549 9682010678844730643595581)
              ·
                refine ⟨3630754004566773991348343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9682010678844730643595581 3630754004566773991348343)
                ·
                  refine ⟨5446131006850160987022515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630754004566773991348343 5446131006850160987022515)
                  ·
                    refine ⟨8169196510275241480533773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5446131006850160987022515 8169196510275241480533773)
                    ·
                      refine ⟨3063448691353215555200165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8169196510275241480533773 3063448691353215555200165)
                      ·
                        rfl

theorem cell23_5966045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5966045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966045 prefixEnd_5966045 := by exact prefixLift 5966045
  have htrace : WordTrace (prefixWord ++ tailWord_5966045) baseStart_5966045 baseEnd_5966045 := by
    simpa [prefixWord, tailWord_5966045, baseEnd_5966045] using wordTrace_append hprefix tailTrace_5966045
  have hstable : (prefixWord ++ tailWord_5966045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966045).length < 2 ^ (prefixWord ++ tailWord_5966045).sum := by decide
  have hdescent : baseEnd_5966045 < baseStart_5966045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966047 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_5966047 : Nat := 118140960795 + 5966047 * 2 ^ 59
def prefixEnd_5966047 : Nat := 4983230072969 + 3 ^ 40 * 5966047 * 2
def baseEnd_5966047 : Nat := 3063449718314524547375155

theorem tailTrace_5966047 : CollatzResearch.WordTrace tailWord_5966047 prefixEnd_5966047 3063449718314524547375155 := by
  unfold tailWord_5966047
  simp only [CollatzResearch.WordTrace]
  refine ⟨217599610617038113552368395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145066407078025409034912263 217599610617038113552368395)
  ·
    refine ⟨326399415925557170328552593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217599610617038113552368395 326399415925557170328552593)
    ·
      refine ⟨244799561944167877746414445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326399415925557170328552593 244799561944167877746414445)
      ·
        refine ⟨91799835729062954154905417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244799561944167877746414445 91799835729062954154905417)
        ·
          refine ⟨68849876796797215616179063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91799835729062954154905417 68849876796797215616179063)
          ·
            refine ⟨103274815195195823424268595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68849876796797215616179063 103274815195195823424268595)
            ·
              refine ⟨154912222792793735136402893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103274815195195823424268595 154912222792793735136402893)
              ·
                refine ⟨58092083547297650676151085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154912222792793735136402893 58092083547297650676151085)
                ·
                  refine ⟨21784531330236619003556657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58092083547297650676151085 21784531330236619003556657)
                  ·
                    refine ⟨16338398497677464252667493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21784531330236619003556657 16338398497677464252667493)
                    ·
                      refine ⟨3063449718314524547375155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16338398497677464252667493 3063449718314524547375155)
                      ·
                        rfl

theorem cell23_5966047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_5966047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966047 prefixEnd_5966047 := by exact prefixLift 5966047
  have htrace : WordTrace (prefixWord ++ tailWord_5966047) baseStart_5966047 baseEnd_5966047 := by
    simpa [prefixWord, tailWord_5966047, baseEnd_5966047] using wordTrace_append hprefix tailTrace_5966047
  have hstable : (prefixWord ++ tailWord_5966047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966047).length < 2 ^ (prefixWord ++ tailWord_5966047).sum := by decide
  have hdescent : baseEnd_5966047 < baseStart_5966047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966088 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_5966088 : Nat := 118140960795 + 5966088 * 2 ^ 59
def prefixEnd_5966088 : Nat := 4983230072969 + 3 ^ 40 * 5966088 * 2
def baseEnd_5966088 : Nat := 3063470771021358886962467

theorem tailTrace_5966088 : CollatzResearch.WordTrace tailWord_5966088 prefixEnd_5966088 3063470771021358886962467 := by
  unfold tailWord_5966088
  simp only [CollatzResearch.WordTrace]
  refine ⟨108800553004944788777305459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145067404006593051703073945 108800553004944788777305459)
  ·
    refine ⟨163200829507417183165958189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108800553004944788777305459 163200829507417183165958189)
    ·
      refine ⟨61200311065281443687234321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163200829507417183165958189 61200311065281443687234321)
      ·
        refine ⟨45900233298961082765425741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61200311065281443687234321 45900233298961082765425741)
        ·
          refine ⟨17212587487110406037034653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45900233298961082765425741 17212587487110406037034653)
          ·
            refine ⟨6454720307666402263887995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17212587487110406037034653 6454720307666402263887995)
            ·
              refine ⟨9682080461499603395831993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6454720307666402263887995 9682080461499603395831993)
              ·
                refine ⟨7261560346124702546873995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9682080461499603395831993 7261560346124702546873995)
                ·
                  refine ⟨10892340519187053820310993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7261560346124702546873995 10892340519187053820310993)
                  ·
                    refine ⟨8169255389390290365233245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10892340519187053820310993 8169255389390290365233245)
                    ·
                      refine ⟨3063470771021358886962467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8169255389390290365233245 3063470771021358886962467)
                      ·
                        rfl

theorem cell23_5966088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_5966088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966088 prefixEnd_5966088 := by exact prefixLift 5966088
  have htrace : WordTrace (prefixWord ++ tailWord_5966088) baseStart_5966088 baseEnd_5966088 := by
    simpa [prefixWord, tailWord_5966088, baseEnd_5966088] using wordTrace_append hprefix tailTrace_5966088
  have hstable : (prefixWord ++ tailWord_5966088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966088).length < 2 ^ (prefixWord ++ tailWord_5966088).sum := by decide
  have hdescent : baseEnd_5966088 < baseStart_5966088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966127 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_5966127 : Nat := 118140960795 + 5966127 * 2 ^ 59
def prefixEnd_5966127 : Nat := 4983230072969 + 3 ^ 40 * 5966127 * 2
def baseEnd_5966127 : Nat := 3063490796766884234374787

theorem tailTrace_5966127 : CollatzResearch.WordTrace tailWord_5966127 prefixEnd_5966127 3063490796766884234374787 := by
  unfold tailWord_5966127
  simp only [CollatzResearch.WordTrace]
  refine ⟨217602528456748287215280635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145068352304498858143520423 217602528456748287215280635)
  ·
    refine ⟨326403792685122430822920953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217602528456748287215280635 326403792685122430822920953)
    ·
      refine ⟨244802844513841823117190715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326403792685122430822920953 244802844513841823117190715)
      ·
        refine ⟨367204266770762734675786073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244802844513841823117190715 367204266770762734675786073)
        ·
          refine ⟨275403200078072051006839555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367204266770762734675786073 275403200078072051006839555)
          ·
            refine ⟨413104800117108076510259333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275403200078072051006839555 413104800117108076510259333)
            ·
              refine ⟨77457150021957764345673625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 413104800117108076510259333 77457150021957764345673625)
              ·
                refine ⟨58092862516468323259255219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77457150021957764345673625 58092862516468323259255219)
                ·
                  refine ⟨87139293774702484888882829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58092862516468323259255219 87139293774702484888882829)
                  ·
                    refine ⟨32677235165513431833331061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87139293774702484888882829 32677235165513431833331061)
                    ·
                      refine ⟨3063490796766884234374787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32677235165513431833331061 3063490796766884234374787)
                      ·
                        rfl

theorem cell23_5966127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_5966127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966127 prefixEnd_5966127 := by exact prefixLift 5966127
  have htrace : WordTrace (prefixWord ++ tailWord_5966127) baseStart_5966127 baseEnd_5966127 := by
    simpa [prefixWord, tailWord_5966127, baseEnd_5966127] using wordTrace_append hprefix tailTrace_5966127
  have hstable : (prefixWord ++ tailWord_5966127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966127).length < 2 ^ (prefixWord ++ tailWord_5966127).sum := by decide
  have hdescent : baseEnd_5966127 < baseStart_5966127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966147 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 9]
def baseStart_5966147 : Nat := 118140960795 + 5966147 * 2 ^ 59
def prefixEnd_5966147 : Nat := 4983230072969 + 3 ^ 40 * 5966147 * 2
def baseEnd_5966147 : Nat := 340389007375552684013855

theorem tailTrace_5966147 : CollatzResearch.WordTrace tailWord_5966147 prefixEnd_5966147 340389007375552684013855 := by
  unfold tailWord_5966147
  simp only [CollatzResearch.WordTrace]
  refine ⟨217603257916675830631008695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145068838611117220420672463 217603257916675830631008695)
  ·
    refine ⟨326404886875013745946513043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217603257916675830631008695 326404886875013745946513043)
    ·
      refine ⟨489607330312520618919769565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326404886875013745946513043 489607330312520618919769565)
      ·
        refine ⟨183602748867195232094913587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489607330312520618919769565 183602748867195232094913587)
        ·
          refine ⟨275404123300792848142370381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183602748867195232094913587 275404123300792848142370381)
          ·
            refine ⟨103276546237797318053388893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275404123300792848142370381 103276546237797318053388893)
            ·
              refine ⟨38728704839173994270020835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103276546237797318053388893 38728704839173994270020835)
              ·
                refine ⟨58093057258760991405031253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38728704839173994270020835 58093057258760991405031253)
                ·
                  refine ⟨340389007375552684013855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58093057258760991405031253 340389007375552684013855)
                  ·
                    rfl

theorem cell23_5966147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 9].length) (baseStart_5966147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966147 prefixEnd_5966147 := by exact prefixLift 5966147
  have htrace : WordTrace (prefixWord ++ tailWord_5966147) baseStart_5966147 baseEnd_5966147 := by
    simpa [prefixWord, tailWord_5966147, baseEnd_5966147] using wordTrace_append hprefix tailTrace_5966147
  have hstable : (prefixWord ++ tailWord_5966147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966147).length < 2 ^ (prefixWord ++ tailWord_5966147).sum := by decide
  have hdescent : baseEnd_5966147 < baseStart_5966147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966181 : List Nat := [1, 3, 1, 3, 1, 3, 2, 4, 5]
def baseStart_5966181 : Nat := 118140960795 + 5966181 * 2 ^ 59
def prefixEnd_5966181 : Nat := 4983230072969 + 3 ^ 40 * 5966181 * 2
def baseEnd_5966181 : Nat := 340390947191358558122171

theorem tailTrace_5966181 : CollatzResearch.WordTrace tailWord_5966181 prefixEnd_5966181 340390947191358558122171 := by
  unfold tailWord_5966181
  simp only [CollatzResearch.WordTrace]
  refine ⟨217604497998552654437746397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145069665332368436291830931 217604497998552654437746397)
  ·
    refine ⟨81601686749457245414154899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217604497998552654437746397 81601686749457245414154899)
    ·
      refine ⟨122402530124185868121232349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81601686749457245414154899 122402530124185868121232349)
      ·
        refine ⟨45900948796569700545462131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122402530124185868121232349 45900948796569700545462131)
        ·
          refine ⟨68851423194854550818193197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45900948796569700545462131 68851423194854550818193197)
          ·
            refine ⟨25819283698070456556822449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68851423194854550818193197 25819283698070456556822449)
            ·
              refine ⟨19364462773552842417616837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25819283698070456556822449 19364462773552842417616837)
              ·
                refine ⟨3630836770041157953303157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19364462773552842417616837 3630836770041157953303157)
                ·
                  refine ⟨340390947191358558122171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3630836770041157953303157 340390947191358558122171)
                  ·
                    rfl

theorem cell23_5966181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_5966181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966181 prefixEnd_5966181 := by exact prefixLift 5966181
  have htrace : WordTrace (prefixWord ++ tailWord_5966181) baseStart_5966181 baseEnd_5966181 := by
    simpa [prefixWord, tailWord_5966181, baseEnd_5966181] using wordTrace_append hprefix tailTrace_5966181
  have hstable : (prefixWord ++ tailWord_5966181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966181).length < 2 ^ (prefixWord ++ tailWord_5966181).sum := by decide
  have hdescent : baseEnd_5966181 < baseStart_5966181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966194 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_5966194 : Nat := 118140960795 + 5966194 * 2 ^ 59
def prefixEnd_5966194 : Nat := 4983230072969 + 3 ^ 40 * 5966194 * 2
def baseEnd_5966194 : Nat := 1021175066656911824078993

theorem tailTrace_5966194 : CollatzResearch.WordTrace tailWord_5966194 prefixEnd_5966194 1021175066656911824078993 := by
  unfold tailWord_5966194
  simp only [CollatzResearch.WordTrace]
  refine ⟨54401243036876389414492409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145069981431670371771979757 54401243036876389414492409)
  ·
    refine ⟨40800932277657292060869307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54401243036876389414492409 40800932277657292060869307)
    ·
      refine ⟨61201398416485938091303961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40800932277657292060869307 61201398416485938091303961)
      ·
        refine ⟨45901048812364453568477971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61201398416485938091303961 45901048812364453568477971)
        ·
          refine ⟨68851573218546680352716957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45901048812364453568477971 68851573218546680352716957)
          ·
            refine ⟨25819339956955005132268859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68851573218546680352716957 25819339956955005132268859)
            ·
              refine ⟨38729009935432507698403289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25819339956955005132268859 38729009935432507698403289)
              ·
                refine ⟨29046757451574380773802467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38729009935432507698403289 29046757451574380773802467)
                ·
                  refine ⟨43570136177361571160703701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29046757451574380773802467 43570136177361571160703701)
                  ·
                    refine ⟨1021175066656911824078993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43570136177361571160703701 1021175066656911824078993)
                    ·
                      rfl

theorem cell23_5966194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_5966194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966194 prefixEnd_5966194 := by exact prefixLift 5966194
  have htrace : WordTrace (prefixWord ++ tailWord_5966194) baseStart_5966194 baseEnd_5966194 := by
    simpa [prefixWord, tailWord_5966194, baseEnd_5966194] using wordTrace_append hprefix tailTrace_5966194
  have hstable : (prefixWord ++ tailWord_5966194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966194).length < 2 ^ (prefixWord ++ tailWord_5966194).sum := by decide
  have hdescent : baseEnd_5966194 < baseStart_5966194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966228 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_5966228 : Nat := 118140960795 + 5966228 * 2 ^ 59
def prefixEnd_5966228 : Nat := 4983230072969 + 3 ^ 40 * 5966228 * 2
def baseEnd_5966228 : Nat := 1021180886104329446403941

theorem tailTrace_5966228 : CollatzResearch.WordTrace tailWord_5966228 prefixEnd_5966228 1021180886104329446403941 := by
  unfold tailWord_5966228
  simp only [CollatzResearch.WordTrace]
  refine ⟨108803106114691190732353669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145070808152921587643138225 108803106114691190732353669)
  ·
    refine ⟨20400582396504598262316313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108803106114691190732353669 20400582396504598262316313)
    ·
      refine ⟨15300436797378448696737235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20400582396504598262316313 15300436797378448696737235)
      ·
        refine ⟨22950655196067673045105853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15300436797378448696737235 22950655196067673045105853)
        ·
          refine ⟨8606495698525377391914695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22950655196067673045105853 8606495698525377391914695)
          ·
            refine ⟨12909743547788066087872043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8606495698525377391914695 12909743547788066087872043)
            ·
              refine ⟨19364615321682099131808065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12909743547788066087872043 19364615321682099131808065)
              ·
                refine ⟨14523461491261574348856049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19364615321682099131808065 14523461491261574348856049)
                ·
                  refine ⟨10892596118446180761642037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14523461491261574348856049 10892596118446180761642037)
                  ·
                    refine ⟨1021180886104329446403941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10892596118446180761642037 1021180886104329446403941)
                    ·
                      rfl

theorem cell23_5966228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_5966228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966228 prefixEnd_5966228 := by exact prefixLift 5966228
  have htrace : WordTrace (prefixWord ++ tailWord_5966228) baseStart_5966228 baseEnd_5966228 := by
    simpa [prefixWord, tailWord_5966228, baseEnd_5966228] using wordTrace_append hprefix tailTrace_5966228
  have hstable : (prefixWord ++ tailWord_5966228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966228).length < 2 ^ (prefixWord ++ tailWord_5966228).sum := by decide
  have hdescent : baseEnd_5966228 < baseStart_5966228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966231 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 4, 4, 2]
def baseStart_5966231 : Nat := 118140960795 + 5966231 * 2 ^ 59
def prefixEnd_5966231 : Nat := 4983230072969 + 3 ^ 40 * 5966231 * 2
def baseEnd_5966231 : Nat := 3063544198754951827474309

theorem tailTrace_5966231 : CollatzResearch.WordTrace tailWord_5966231 prefixEnd_5966231 3063544198754951827474309 := by
  unfold tailWord_5966231
  simp only [CollatzResearch.WordTrace]
  refine ⟨217606321648371512977066547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145070881098914341984711031 217606321648371512977066547)
  ·
    refine ⟨326409482472557269465599821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217606321648371512977066547 326409482472557269465599821)
    ·
      refine ⟨122403555927208976049599933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326409482472557269465599821 122403555927208976049599933)
      ·
        refine ⟨45901333472703366018599975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122403555927208976049599933 45901333472703366018599975)
        ·
          refine ⟨68852000209055049027899963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45901333472703366018599975 68852000209055049027899963)
          ·
            refine ⟨103278000313582573541849945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68852000209055049027899963 103278000313582573541849945)
            ·
              refine ⟨77458500235186930156387459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103278000313582573541849945 77458500235186930156387459)
              ·
                refine ⟨116187750352780395234581189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77458500235186930156387459 116187750352780395234581189)
                ·
                  refine ⟨21785203191146324106483973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116187750352780395234581189 21785203191146324106483973)
                  ·
                    refine ⟨4084725598339935769965745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21785203191146324106483973 4084725598339935769965745)
                    ·
                      refine ⟨3063544198754951827474309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084725598339935769965745 3063544198754951827474309)
                      ·
                        rfl

theorem cell23_5966231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_5966231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966231 prefixEnd_5966231 := by exact prefixLift 5966231
  have htrace : WordTrace (prefixWord ++ tailWord_5966231) baseStart_5966231 baseEnd_5966231 := by
    simpa [prefixWord, tailWord_5966231, baseEnd_5966231] using wordTrace_append hprefix tailTrace_5966231
  have hstable : (prefixWord ++ tailWord_5966231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966231).length < 2 ^ (prefixWord ++ tailWord_5966231).sum := by decide
  have hdescent : baseEnd_5966231 < baseStart_5966231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966238 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5966238 : Nat := 118140960795 + 5966238 * 2 ^ 59
def prefixEnd_5966238 : Nat := 4983230072969 + 3 ^ 40 * 5966238 * 2
def baseEnd_5966238 : Nat := 3063547793119533300086777

theorem tailTrace_5966238 : CollatzResearch.WordTrace tailWord_5966238 prefixEnd_5966238 3063547793119533300086777 := by
  unfold tailWord_5966238
  simp only [CollatzResearch.WordTrace]
  refine ⟨27200822119918269146571421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145071051306230768781714245 27200822119918269146571421)
  ·
    refine ⟨10200308294969350929964283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27200822119918269146571421 10200308294969350929964283)
    ·
      refine ⟨15300462442454026394946425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10200308294969350929964283 15300462442454026394946425)
      ·
        refine ⟨11475346831840519796209819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15300462442454026394946425 11475346831840519796209819)
        ·
          refine ⟨17213020247760779694314729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11475346831840519796209819 17213020247760779694314729)
          ·
            refine ⟨12909765185820584770736047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17213020247760779694314729 12909765185820584770736047)
            ·
              refine ⟨19364647778730877156104071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12909765185820584770736047 19364647778730877156104071)
              ·
                refine ⟨29046971668096315734156107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19364647778730877156104071 29046971668096315734156107)
                ·
                  refine ⟨43570457502144473601234161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29046971668096315734156107 43570457502144473601234161)
                  ·
                    refine ⟨32677843126608355200925621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43570457502144473601234161 32677843126608355200925621)
                    ·
                      refine ⟨3063547793119533300086777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32677843126608355200925621 3063547793119533300086777)
                      ·
                        rfl

theorem cell23_5966238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5966238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966238 prefixEnd_5966238 := by exact prefixLift 5966238
  have htrace : WordTrace (prefixWord ++ tailWord_5966238) baseStart_5966238 baseEnd_5966238 := by
    simpa [prefixWord, tailWord_5966238, baseEnd_5966238] using wordTrace_append hprefix tailTrace_5966238
  have hstable : (prefixWord ++ tailWord_5966238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966238).length < 2 ^ (prefixWord ++ tailWord_5966238).sum := by decide
  have hdescent : baseEnd_5966238 < baseStart_5966238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966244 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_5966244 : Nat := 118140960795 + 5966244 * 2 ^ 59
def prefixEnd_5966244 : Nat := 4983230072969 + 3 ^ 40 * 5966244 * 2
def baseEnd_5966244 : Nat := 3063550874003460276611749

theorem tailTrace_5966244 : CollatzResearch.WordTrace tailWord_5966244 prefixEnd_5966244 3063550874003460276611749 := by
  unfold tailWord_5966244
  simp only [CollatzResearch.WordTrace]
  refine ⟨108803397898662208098644893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145071197198216277464859857 108803397898662208098644893)
  ·
    refine ⟨40801274211998328036991835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108803397898662208098644893 40801274211998328036991835)
    ·
      refine ⟨61201911317997492055487753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40801274211998328036991835 61201911317997492055487753)
      ·
        refine ⟨45901433488498119041615815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61201911317997492055487753 45901433488498119041615815)
        ·
          refine ⟨68852150232747178562423723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45901433488498119041615815 68852150232747178562423723)
          ·
            refine ⟨103278225349120767843635585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68852150232747178562423723 103278225349120767843635585)
            ·
              refine ⟨77458669011840575882726689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103278225349120767843635585 77458669011840575882726689)
              ·
                refine ⟨58094001758880431912045017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77458669011840575882726689 58094001758880431912045017)
                ·
                  refine ⟨43570501319160323934033763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58094001758880431912045017 43570501319160323934033763)
                  ·
                    refine ⟨65355751978740485901050645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43570501319160323934033763 65355751978740485901050645)
                    ·
                      refine ⟨3063550874003460276611749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65355751978740485901050645 3063550874003460276611749)
                      ·
                        rfl

theorem cell23_5966244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_5966244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966244 prefixEnd_5966244 := by exact prefixLift 5966244
  have htrace : WordTrace (prefixWord ++ tailWord_5966244) baseStart_5966244 baseEnd_5966244 := by
    simpa [prefixWord, tailWord_5966244, baseEnd_5966244] using wordTrace_append hprefix tailTrace_5966244
  have hstable : (prefixWord ++ tailWord_5966244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966244).length < 2 ^ (prefixWord ++ tailWord_5966244).sum := by decide
  have hdescent : baseEnd_5966244 < baseStart_5966244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966268 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5966268 : Nat := 118140960795 + 5966268 * 2 ^ 59
def prefixEnd_5966268 : Nat := 4983230072969 + 3 ^ 40 * 5966268 * 2
def baseEnd_5966268 : Nat := 3063563197539168182711639

theorem tailTrace_5966268 : CollatzResearch.WordTrace tailWord_5966268 prefixEnd_5966268 3063563197539168182711639 := by
  unfold tailWord_5966268
  simp only [CollatzResearch.WordTrace]
  refine ⟨108803835574618734148081729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145071780766158312197442305 108803835574618734148081729)
  ·
    refine ⟨81602876680964050611061297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108803835574618734148081729 81602876680964050611061297)
    ·
      refine ⟨61202157510723037958295973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81602876680964050611061297 61202157510723037958295973)
      ·
        refine ⟨11475404533260569617180495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61202157510723037958295973 11475404533260569617180495)
        ·
          refine ⟨17213106799890854425770743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11475404533260569617180495 17213106799890854425770743)
          ·
            refine ⟨25819660199836281638656115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17213106799890854425770743 25819660199836281638656115)
            ·
              refine ⟨38729490299754422457984173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25819660199836281638656115 38729490299754422457984173)
              ·
                refine ⟨14523558862407908421744065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38729490299754422457984173 14523558862407908421744065)
                ·
                  refine ⟨10892669146805931316308049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14523558862407908421744065 10892669146805931316308049)
                  ·
                    refine ⟨8169501860104448487231037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10892669146805931316308049 8169501860104448487231037)
                    ·
                      refine ⟨3063563197539168182711639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8169501860104448487231037 3063563197539168182711639)
                      ·
                        rfl

theorem cell23_5966268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5966268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966268 prefixEnd_5966268 := by exact prefixLift 5966268
  have htrace : WordTrace (prefixWord ++ tailWord_5966268) baseStart_5966268 baseEnd_5966268 := by
    simpa [prefixWord, tailWord_5966268, baseEnd_5966268] using wordTrace_append hprefix tailTrace_5966268
  have hstable : (prefixWord ++ tailWord_5966268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966268).length < 2 ^ (prefixWord ++ tailWord_5966268).sum := by decide
  have hdescent : baseEnd_5966268 < baseStart_5966268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966292 : List Nat := [2, 4, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_5966292 : Nat := 118140960795 + 5966292 * 2 ^ 59
def prefixEnd_5966292 : Nat := 4983230072969 + 3 ^ 40 * 5966292 * 2
def baseEnd_5966292 : Nat := 1021191840358292029603843

theorem tailTrace_5966292 : CollatzResearch.WordTrace tailWord_5966292 prefixEnd_5966292 1021191840358292029603843 := by
  unfold tailWord_5966292
  simp only [CollatzResearch.WordTrace]
  refine ⟨108804273250575260197518565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145072364334100346930024753 108804273250575260197518565)
  ·
    refine ⟨20400801234482861287034731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108804273250575260197518565 20400801234482861287034731)
    ·
      refine ⟨30601201851724291930552097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20400801234482861287034731 30601201851724291930552097)
      ·
        refine ⟨22950901388793218947914073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30601201851724291930552097 22950901388793218947914073)
        ·
          refine ⟨17213176041594914210935555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22950901388793218947914073 17213176041594914210935555)
          ·
            refine ⟨25819764062392371316403333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17213176041594914210935555 25819764062392371316403333)
            ·
              refine ⟨4841205761698569621825625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25819764062392371316403333 4841205761698569621825625)
              ·
                refine ⟨3630904321273927216369219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4841205761698569621825625 3630904321273927216369219)
                ·
                  refine ⟨5446356481910890824553829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630904321273927216369219 5446356481910890824553829)
                  ·
                    refine ⟨1021191840358292029603843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446356481910890824553829 1021191840358292029603843)
                    ·
                      rfl

theorem cell23_5966292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_5966292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966292 prefixEnd_5966292 := by exact prefixLift 5966292
  have htrace : WordTrace (prefixWord ++ tailWord_5966292) baseStart_5966292 baseEnd_5966292 := by
    simpa [prefixWord, tailWord_5966292, baseEnd_5966292] using wordTrace_append hprefix tailTrace_5966292
  have hstable : (prefixWord ++ tailWord_5966292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966292).length < 2 ^ (prefixWord ++ tailWord_5966292).sum := by decide
  have hdescent : baseEnd_5966292 < baseStart_5966292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966298 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3]
def baseStart_5966298 : Nat := 118140960795 + 5966298 * 2 ^ 59
def prefixEnd_5966298 : Nat := 4983230072969 + 3 ^ 40 * 5966298 * 2
def baseEnd_5966298 : Nat := 3063578601958803065336501

theorem tailTrace_5966298 : CollatzResearch.WordTrace tailWord_5966298 prefixEnd_5966298 3063578601958803065336501 := by
  unfold tailWord_5966298
  simp only [CollatzResearch.WordTrace]
  refine ⟨54402191334782195854938887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145072510226085855613170365 54402191334782195854938887)
  ·
    refine ⟨81603287002173293782408331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54402191334782195854938887 81603287002173293782408331)
    ·
      refine ⟨122404930503259940673612497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81603287002173293782408331 122404930503259940673612497)
      ·
        refine ⟨91803697877444955505209373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122404930503259940673612497 91803697877444955505209373)
        ·
          refine ⟨34426386704041858314453515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91803697877444955505209373 34426386704041858314453515)
          ·
            refine ⟨51639580056062787471680273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34426386704041858314453515 51639580056062787471680273)
            ·
              refine ⟨38729685042047090603760205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51639580056062787471680273 38729685042047090603760205)
              ·
                refine ⟨14523631890767658976410077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38729685042047090603760205 14523631890767658976410077)
                ·
                  refine ⟨5446361959037872116153779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14523631890767658976410077 5446361959037872116153779)
                  ·
                    refine ⟨8169542938556808174230669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5446361959037872116153779 8169542938556808174230669)
                    ·
                      refine ⟨3063578601958803065336501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8169542938556808174230669 3063578601958803065336501)
                      ·
                        rfl

theorem cell23_5966298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_5966298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966298 prefixEnd_5966298 := by exact prefixLift 5966298
  have htrace : WordTrace (prefixWord ++ tailWord_5966298) baseStart_5966298 baseEnd_5966298 := by
    simpa [prefixWord, tailWord_5966298, baseEnd_5966298] using wordTrace_append hprefix tailTrace_5966298
  have hstable : (prefixWord ++ tailWord_5966298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966298).length < 2 ^ (prefixWord ++ tailWord_5966298).sum := by decide
  have hdescent : baseEnd_5966298 < baseStart_5966298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966301 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_5966301 : Nat := 118140960795 + 5966301 * 2 ^ 59
def prefixEnd_5966301 : Nat := 4983230072969 + 3 ^ 40 * 5966301 * 2
def baseEnd_5966301 : Nat := 1021193380800255517866329

theorem tailTrace_5966301 : CollatzResearch.WordTrace tailWord_5966301 prefixEnd_5966301 1021193380800255517866329 := by
  unfold tailWord_5966301
  simp only [CollatzResearch.WordTrace]
  refine ⟨217608874758117914932114757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145072583172078609954743171 217608874758117914932114757)
  ·
    refine ⟨40801664017147109049771517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217608874758117914932114757 40801664017147109049771517)
    ·
      refine ⟨15300624006430165893664319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40801664017147109049771517 15300624006430165893664319)
      ·
        refine ⟨22950936009645248840496479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15300624006430165893664319 22950936009645248840496479)
        ·
          refine ⟨34426404014467873260744719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22950936009645248840496479 34426404014467873260744719)
          ·
            refine ⟨51639606021701809891117079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34426404014467873260744719 51639606021701809891117079)
            ·
              refine ⟨77459409032552714836675619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51639606021701809891117079 77459409032552714836675619)
              ·
                refine ⟨116189113548829072255013429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77459409032552714836675619 116189113548829072255013429)
                ·
                  refine ⟨10892729395202725523907509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116189113548829072255013429 10892729395202725523907509)
                  ·
                    refine ⟨1021193380800255517866329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10892729395202725523907509 1021193380800255517866329)
                    ·
                      rfl

theorem cell23_5966301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_5966301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966301 prefixEnd_5966301 := by exact prefixLift 5966301
  have htrace : WordTrace (prefixWord ++ tailWord_5966301) baseStart_5966301 baseEnd_5966301 := by
    simpa [prefixWord, tailWord_5966301, baseEnd_5966301] using wordTrace_append hprefix tailTrace_5966301
  have hstable : (prefixWord ++ tailWord_5966301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966301).length < 2 ^ (prefixWord ++ tailWord_5966301).sum := by decide
  have hdescent : baseEnd_5966301 < baseStart_5966301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966321 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_5966321 : Nat := 118140960795 + 5966321 * 2 ^ 59
def prefixEnd_5966321 : Nat := 4983230072969 + 3 ^ 40 * 5966321 * 2
def baseEnd_5966321 : Nat := 3063590412013856475348895

theorem tailTrace_5966321 : CollatzResearch.WordTrace tailWord_5966321 prefixEnd_5966321 3063590412013856475348895 := by
  unfold tailWord_5966321
  simp only [CollatzResearch.WordTrace]
  refine ⟨217609604218045458347842817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145073069478696972231895211 217609604218045458347842817)
  ·
    refine ⟨163207203163534093760882113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217609604218045458347842817 163207203163534093760882113)
    ·
      refine ⟨122405402372650570320661585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163207203163534093760882113 122405402372650570320661585)
      ·
        refine ⟨91804051779487927740496189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122405402372650570320661585 91804051779487927740496189)
        ·
          refine ⟨34426519417307972902686071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91804051779487927740496189 34426519417307972902686071)
          ·
            refine ⟨51639779125961959354029107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34426519417307972902686071 51639779125961959354029107)
            ·
              refine ⟨77459668688942939031043661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51639779125961959354029107 77459668688942939031043661)
              ·
                refine ⟨29047375758353602136641373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77459668688942939031043661 29047375758353602136641373)
                ·
                  refine ⟨10892765909382600801240515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29047375758353602136641373 10892765909382600801240515)
                  ·
                    refine ⟨16339148864073901201860773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10892765909382600801240515 16339148864073901201860773)
                    ·
                      refine ⟨3063590412013856475348895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16339148864073901201860773 3063590412013856475348895)
                      ·
                        rfl

theorem cell23_5966321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_5966321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966321 prefixEnd_5966321 := by exact prefixLift 5966321
  have htrace : WordTrace (prefixWord ++ tailWord_5966321) baseStart_5966321 baseEnd_5966321 := by
    simpa [prefixWord, tailWord_5966321, baseEnd_5966321] using wordTrace_append hprefix tailTrace_5966321
  have hstable : (prefixWord ++ tailWord_5966321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966321).length < 2 ^ (prefixWord ++ tailWord_5966321).sum := by decide
  have hdescent : baseEnd_5966321 < baseStart_5966321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966348 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_5966348 : Nat := 118140960795 + 5966348 * 2 ^ 59
def prefixEnd_5966348 : Nat := 4983230072969 + 3 ^ 40 * 5966348 * 2
def baseEnd_5966348 : Nat := 1021201425330509289903757

theorem tailTrace_5966348 : CollatzResearch.WordTrace tailWord_5966348 prefixEnd_5966348 1021201425330509289903757 := by
  unfold tailWord_5966348
  simp only [CollatzResearch.WordTrace]
  refine ⟨108805294494473820979537849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145073725992631761306050465 108805294494473820979537849)
  ·
    refine ⟨81603970870855365734653387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108805294494473820979537849 81603970870855365734653387)
    ·
      refine ⟨122405956306283048601980081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81603970870855365734653387 122405956306283048601980081)
      ·
        refine ⟨91804467229712286451485061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122405956306283048601980081 91804467229712286451485061)
        ·
          refine ⟨17213337605571053709653449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91804467229712286451485061 17213337605571053709653449)
          ·
            refine ⟨12910003204178290282240087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17213337605571053709653449 12910003204178290282240087)
            ·
              refine ⟨19365004806267435423360131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12910003204178290282240087 19365004806267435423360131)
              ·
                refine ⟨29047507209401153135040197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19365004806267435423360131 29047507209401153135040197)
                ·
                  refine ⟨5446407601762716212820037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29047507209401153135040197 5446407601762716212820037)
                  ·
                    refine ⟨1021201425330509289903757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446407601762716212820037 1021201425330509289903757)
                    ·
                      rfl

theorem cell23_5966348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_5966348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966348 prefixEnd_5966348 := by exact prefixLift 5966348
  have htrace : WordTrace (prefixWord ++ tailWord_5966348) baseStart_5966348 baseEnd_5966348 := by
    simpa [prefixWord, tailWord_5966348, baseEnd_5966348] using wordTrace_append hprefix tailTrace_5966348
  have hstable : (prefixWord ++ tailWord_5966348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966348).length < 2 ^ (prefixWord ++ tailWord_5966348).sum := by decide
  have hdescent : baseEnd_5966348 < baseStart_5966348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966349 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_5966349 : Nat := 118140960795 + 5966349 * 2 ^ 59
def prefixEnd_5966349 : Nat := 4983230072969 + 3 ^ 40 * 5966349 * 2
def baseEnd_5966349 : Nat := 3063604789472182365798767

theorem tailTrace_5966349 : CollatzResearch.WordTrace tailWord_5966349 prefixEnd_5966349 3063604789472182365798767 := by
  unfold tailWord_5966349
  simp only [CollatzResearch.WordTrace]
  refine ⟨217610625461944019129862101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145073750307962679419908067 217610625461944019129862101)
  ·
    refine ⟨5100249034264312948356143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 217610625461944019129862101 5100249034264312948356143)
    ·
      refine ⟨7650373551396469422534215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100249034264312948356143 7650373551396469422534215)
      ·
        refine ⟨11475560327094704133801323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7650373551396469422534215 11475560327094704133801323)
        ·
          refine ⟨17213340490642056200701985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11475560327094704133801323 17213340490642056200701985)
          ·
            refine ⟨12910005367981542150526489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17213340490642056200701985 12910005367981542150526489)
            ·
              refine ⟨9682504025986156612894867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12910005367981542150526489 9682504025986156612894867)
              ·
                refine ⟨14523756038979234919342301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9682504025986156612894867 14523756038979234919342301)
                ·
                  refine ⟨5446408514617213094753363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14523756038979234919342301 5446408514617213094753363)
                  ·
                    refine ⟨8169612771925819642130045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5446408514617213094753363 8169612771925819642130045)
                    ·
                      refine ⟨3063604789472182365798767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8169612771925819642130045 3063604789472182365798767)
                      ·
                        rfl

theorem cell23_5966349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_5966349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966349 prefixEnd_5966349 := by exact prefixLift 5966349
  have htrace : WordTrace (prefixWord ++ tailWord_5966349) baseStart_5966349 baseEnd_5966349 := by
    simpa [prefixWord, tailWord_5966349, baseEnd_5966349] using wordTrace_append hprefix tailTrace_5966349
  have hstable : (prefixWord ++ tailWord_5966349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966349).length < 2 ^ (prefixWord ++ tailWord_5966349).sum := by decide
  have hdescent : baseEnd_5966349 < baseStart_5966349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966355 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 3, 2, 2]
def baseStart_5966355 : Nat := 118140960795 + 5966355 * 2 ^ 59
def prefixEnd_5966355 : Nat := 4983230072969 + 3 ^ 40 * 5966355 * 2
def baseEnd_5966355 : Nat := 3063607870356109342323739

theorem tailTrace_5966355 : CollatzResearch.WordTrace tailWord_5966355 prefixEnd_5966355 3063607870356109342323739 := by
  unfold tailWord_5966355
  simp only [CollatzResearch.WordTrace]
  refine ⟨217610844299922282154580519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145073896199948188103053679 217610844299922282154580519)
  ·
    refine ⟨326416266449883423231870779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217610844299922282154580519 326416266449883423231870779)
    ·
      refine ⟨489624399674825134847806169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326416266449883423231870779 489624399674825134847806169)
      ·
        refine ⟨367218299756118851135854627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489624399674825134847806169 367218299756118851135854627)
        ·
          refine ⟨550827449634178276703781941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367218299756118851135854627 550827449634178276703781941)
          ·
            refine ⟨51640073403204213440979557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 550827449634178276703781941 51640073403204213440979557)
            ·
              refine ⟨9682513763100790020183667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51640073403204213440979557 9682513763100790020183667)
              ·
                refine ⟨14523770644651185030275501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9682513763100790020183667 14523770644651185030275501)
                ·
                  refine ⟨5446413991744194386353313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14523770644651185030275501 5446413991744194386353313)
                  ·
                    refine ⟨4084810493808145789764985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5446413991744194386353313 4084810493808145789764985)
                    ·
                      refine ⟨3063607870356109342323739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084810493808145789764985 3063607870356109342323739)
                      ·
                        rfl

theorem cell23_5966355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 3, 2, 2].length) (baseStart_5966355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966355 prefixEnd_5966355 := by exact prefixLift 5966355
  have htrace : WordTrace (prefixWord ++ tailWord_5966355) baseStart_5966355 baseEnd_5966355 := by
    simpa [prefixWord, tailWord_5966355, baseEnd_5966355] using wordTrace_append hprefix tailTrace_5966355
  have hstable : (prefixWord ++ tailWord_5966355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966355).length < 2 ^ (prefixWord ++ tailWord_5966355).sum := by decide
  have hdescent : baseEnd_5966355 < baseStart_5966355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966368 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5966368 : Nat := 118140960795 + 5966368 * 2 ^ 59
def prefixEnd_5966368 : Nat := 4983230072969 + 3 ^ 40 * 5966368 * 2
def baseEnd_5966368 : Nat := 3063614545604617791461179

theorem tailTrace_5966368 : CollatzResearch.WordTrace tailWord_5966368 prefixEnd_5966368 3063614545604617791461179 := by
  unfold tailWord_5966368
  simp only [CollatzResearch.WordTrace]
  refine ⟨108805659224437592687401879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145074212299250123583202505 108805659224437592687401879)
  ·
    refine ⟨163208488836656389031102819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108805659224437592687401879 163208488836656389031102819)
    ·
      refine ⟨244812733254984583546654229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163208488836656389031102819 244812733254984583546654229)
      ·
        refine ⟨11475596871327402353749417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 244812733254984583546654229 11475596871327402353749417)
        ·
          refine ⟨8606697653495551765312063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11475596871327402353749417 8606697653495551765312063)
          ·
            refine ⟨12910046480243327647968095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8606697653495551765312063 12910046480243327647968095)
            ·
              refine ⟨19365069720364991471952143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12910046480243327647968095 19365069720364991471952143)
              ·
                refine ⟨29047604580547487207928215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19365069720364991471952143 29047604580547487207928215)
                ·
                  refine ⟨43571406870821230811892323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29047604580547487207928215 43571406870821230811892323)
                  ·
                    refine ⟨65357110306231846217838485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43571406870821230811892323 65357110306231846217838485)
                    ·
                      refine ⟨3063614545604617791461179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65357110306231846217838485 3063614545604617791461179)
                      ·
                        rfl

theorem cell23_5966368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5966368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966368 prefixEnd_5966368 := by exact prefixLift 5966368
  have htrace : WordTrace (prefixWord ++ tailWord_5966368) baseStart_5966368 baseEnd_5966368 := by
    simpa [prefixWord, tailWord_5966368, baseEnd_5966368] using wordTrace_append hprefix tailTrace_5966368
  have hstable : (prefixWord ++ tailWord_5966368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966368).length < 2 ^ (prefixWord ++ tailWord_5966368).sum := by decide
  have hdescent : baseEnd_5966368 < baseStart_5966368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966372 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5966372 : Nat := 118140960795 + 5966372 * 2 ^ 59
def prefixEnd_5966372 : Nat := 4983230072969 + 3 ^ 40 * 5966372 * 2
def baseEnd_5966372 : Nat := 3063616599527235775811161

theorem tailTrace_5966372 : CollatzResearch.WordTrace tailWord_5966372 prefixEnd_5966372 3063616599527235775811161 := by
  unfold tailWord_5966372
  simp only [CollatzResearch.WordTrace]
  refine ⟨108805732170430347028974685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145074309560573796038632913 108805732170430347028974685)
  ·
    refine ⟨40802149563911380135865507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108805732170430347028974685 40802149563911380135865507)
    ·
      refine ⟨61203224345867070203798261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40802149563911380135865507 61203224345867070203798261)
      ·
        refine ⟨5737802282425037831606087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61203224345867070203798261 5737802282425037831606087)
        ·
          refine ⟨8606703423637556747409131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5737802282425037831606087 8606703423637556747409131)
          ·
            refine ⟨12910055135456335121113697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8606703423637556747409131 12910055135456335121113697)
            ·
              refine ⟨9682541351592251340835273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12910055135456335121113697 9682541351592251340835273)
              ·
                refine ⟨7261906013694188505626455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9682541351592251340835273 7261906013694188505626455)
                ·
                  refine ⟨10892859020541282758439683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7261906013694188505626455 10892859020541282758439683)
                  ·
                    refine ⟨16339288530811924137659525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10892859020541282758439683 16339288530811924137659525)
                    ·
                      refine ⟨3063616599527235775811161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16339288530811924137659525 3063616599527235775811161)
                      ·
                        rfl

theorem cell23_5966372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5966372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966372 prefixEnd_5966372 := by exact prefixLift 5966372
  have htrace : WordTrace (prefixWord ++ tailWord_5966372) baseStart_5966372 baseEnd_5966372 := by
    simpa [prefixWord, tailWord_5966372, baseEnd_5966372] using wordTrace_append hprefix tailTrace_5966372
  have hstable : (prefixWord ++ tailWord_5966372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966372).length < 2 ^ (prefixWord ++ tailWord_5966372).sum := by decide
  have hdescent : baseEnd_5966372 < baseStart_5966372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966378 : List Nat := [3, 1, 4, 1, 1, 2, 4, 7]
def baseStart_5966378 : Nat := 118140960795 + 5966378 * 2 ^ 59
def prefixEnd_5966378 : Nat := 4983230072969 + 3 ^ 40 * 5966378 * 2
def baseEnd_5966378 : Nat := 113467395570783805642079

theorem tailTrace_5966378 : CollatzResearch.WordTrace tailWord_5966378 prefixEnd_5966378 113467395570783805642079 := by
  unfold tailWord_5966378
  simp only [CollatzResearch.WordTrace]
  refine ⟨54402920794709739270666947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145074455452559304721778525 54402920794709739270666947)
  ·
    refine ⟨81604381192064608906000421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54402920794709739270666947 81604381192064608906000421)
    ·
      refine ⟨15300821473512114169875079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81604381192064608906000421 15300821473512114169875079)
      ·
        refine ⟨22951232210268171254812619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15300821473512114169875079 22951232210268171254812619)
        ·
          refine ⟨34426848315402256882218929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22951232210268171254812619 34426848315402256882218929)
          ·
            refine ⟨25820136236551692661664197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34426848315402256882218929 25820136236551692661664197)
            ·
              refine ⟨4841275544353442374062037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25820136236551692661664197 4841275544353442374062037)
              ·
                refine ⟨113467395570783805642079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4841275544353442374062037 113467395570783805642079)
                ·
                  rfl

theorem cell23_5966378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 7].length) (baseStart_5966378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966378 prefixEnd_5966378 := by exact prefixLift 5966378
  have htrace : WordTrace (prefixWord ++ tailWord_5966378) baseStart_5966378 baseEnd_5966378 := by
    simpa [prefixWord, tailWord_5966378, baseEnd_5966378] using wordTrace_append hprefix tailTrace_5966378
  have hstable : (prefixWord ++ tailWord_5966378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966378).length < 2 ^ (prefixWord ++ tailWord_5966378).sum := by decide
  have hdescent : baseEnd_5966378 < baseStart_5966378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966406 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_5966406 : Nat := 118140960795 + 5966406 * 2 ^ 59
def prefixEnd_5966406 : Nat := 4983230072969 + 3 ^ 40 * 5966406 * 2
def baseEnd_5966406 : Nat := 3063634057869488642786005

theorem tailTrace_5966406 : CollatzResearch.WordTrace tailWord_5966406 prefixEnd_5966406 3063634057869488642786005 := by
  unfold tailWord_5966406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800397013210547433271471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145075136281825011909791381 6800397013210547433271471)
  ·
    refine ⟨10200595519815821149907207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6800397013210547433271471 10200595519815821149907207)
    ·
      refine ⟨15300893279723731724860811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10200595519815821149907207 15300893279723731724860811)
      ·
        refine ⟨22951339919585597587291217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15300893279723731724860811 22951339919585597587291217)
        ·
          refine ⟨17213504939689198190468413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22951339919585597587291217 17213504939689198190468413)
          ·
            refine ⟨6455064352383449321425655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17213504939689198190468413 6455064352383449321425655)
            ·
              refine ⟨9682596528575173982138483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455064352383449321425655 9682596528575173982138483)
              ·
                refine ⟨14523894792862760973207725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9682596528575173982138483 14523894792862760973207725)
                ·
                  refine ⟨5446460547323535364952897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14523894792862760973207725 5446460547323535364952897)
                  ·
                    refine ⟨4084845410492651523714673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5446460547323535364952897 4084845410492651523714673)
                    ·
                      refine ⟨3063634057869488642786005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084845410492651523714673 3063634057869488642786005)
                      ·
                        rfl

theorem cell23_5966406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_5966406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966406 prefixEnd_5966406 := by exact prefixLift 5966406
  have htrace : WordTrace (prefixWord ++ tailWord_5966406) baseStart_5966406 baseEnd_5966406 := by
    simpa [prefixWord, tailWord_5966406, baseEnd_5966406] using wordTrace_append hprefix tailTrace_5966406
  have hstable : (prefixWord ++ tailWord_5966406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966406).length < 2 ^ (prefixWord ++ tailWord_5966406).sum := by decide
  have hdescent : baseEnd_5966406 < baseStart_5966406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966421 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_5966421 : Nat := 118140960795 + 5966421 * 2 ^ 59
def prefixEnd_5966421 : Nat := 4983230072969 + 3 ^ 40 * 5966421 * 2
def baseEnd_5966421 : Nat := 1021213920026435361366145

theorem tailTrace_5966421 : CollatzResearch.WordTrace tailWord_5966421 prefixEnd_5966421 1021213920026435361366145 := by
  unfold tailWord_5966421
  simp only [CollatzResearch.WordTrace]
  refine ⟨217613251517683175426483117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145075501011788783617655411 217613251517683175426483117)
  ·
    refine ⟨81604969319131190784931169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217613251517683175426483117 81604969319131190784931169)
    ·
      refine ⟨61203726989348393088698377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81604969319131190784931169 61203726989348393088698377)
      ·
        refine ⟨45902795242011294816523783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61203726989348393088698377 45902795242011294816523783)
        ·
          refine ⟨68854192863016942224785675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45902795242011294816523783 68854192863016942224785675)
          ·
            refine ⟨103281289294525413337178513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68854192863016942224785675 103281289294525413337178513)
            ·
              refine ⟨77460966970894060002883885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103281289294525413337178513 77460966970894060002883885)
              ·
                refine ⟨29047862614085272501081457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77460966970894060002883885 29047862614085272501081457)
                ·
                  refine ⟨21785896960563954375811093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29047862614085272501081457 21785896960563954375811093)
                  ·
                    refine ⟨1021213920026435361366145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21785896960563954375811093 1021213920026435361366145)
                    ·
                      rfl

theorem cell23_5966421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_5966421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966421 prefixEnd_5966421 := by exact prefixLift 5966421
  have htrace : WordTrace (prefixWord ++ tailWord_5966421) baseStart_5966421 baseEnd_5966421 := by
    simpa [prefixWord, tailWord_5966421, baseEnd_5966421] using wordTrace_append hprefix tailTrace_5966421
  have hstable : (prefixWord ++ tailWord_5966421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966421).length < 2 ^ (prefixWord ++ tailWord_5966421).sum := by decide
  have hdescent : baseEnd_5966421 < baseStart_5966421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966441 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 4]
def baseStart_5966441 : Nat := 118140960795 + 5966441 * 2 ^ 59
def prefixEnd_5966441 : Nat := 4983230072969 + 3 ^ 40 * 5966441 * 2
def baseEnd_5966441 : Nat := 3063652029692396005848343

theorem tailTrace_5966441 : CollatzResearch.WordTrace tailWord_5966441 prefixEnd_5966441 3063652029692396005848343 := by
  unfold tailWord_5966441
  simp only [CollatzResearch.WordTrace]
  refine ⟨217613980977610718842211177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145075987318407145894807451 217613980977610718842211177)
  ·
    refine ⟨163210485733208039131658383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217613980977610718842211177 163210485733208039131658383)
    ·
      refine ⟨244815728599812058697487575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163210485733208039131658383 244815728599812058697487575)
      ·
        refine ⟨367223592899718088046231363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244815728599812058697487575 367223592899718088046231363)
        ·
          refine ⟨550835389349577132069347045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367223592899718088046231363 550835389349577132069347045)
          ·
            refine ⟨103281635503045712263002571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 550835389349577132069347045 103281635503045712263002571)
            ·
              refine ⟨154922453254568568394503857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103281635503045712263002571 154922453254568568394503857)
              ·
                refine ⟨116191839940926426295877893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154922453254568568394503857 116191839940926426295877893)
                ·
                  refine ⟨21785969988923704930477105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116191839940926426295877893 21785969988923704930477105)
                  ·
                    refine ⟨16339477491692778697857829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21785969988923704930477105 16339477491692778697857829)
                    ·
                      refine ⟨3063652029692396005848343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16339477491692778697857829 3063652029692396005848343)
                      ·
                        rfl

theorem cell23_5966441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_5966441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966441 prefixEnd_5966441 := by exact prefixLift 5966441
  have htrace : WordTrace (prefixWord ++ tailWord_5966441) baseStart_5966441 baseEnd_5966441 := by
    simpa [prefixWord, tailWord_5966441, baseEnd_5966441] using wordTrace_append hprefix tailTrace_5966441
  have hstable : (prefixWord ++ tailWord_5966441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966441).length < 2 ^ (prefixWord ++ tailWord_5966441).sum := by decide
  have hdescent : baseEnd_5966441 < baseStart_5966441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966445 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_5966445 : Nat := 118140960795 + 5966445 * 2 ^ 59
def prefixEnd_5966445 : Nat := 4983230072969 + 3 ^ 40 * 5966445 * 2
def baseEnd_5966445 : Nat := 3063654083615013990198325

theorem tailTrace_5966445 : CollatzResearch.WordTrace tailWord_5966445 prefixEnd_5966445 3063654083615013990198325 := by
  unfold tailWord_5966445
  simp only [CollatzResearch.WordTrace]
  refine ⟨217614126869596227525356789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145076084579730818350237859 217614126869596227525356789)
  ·
    refine ⟨20401324394024646330502199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217614126869596227525356789 20401324394024646330502199)
    ·
      refine ⟨30601986591036969495753299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20401324394024646330502199 30601986591036969495753299)
      ·
        refine ⟨45902979886555454243629949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30601986591036969495753299 45902979886555454243629949)
        ·
          refine ⟨17213617457458295341361231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45902979886555454243629949 17213617457458295341361231)
          ·
            refine ⟨25820426186187443012041847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17213617457458295341361231 25820426186187443012041847)
            ·
              refine ⟨38730639279281164518062771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25820426186187443012041847 38730639279281164518062771)
              ·
                refine ⟨58095958918921746777094157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38730639279281164518062771 58095958918921746777094157)
                ·
                  refine ⟨21785984594595655041410309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58095958918921746777094157 21785984594595655041410309)
                  ·
                    refine ⟨4084872111486685320264433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21785984594595655041410309 4084872111486685320264433)
                    ·
                      refine ⟨3063654083615013990198325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084872111486685320264433 3063654083615013990198325)
                      ·
                        rfl

theorem cell23_5966445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_5966445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966445 prefixEnd_5966445 := by exact prefixLift 5966445
  have htrace : WordTrace (prefixWord ++ tailWord_5966445) baseStart_5966445 baseEnd_5966445 := by
    simpa [prefixWord, tailWord_5966445, baseEnd_5966445] using wordTrace_append hprefix tailTrace_5966445
  have hstable : (prefixWord ++ tailWord_5966445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966445).length < 2 ^ (prefixWord ++ tailWord_5966445).sum := by decide
  have hdescent : baseEnd_5966445 < baseStart_5966445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966513 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 2, 2, 2]
def baseStart_5966513 : Nat := 118140960795 + 5966513 * 2 ^ 59
def prefixEnd_5966513 : Nat := 4983230072969 + 3 ^ 40 * 5966513 * 2
def baseEnd_5966513 : Nat := 3063689000299519724148013

theorem tailTrace_5966513 : CollatzResearch.WordTrace tailWord_5966513 prefixEnd_5966513 3063689000299519724148013 := by
  unfold tailWord_5966513
  simp only [CollatzResearch.WordTrace]
  refine ⟨217616607033349875138832193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145077738022233250092554795 217616607033349875138832193)
  ·
    refine ⟨163212455275012406354124145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217616607033349875138832193 163212455275012406354124145)
    ·
      refine ⟨122409341456259304765593109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163212455275012406354124145 122409341456259304765593109)
      ·
        refine ⟨5737937880762154910887177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122409341456259304765593109 5737937880762154910887177)
        ·
          refine ⟨4303453410571616183165383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5737937880762154910887177 4303453410571616183165383)
          ·
            refine ⟨6455180115857424274748075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303453410571616183165383 6455180115857424274748075)
            ·
              refine ⟨9682770173786136412122113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455180115857424274748075 9682770173786136412122113)
              ·
                refine ⟨7262077630339602309091585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9682770173786136412122113 7262077630339602309091585)
                ·
                  refine ⟨5446558222754701731818689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7262077630339602309091585 5446558222754701731818689)
                  ·
                    refine ⟨4084918667066026298864017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5446558222754701731818689 4084918667066026298864017)
                    ·
                      refine ⟨3063689000299519724148013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084918667066026298864017 3063689000299519724148013)
                      ·
                        rfl

theorem cell23_5966513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_5966513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966513 prefixEnd_5966513 := by exact prefixLift 5966513
  have htrace : WordTrace (prefixWord ++ tailWord_5966513) baseStart_5966513 baseEnd_5966513 := by
    simpa [prefixWord, tailWord_5966513, baseEnd_5966513] using wordTrace_append hprefix tailTrace_5966513
  have hstable : (prefixWord ++ tailWord_5966513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966513).length < 2 ^ (prefixWord ++ tailWord_5966513).sum := by decide
  have hdescent : baseEnd_5966513 < baseStart_5966513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966595 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 6, 3, 2]
def baseStart_5966595 : Nat := 118140960795 + 5966595 * 2 ^ 59
def prefixEnd_5966595 : Nat := 4983230072969 + 3 ^ 40 * 5966595 * 2
def baseEnd_5966595 : Nat := 3063731105713188403322635

theorem tailTrace_5966595 : CollatzResearch.WordTrace tailWord_5966595 prefixEnd_5966595 3063731105713188403322635 := by
  unfold tailWord_5966595
  simp only [CollatzResearch.WordTrace]
  refine ⟨217619597819052803143317239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145079731879368535428878159 217619597819052803143317239)
  ·
    refine ⟨326429396728579204714975859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217619597819052803143317239 326429396728579204714975859)
    ·
      refine ⟨489644095092868807072463789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326429396728579204714975859 489644095092868807072463789)
      ·
        refine ⟨183616535659825802652173921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489644095092868807072463789 183616535659825802652173921)
        ·
          refine ⟨137712401744869351989130441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183616535659825802652173921 137712401744869351989130441)
          ·
            refine ⟨103284301308652013991847831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137712401744869351989130441 103284301308652013991847831)
            ·
              refine ⟨154926451962978020987771747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103284301308652013991847831 154926451962978020987771747)
              ·
                refine ⟨232389677944467031481657621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154926451962978020987771747 232389677944467031481657621)
                ·
                  refine ⟨10893266153646892100702701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 232389677944467031481657621 10893266153646892100702701)
                  ·
                    refine ⟨4084974807617584537763513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10893266153646892100702701 4084974807617584537763513)
                    ·
                      refine ⟨3063731105713188403322635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4084974807617584537763513 3063731105713188403322635)
                      ·
                        rfl

theorem cell23_5966595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_5966595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966595 prefixEnd_5966595 := by exact prefixLift 5966595
  have htrace : WordTrace (prefixWord ++ tailWord_5966595) baseStart_5966595 baseEnd_5966595 := by
    simpa [prefixWord, tailWord_5966595, baseEnd_5966595] using wordTrace_append hprefix tailTrace_5966595
  have hstable : (prefixWord ++ tailWord_5966595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966595).length < 2 ^ (prefixWord ++ tailWord_5966595).sum := by decide
  have hdescent : baseEnd_5966595 < baseStart_5966595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966635 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 2, 4]
def baseStart_5966635 : Nat := 118140960795 + 5966635 * 2 ^ 59
def prefixEnd_5966635 : Nat := 4983230072969 + 3 ^ 40 * 5966635 * 2
def baseEnd_5966635 : Nat := 1021250548313122748940817

theorem tailTrace_5966635 : CollatzResearch.WordTrace tailWord_5966635 prefixEnd_5966635 1021250548313122748940817 := by
  unfold tailWord_5966635
  simp only [CollatzResearch.WordTrace]
  refine ⟨217621056738907889974773359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145080704492605259983182239 217621056738907889974773359)
  ·
    refine ⟨326431585108361834962160039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217621056738907889974773359 326431585108361834962160039)
    ·
      refine ⟨489647377662542752443240059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326431585108361834962160039 489647377662542752443240059)
      ·
        refine ⟨734471066493814128664860089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489647377662542752443240059 734471066493814128664860089)
        ·
          refine ⟨550853299870360596498645067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 734471066493814128664860089 550853299870360596498645067)
          ·
            refine ⟨826279949805540894747967601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550853299870360596498645067 826279949805540894747967601)
            ·
              refine ⟨619709962354155671060975701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826279949805540894747967601 619709962354155671060975701)
              ·
                refine ⟨7262226121337761770245809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 619709962354155671060975701 7262226121337761770245809)
                ·
                  refine ⟨5446669591003321327684357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7262226121337761770245809 5446669591003321327684357)
                  ·
                    refine ⟨1021250548313122748940817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446669591003321327684357 1021250548313122748940817)
                    ·
                      rfl

theorem cell23_5966635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 4].length) (baseStart_5966635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966635 prefixEnd_5966635 := by exact prefixLift 5966635
  have htrace : WordTrace (prefixWord ++ tailWord_5966635) baseStart_5966635 baseEnd_5966635 := by
    simpa [prefixWord, tailWord_5966635, baseEnd_5966635] using wordTrace_append hprefix tailTrace_5966635
  have hstable : (prefixWord ++ tailWord_5966635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966635).length < 2 ^ (prefixWord ++ tailWord_5966635).sum := by decide
  have hdescent : baseEnd_5966635 < baseStart_5966635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966655 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_5966655 : Nat := 118140960795 + 5966655 * 2 ^ 59
def prefixEnd_5966655 : Nat := 4983230072969 + 3 ^ 40 * 5966655 * 2
def baseEnd_5966655 : Nat := 3063761914552458168572359

theorem tailTrace_5966655 : CollatzResearch.WordTrace tailWord_5966655 prefixEnd_5966655 3063761914552458168572359 := by
  unfold tailWord_5966655
  simp only [CollatzResearch.WordTrace]
  refine ⟨217621786198835433390501419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145081190799223622260334279 217621786198835433390501419)
  ·
    refine ⟨326432679298253150085752129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217621786198835433390501419 326432679298253150085752129)
    ·
      refine ⟨244824509473689862564314097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326432679298253150085752129 244824509473689862564314097)
      ·
        refine ⟨183618382105267396923235573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244824509473689862564314097 183618382105267396923235573)
        ·
          refine ⟨17214223322368818461553335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183618382105267396923235573 17214223322368818461553335)
          ·
            refine ⟨25821334983553227692330003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17214223322368818461553335 25821334983553227692330003)
            ·
              refine ⟨38732002475329841538495005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25821334983553227692330003 38732002475329841538495005)
              ·
                refine ⟨14524500928248690576935627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38732002475329841538495005 14524500928248690576935627)
                ·
                  refine ⟨21786751392373035865403441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14524500928248690576935627 21786751392373035865403441)
                  ·
                    refine ⟨16340063544279776899052581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21786751392373035865403441 16340063544279776899052581)
                    ·
                      refine ⟨3063761914552458168572359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16340063544279776899052581 3063761914552458168572359)
                      ·
                        rfl

theorem cell23_5966655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_5966655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966655 prefixEnd_5966655 := by exact prefixLift 5966655
  have htrace : WordTrace (prefixWord ++ tailWord_5966655) baseStart_5966655 baseEnd_5966655 := by
    simpa [prefixWord, tailWord_5966655, baseEnd_5966655] using wordTrace_append hprefix tailTrace_5966655
  have hstable : (prefixWord ++ tailWord_5966655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966655).length < 2 ^ (prefixWord ++ tailWord_5966655).sum := by decide
  have hdescent : baseEnd_5966655 < baseStart_5966655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966665 : List Nat := [1, 2, 1, 1, 2, 6, 3, 7]
def baseStart_5966665 : Nat := 118140960795 + 5966665 * 2 ^ 59
def prefixEnd_5966665 : Nat := 4983230072969 + 3 ^ 40 * 5966665 * 2
def baseEnd_5966665 : Nat := 113472853679963078868419

theorem tailTrace_5966665 : CollatzResearch.WordTrace tailWord_5966665 prefixEnd_5966665 113472853679963078868419 := by
  unfold tailWord_5966665
  simp only [CollatzResearch.WordTrace]
  refine ⟨217622150928799205098365449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145081433952532803398910299 217622150928799205098365449)
  ·
    refine ⟨163216613196599403823774087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217622150928799205098365449 163216613196599403823774087)
    ·
      refine ⟨244824919794899105735661131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163216613196599403823774087 244824919794899105735661131)
      ·
        refine ⟨367237379692348658603491697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244824919794899105735661131 367237379692348658603491697)
        ·
          refine ⟨275428034769261493952618773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367237379692348658603491697 275428034769261493952618773)
          ·
            refine ⟨12910689129809132529029005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 275428034769261493952618773 12910689129809132529029005)
            ·
              refine ⟨4841508423678424698385877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12910689129809132529029005 4841508423678424698385877)
              ·
                refine ⟨113472853679963078868419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4841508423678424698385877 113472853679963078868419)
                ·
                  rfl

theorem cell23_5966665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 7].length) (baseStart_5966665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966665 prefixEnd_5966665 := by exact prefixLift 5966665
  have htrace : WordTrace (prefixWord ++ tailWord_5966665) baseStart_5966665 baseEnd_5966665 := by
    simpa [prefixWord, tailWord_5966665, baseEnd_5966665] using wordTrace_append hprefix tailTrace_5966665
  have hstable : (prefixWord ++ tailWord_5966665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966665).length < 2 ^ (prefixWord ++ tailWord_5966665).sum := by decide
  have hdescent : baseEnd_5966665 < baseStart_5966665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966676 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_5966676 : Nat := 118140960795 + 5966676 * 2 ^ 59
def prefixEnd_5966676 : Nat := 4983230072969 + 3 ^ 40 * 5966676 * 2
def baseEnd_5966676 : Nat := 3063772697646202586409763

theorem tailTrace_5966676 : CollatzResearch.WordTrace tailWord_5966676 prefixEnd_5966676 3063772697646202586409763 := by
  unfold tailWord_5966676
  simp only [CollatzResearch.WordTrace]
  refine ⟨108811276065879676988507941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145081701421172902651343921 108811276065879676988507941)
  ·
    refine ⟨20402114262352439435345239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108811276065879676988507941 20402114262352439435345239)
    ·
      refine ⟨30603171393528659153017859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20402114262352439435345239 30603171393528659153017859)
      ·
        refine ⟨45904757090292988729526789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30603171393528659153017859 45904757090292988729526789)
        ·
          refine ⟨8607141954429935386786273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45904757090292988729526789 8607141954429935386786273)
          ·
            refine ⟨6455356465822451540089705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8607141954429935386786273 6455356465822451540089705)
            ·
              refine ⟨4841517349366838655067279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6455356465822451540089705 4841517349366838655067279)
              ·
                refine ⟨7262276024050257982600919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841517349366838655067279 7262276024050257982600919)
                ·
                  refine ⟨10893414036075386973901379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7262276024050257982600919 10893414036075386973901379)
                  ·
                    refine ⟨16340121054113080460852069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10893414036075386973901379 16340121054113080460852069)
                    ·
                      refine ⟨3063772697646202586409763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16340121054113080460852069 3063772697646202586409763)
                      ·
                        rfl

theorem cell23_5966676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_5966676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966676 prefixEnd_5966676 := by exact prefixLift 5966676
  have htrace : WordTrace (prefixWord ++ tailWord_5966676) baseStart_5966676 baseEnd_5966676 := by
    simpa [prefixWord, tailWord_5966676, baseEnd_5966676] using wordTrace_append hprefix tailTrace_5966676
  have hstable : (prefixWord ++ tailWord_5966676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966676).length < 2 ^ (prefixWord ++ tailWord_5966676).sum := by decide
  have hdescent : baseEnd_5966676 < baseStart_5966676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966679 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 1, 2, 3]
def baseStart_5966679 : Nat := 118140960795 + 5966679 * 2 ^ 59
def prefixEnd_5966679 : Nat := 4983230072969 + 3 ^ 40 * 5966679 * 2
def baseEnd_5966679 : Nat := 3063774238088166074672249

theorem tailTrace_5966679 : CollatzResearch.WordTrace tailWord_5966679 prefixEnd_5966679 3063774238088166074672249 := by
  unfold tailWord_5966679
  simp only [CollatzResearch.WordTrace]
  refine ⟨217622661550748485489375091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145081774367165656992916727 217622661550748485489375091)
  ·
    refine ⟨326433992326122728234062637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217622661550748485489375091 326433992326122728234062637)
    ·
      refine ⟨122412747122296023087773489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326433992326122728234062637 122412747122296023087773489)
      ·
        refine ⟨91809560341722017315830117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122412747122296023087773489 91809560341722017315830117)
        ·
          refine ⟨17214292564072878246718147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91809560341722017315830117 17214292564072878246718147)
          ·
            refine ⟨25821438846109317370077221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17214292564072878246718147 25821438846109317370077221)
            ·
              refine ⟨4841519783645497006889479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25821438846109317370077221 4841519783645497006889479)
              ·
                refine ⟨7262279675468245510334219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841519783645497006889479 7262279675468245510334219)
                ·
                  refine ⟨10893419513202368265501329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7262279675468245510334219 10893419513202368265501329)
                  ·
                    refine ⟨8170064634901776199125997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10893419513202368265501329 8170064634901776199125997)
                    ·
                      refine ⟨3063774238088166074672249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8170064634901776199125997 3063774238088166074672249)
                      ·
                        rfl

theorem cell23_5966679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_5966679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966679 prefixEnd_5966679 := by exact prefixLift 5966679
  have htrace : WordTrace (prefixWord ++ tailWord_5966679) baseStart_5966679 baseEnd_5966679 := by
    simpa [prefixWord, tailWord_5966679, baseEnd_5966679] using wordTrace_append hprefix tailTrace_5966679
  have hstable : (prefixWord ++ tailWord_5966679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966679).length < 2 ^ (prefixWord ++ tailWord_5966679).sum := by decide
  have hdescent : baseEnd_5966679 < baseStart_5966679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966709 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_5966709 : Nat := 118140960795 + 5966709 * 2 ^ 59
def prefixEnd_5966709 : Nat := 4983230072969 + 3 ^ 40 * 5966709 * 2
def baseEnd_5966709 : Nat := 3063789642507800957297111

theorem tailTrace_5966709 : CollatzResearch.WordTrace tailWord_5966709 prefixEnd_5966709 3063789642507800957297111 := by
  unfold tailWord_5966709
  simp only [CollatzResearch.WordTrace]
  refine ⟨217623755740639800612967181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145082503827093200408644787 217623755740639800612967181)
  ·
    refine ⟨81608908402739925229862693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217623755740639800612967181 81608908402739925229862693)
    ·
      refine ⟨15301670325513735980599255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81608908402739925229862693 15301670325513735980599255)
      ·
        refine ⟨22952505488270603970898883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15301670325513735980599255 22952505488270603970898883)
        ·
          refine ⟨34428758232405905956348325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22952505488270603970898883 34428758232405905956348325)
          ·
            refine ⟨6455392168576107366815311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34428758232405905956348325 6455392168576107366815311)
            ·
              refine ⟨9683088252864161050222967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455392168576107366815311 9683088252864161050222967)
              ·
                refine ⟨14524632379296241575334451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9683088252864161050222967 14524632379296241575334451)
                ·
                  refine ⟨21786948568944362363001677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14524632379296241575334451 21786948568944362363001677)
                  ·
                    refine ⟨8170105713354135886125629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21786948568944362363001677 8170105713354135886125629)
                    ·
                      refine ⟨3063789642507800957297111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8170105713354135886125629 3063789642507800957297111)
                      ·
                        rfl

theorem cell23_5966709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_5966709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966709 prefixEnd_5966709 := by exact prefixLift 5966709
  have htrace : WordTrace (prefixWord ++ tailWord_5966709) baseStart_5966709 baseEnd_5966709 := by
    simpa [prefixWord, tailWord_5966709, baseEnd_5966709] using wordTrace_append hprefix tailTrace_5966709
  have hstable : (prefixWord ++ tailWord_5966709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966709).length < 2 ^ (prefixWord ++ tailWord_5966709).sum := by decide
  have hdescent : baseEnd_5966709 < baseStart_5966709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966732 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 1, 4, 2]
def baseStart_5966732 : Nat := 118140960795 + 5966732 * 2 ^ 59
def prefixEnd_5966732 : Nat := 4983230072969 + 3 ^ 40 * 5966732 * 2
def baseEnd_5966732 : Nat := 3063801452562854367309505

theorem tailTrace_5966732 : CollatzResearch.WordTrace tailWord_5966732 prefixEnd_5966732 3063801452562854367309505 := by
  unfold tailWord_5966732
  simp only [CollatzResearch.WordTrace]
  refine ⟨108812297309778237770527225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145083063079704317027369633 108812297309778237770527225)
  ·
    refine ⟨81609222982333678327895419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108812297309778237770527225 81609222982333678327895419)
    ·
      refine ⟨122413834473500517491843129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81609222982333678327895419 122413834473500517491843129)
      ·
        refine ⟨91810375855125388118882347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122413834473500517491843129 91810375855125388118882347)
        ·
          refine ⟨137715563782688082178323521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91810375855125388118882347 137715563782688082178323521)
          ·
            refine ⟨103286672837016061633742641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137715563782688082178323521 103286672837016061633742641)
            ·
              refine ⟨77465004627762046225306981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103286672837016061633742641 77465004627762046225306981)
              ·
                refine ⟨14524688367705383667245059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77465004627762046225306981 14524688367705383667245059)
                ·
                  refine ⟨21787032551558075500867589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14524688367705383667245059 21787032551558075500867589)
                  ·
                    refine ⟨4085068603417139156412673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21787032551558075500867589 4085068603417139156412673)
                    ·
                      refine ⟨3063801452562854367309505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085068603417139156412673 3063801452562854367309505)
                      ·
                        rfl

theorem cell23_5966732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_5966732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966732 prefixEnd_5966732 := by exact prefixLift 5966732
  have htrace : WordTrace (prefixWord ++ tailWord_5966732) baseStart_5966732 baseEnd_5966732 := by
    simpa [prefixWord, tailWord_5966732, baseEnd_5966732] using wordTrace_append hprefix tailTrace_5966732
  have hstable : (prefixWord ++ tailWord_5966732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966732).length < 2 ^ (prefixWord ++ tailWord_5966732).sum := by decide
  have hdescent : baseEnd_5966732 < baseStart_5966732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966749 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_5966749 : Nat := 118140960795 + 5966749 * 2 ^ 59
def prefixEnd_5966749 : Nat := 4983230072969 + 3 ^ 40 * 5966749 * 2
def baseEnd_5966749 : Nat := 3063810181733980800796927

theorem tailTrace_5966749 : CollatzResearch.WordTrace tailWord_5966749 prefixEnd_5966749 3063810181733980800796927 := by
  unfold tailWord_5966749
  simp only [CollatzResearch.WordTrace]
  refine ⟨217625214660494887444423301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145083476440329924962948867 217625214660494887444423301)
  ·
    refine ⟨40804727748842791395829369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217625214660494887444423301 40804727748842791395829369)
    ·
      refine ⟨30603545811632093546872027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40804727748842791395829369 30603545811632093546872027)
      ·
        refine ⟨45905318717448140320308041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30603545811632093546872027 45905318717448140320308041)
        ·
          refine ⟨34428989038086105240231031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45905318717448140320308041 34428989038086105240231031)
          ·
            refine ⟨51643483557129157860346547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34428989038086105240231031 51643483557129157860346547)
            ·
              refine ⟨77465225335693736790519821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51643483557129157860346547 77465225335693736790519821)
              ·
                refine ⟨29049459500885151296444933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77465225335693736790519821 29049459500885151296444933)
                ·
                  refine ⟨5446773656415965868083425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29049459500885151296444933 5446773656415965868083425)
                  ·
                    refine ⟨4085080242311974401062569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5446773656415965868083425 4085080242311974401062569)
                    ·
                      refine ⟨3063810181733980800796927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085080242311974401062569 3063810181733980800796927)
                      ·
                        rfl

theorem cell23_5966749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_5966749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966749 prefixEnd_5966749 := by exact prefixLift 5966749
  have htrace : WordTrace (prefixWord ++ tailWord_5966749) baseStart_5966749 baseEnd_5966749 := by
    simpa [prefixWord, tailWord_5966749, baseEnd_5966749] using wordTrace_append hprefix tailTrace_5966749
  have hstable : (prefixWord ++ tailWord_5966749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966749).length < 2 ^ (prefixWord ++ tailWord_5966749).sum := by decide
  have hdescent : baseEnd_5966749 < baseStart_5966749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966755 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 7]
def baseStart_5966755 : Nat := 118140960795 + 5966755 * 2 ^ 59
def prefixEnd_5966755 : Nat := 4983230072969 + 3 ^ 40 * 5966755 * 2
def baseEnd_5966755 : Nat := 340423695846434197480211

theorem tailTrace_5966755 : CollatzResearch.WordTrace tailWord_5966755 prefixEnd_5966755 340423695846434197480211 := by
  unfold tailWord_5966755
  simp only [CollatzResearch.WordTrace]
  refine ⟨217625433498473150469141719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145083622332315433646094479 217625433498473150469141719)
  ·
    refine ⟨326438150247709725703712579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217625433498473150469141719 326438150247709725703712579)
    ·
      refine ⟨489657225371564588555568869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326438150247709725703712579 489657225371564588555568869)
      ·
        refine ⟨91810729757168360354169163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 489657225371564588555568869 91810729757168360354169163)
        ·
          refine ⟨137716094635752540531253745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91810729757168360354169163 137716094635752540531253745)
          ·
            refine ⟨103287070976814405398440309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137716094635752540531253745 103287070976814405398440309)
            ·
              refine ⟨9683162904076350506103779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103287070976814405398440309 9683162904076350506103779)
              ·
                refine ⟨14524744356114525759155669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9683162904076350506103779 14524744356114525759155669)
                ·
                  refine ⟨340423695846434197480211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14524744356114525759155669 340423695846434197480211)
                  ·
                    rfl

theorem cell23_5966755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 7].length) (baseStart_5966755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966755 prefixEnd_5966755 := by exact prefixLift 5966755
  have htrace : WordTrace (prefixWord ++ tailWord_5966755) baseStart_5966755 baseEnd_5966755 := by
    simpa [prefixWord, tailWord_5966755, baseEnd_5966755] using wordTrace_append hprefix tailTrace_5966755
  have hstable : (prefixWord ++ tailWord_5966755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966755).length < 2 ^ (prefixWord ++ tailWord_5966755).sum := by decide
  have hdescent : baseEnd_5966755 < baseStart_5966755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966795 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 5]
def baseStart_5966795 : Nat := 118140960795 + 5966795 * 2 ^ 59
def prefixEnd_5966795 : Nat := 4983230072969 + 3 ^ 40 * 5966795 * 2
def baseEnd_5966795 : Nat := 3063833801844087620821715

theorem tailTrace_5966795 : CollatzResearch.WordTrace tailWord_5966795 prefixEnd_5966795 3063833801844087620821715 := by
  unfold tailWord_5966795
  simp only [CollatzResearch.WordTrace]
  refine ⟨217626892418328237300597839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145084594945552158200398559 217626892418328237300597839)
  ·
    refine ⟨326440338627492355950896759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217626892418328237300597839 326440338627492355950896759)
    ·
      refine ⟨489660507941238533926345139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326440338627492355950896759 489660507941238533926345139)
      ·
        refine ⟨734490761911857800889517709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489660507941238533926345139 734490761911857800889517709)
        ·
          refine ⟨275434035716946675333569141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 734490761911857800889517709 275434035716946675333569141)
          ·
            refine ⟨25821940848463750812522107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 275434035716946675333569141 25821940848463750812522107)
            ·
              refine ⟨38732911272695626218783161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25821940848463750812522107 38732911272695626218783161)
              ·
                refine ⟨29049683454521719664087371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38732911272695626218783161 29049683454521719664087371)
                ·
                  refine ⟨43574525181782579496131057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29049683454521719664087371 43574525181782579496131057)
                  ·
                    refine ⟨32680893886336934622098293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43574525181782579496131057 32680893886336934622098293)
                    ·
                      refine ⟨3063833801844087620821715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32680893886336934622098293 3063833801844087620821715)
                      ·
                        rfl

theorem cell23_5966795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_5966795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966795 prefixEnd_5966795 := by exact prefixLift 5966795
  have htrace : WordTrace (prefixWord ++ tailWord_5966795) baseStart_5966795 baseEnd_5966795 := by
    simpa [prefixWord, tailWord_5966795, baseEnd_5966795] using wordTrace_append hprefix tailTrace_5966795
  have hstable : (prefixWord ++ tailWord_5966795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966795).length < 2 ^ (prefixWord ++ tailWord_5966795).sum := by decide
  have hdescent : baseEnd_5966795 < baseStart_5966795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966806 : List Nat := [5, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_5966806 : Nat := 118140960795 + 5966806 * 2 ^ 59
def prefixEnd_5966806 : Nat := 4983230072969 + 3 ^ 40 * 5966806 * 2
def baseEnd_5966806 : Nat := 340426605570143008642685

theorem tailTrace_5966806 : CollatzResearch.WordTrace tailWord_5966806 prefixEnd_5966806 340426605570143008642685 := by
  unfold tailWord_5966806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13601705851330524136203017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145084862414192257452832181 13601705851330524136203017)
  ·
    refine ⟨10201279388497893102152263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13601705851330524136203017 10201279388497893102152263)
    ·
      refine ⟨15301919082746839653228395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10201279388497893102152263 15301919082746839653228395)
      ·
        refine ⟨22952878624120259479842593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15301919082746839653228395 22952878624120259479842593)
        ·
          refine ⟨17214658968090194609881945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22952878624120259479842593 17214658968090194609881945)
          ·
            refine ⟨12910994226067645957411459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17214658968090194609881945 12910994226067645957411459)
            ·
              refine ⟨19366491339101468936117189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12910994226067645957411459 19366491339101468936117189)
              ·
                refine ⟨3631217126081525425521973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19366491339101468936117189 3631217126081525425521973)
                ·
                  refine ⟨340426605570143008642685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3631217126081525425521973 340426605570143008642685)
                  ·
                    rfl

theorem cell23_5966806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_5966806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966806 prefixEnd_5966806 := by exact prefixLift 5966806
  have htrace : WordTrace (prefixWord ++ tailWord_5966806) baseStart_5966806 baseEnd_5966806 := by
    simpa [prefixWord, tailWord_5966806, baseEnd_5966806] using wordTrace_append hprefix tailTrace_5966806
  have hstable : (prefixWord ++ tailWord_5966806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966806).length < 2 ^ (prefixWord ++ tailWord_5966806).sum := by decide
  have hdescent : baseEnd_5966806 < baseStart_5966806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966845 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 8]
def baseStart_5966845 : Nat := 118140960795 + 5966845 * 2 ^ 59
def prefixEnd_5966845 : Nat := 4983230072969 + 3 ^ 40 * 5966845 * 2
def baseEnd_5966845 : Nat := 340428830652979158355165

theorem tailTrace_5966845 : CollatzResearch.WordTrace tailWord_5966845 prefixEnd_5966845 340428830652979158355165 := by
  unfold tailWord_5966845
  simp only [CollatzResearch.WordTrace]
  refine ⟨217628716068147095839917989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145085810712098063893278659 217628716068147095839917989)
  ·
    refine ⟨40805384262777580469984623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217628716068147095839917989 40805384262777580469984623)
    ·
      refine ⟨61208076394166370704976935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40805384262777580469984623 61208076394166370704976935)
      ·
        refine ⟨91812114591249556057465403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61208076394166370704976935 91812114591249556057465403)
        ·
          refine ⟨137718171886874334086198105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91812114591249556057465403 137718171886874334086198105)
          ·
            refine ⟨103288628915155750564648579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137718171886874334086198105 103288628915155750564648579)
            ·
              refine ⟨154932943372733625846972869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103288628915155750564648579 154932943372733625846972869)
              ·
                refine ⟨29049926882387554846307413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154932943372733625846972869 29049926882387554846307413)
                ·
                  refine ⟨340428830652979158355165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29049926882387554846307413 340428830652979158355165)
                  ·
                    rfl

theorem cell23_5966845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_5966845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966845 prefixEnd_5966845 := by exact prefixLift 5966845
  have htrace : WordTrace (prefixWord ++ tailWord_5966845) baseStart_5966845 baseEnd_5966845 := by
    simpa [prefixWord, tailWord_5966845, baseEnd_5966845] using wordTrace_append hprefix tailTrace_5966845
  have hstable : (prefixWord ++ tailWord_5966845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966845).length < 2 ^ (prefixWord ++ tailWord_5966845).sum := by decide
  have hdescent : baseEnd_5966845 < baseStart_5966845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966862 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_5966862 : Nat := 118140960795 + 5966862 * 2 ^ 59
def prefixEnd_5966862 : Nat := 4983230072969 + 3 ^ 40 * 5966862 * 2
def baseEnd_5966862 : Nat := 340429800560882095409323

theorem tailTrace_5966862 : CollatzResearch.WordTrace tailWord_5966862 prefixEnd_5966862 340429800560882095409323 := by
  unfold tailWord_5966862
  simp only [CollatzResearch.WordTrace]
  refine ⟨27203667013635688467910855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145086224072723671828857893 27203667013635688467910855)
  ·
    refine ⟨40805500520453532701866283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27203667013635688467910855 40805500520453532701866283)
    ·
      refine ⟨61208250780680299052799425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40805500520453532701866283 61208250780680299052799425)
      ·
        refine ⟨45906188085510224289599569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61208250780680299052799425 45906188085510224289599569)
        ·
          refine ⟨34429641064132668217199677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45906188085510224289599569 34429641064132668217199677)
          ·
            refine ⟨12911115399049750581449879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34429641064132668217199677 12911115399049750581449879)
            ·
              refine ⟨19366673098574625872174819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12911115399049750581449879 19366673098574625872174819)
              ·
                refine ⟨29050009647861938808262229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19366673098574625872174819 29050009647861938808262229)
                ·
                  refine ⟨340429800560882095409323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29050009647861938808262229 340429800560882095409323)
                  ·
                    rfl

theorem cell23_5966862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_5966862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966862 prefixEnd_5966862 := by exact prefixLift 5966862
  have htrace : WordTrace (prefixWord ++ tailWord_5966862) baseStart_5966862 baseEnd_5966862 := by
    simpa [prefixWord, tailWord_5966862, baseEnd_5966862] using wordTrace_append hprefix tailTrace_5966862
  have hstable : (prefixWord ++ tailWord_5966862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966862).length < 2 ^ (prefixWord ++ tailWord_5966862).sum := by decide
  have hdescent : baseEnd_5966862 < baseStart_5966862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966879 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 6]
def baseStart_5966879 : Nat := 118140960795 + 5966879 * 2 ^ 59
def prefixEnd_5966879 : Nat := 4983230072969 + 3 ^ 40 * 5966879 * 2
def baseEnd_5966879 : Nat := 340430770468785032463481

theorem tailTrace_5966879 : CollatzResearch.WordTrace tailWord_5966879 prefixEnd_5966879 340430770468785032463481 := by
  unfold tailWord_5966879
  simp only [CollatzResearch.WordTrace]
  refine ⟨217629956150023919646655691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145086637433349279764437127 217629956150023919646655691)
  ·
    refine ⟨326444934225035879469983537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217629956150023919646655691 326444934225035879469983537)
    ·
      refine ⟨244833700668776909602487653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326444934225035879469983537 244833700668776909602487653)
      ·
        refine ⟨45906318875395670550466435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244833700668776909602487653 45906318875395670550466435)
        ·
          refine ⟨68859478313093505825699653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45906318875395670550466435 68859478313093505825699653)
          ·
            refine ⟨12911152183705032342318685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68859478313093505825699653 12911152183705032342318685)
            ·
              refine ⟨4841682068889387128369507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12911152183705032342318685 4841682068889387128369507)
              ·
                refine ⟨7262523103334080692554261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841682068889387128369507 7262523103334080692554261)
                ·
                  refine ⟨340430770468785032463481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7262523103334080692554261 340430770468785032463481)
                  ·
                    rfl

theorem cell23_5966879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 6].length) (baseStart_5966879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966879 prefixEnd_5966879 := by exact prefixLift 5966879
  have htrace : WordTrace (prefixWord ++ tailWord_5966879) baseStart_5966879 baseEnd_5966879 := by
    simpa [prefixWord, tailWord_5966879, baseEnd_5966879] using wordTrace_append hprefix tailTrace_5966879
  have hstable : (prefixWord ++ tailWord_5966879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966879).length < 2 ^ (prefixWord ++ tailWord_5966879).sum := by decide
  have hdescent : baseEnd_5966879 < baseStart_5966879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966899 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 2, 3, 2]
def baseStart_5966899 : Nat := 118140960795 + 5966899 * 2 ^ 59
def prefixEnd_5966899 : Nat := 4983230072969 + 3 ^ 40 * 5966899 * 2
def baseEnd_5966899 : Nat := 3063887203832155213921237

theorem tailTrace_5966899 : CollatzResearch.WordTrace tailWord_5966899 prefixEnd_5966899 3063887203832155213921237 := by
  unfold tailWord_5966899
  simp only [CollatzResearch.WordTrace]
  refine ⟨217630685609951463062383751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145087123739967642041589167 217630685609951463062383751)
  ·
    refine ⟨326446028414927194593575627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217630685609951463062383751 326446028414927194593575627)
    ·
      refine ⟨489669042622390791890363441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326446028414927194593575627 489669042622390791890363441)
      ·
        refine ⟨367251781966793093917772581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489669042622390791890363441 367251781966793093917772581)
        ·
          refine ⟨68859709118773705109582359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367251781966793093917772581 68859709118773705109582359)
          ·
            refine ⟨103289563678160557664373539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68859709118773705109582359 103289563678160557664373539)
            ·
              refine ⟨154934345517240836496560309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103289563678160557664373539 154934345517240836496560309)
              ·
                refine ⟨14525094892241328421552529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154934345517240836496560309 14525094892241328421552529)
                ·
                  refine ⟨10893821169180996316164397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14525094892241328421552529 10893821169180996316164397)
                  ·
                    refine ⟨4085182938442873618561649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10893821169180996316164397 4085182938442873618561649)
                    ·
                      refine ⟨3063887203832155213921237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085182938442873618561649 3063887203832155213921237)
                      ·
                        rfl

theorem cell23_5966899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 3, 2].length) (baseStart_5966899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966899 prefixEnd_5966899 := by exact prefixLift 5966899
  have htrace : WordTrace (prefixWord ++ tailWord_5966899) baseStart_5966899 baseEnd_5966899 := by
    simpa [prefixWord, tailWord_5966899, baseEnd_5966899] using wordTrace_append hprefix tailTrace_5966899
  have hstable : (prefixWord ++ tailWord_5966899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966899).length < 2 ^ (prefixWord ++ tailWord_5966899).sum := by decide
  have hdescent : baseEnd_5966899 < baseStart_5966899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966900 : List Nat := [2, 5, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_5966900 : Nat := 118140960795 + 5966900 * 2 ^ 59
def prefixEnd_5966900 : Nat := 4983230072969 + 3 ^ 40 * 5966900 * 2
def baseEnd_5966900 : Nat := 1021295905770936570002911

theorem tailTrace_5966900 : CollatzResearch.WordTrace tailWord_5966900 prefixEnd_5966900 1021295905770936570002911 := by
  unfold tailWord_5966900
  simp only [CollatzResearch.WordTrace]
  refine ⟨108815361041473920116585077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145087148055298560155446769 108815361041473920116585077)
  ·
    refine ⟨10201440097638180010929851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108815361041473920116585077 10201440097638180010929851)
    ·
      refine ⟨15302160146457270016394777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10201440097638180010929851 15302160146457270016394777)
      ·
        refine ⟨11476620109842952512296083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15302160146457270016394777 11476620109842952512296083)
        ·
          refine ⟨17214930164764428768444125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11476620109842952512296083 17214930164764428768444125)
          ·
            refine ⟨6455598811786660788166547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17214930164764428768444125 6455598811786660788166547)
            ·
              refine ⟨9683398217679991182249821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455598811786660788166547 9683398217679991182249821)
              ·
                refine ⟨3631274331629996693343683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9683398217679991182249821 3631274331629996693343683)
                ·
                  refine ⟨5446911497444995040015525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631274331629996693343683 5446911497444995040015525)
                  ·
                    refine ⟨1021295905770936570002911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5446911497444995040015525 1021295905770936570002911)
                    ·
                      rfl

theorem cell23_5966900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_5966900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966900 prefixEnd_5966900 := by exact prefixLift 5966900
  have htrace : WordTrace (prefixWord ++ tailWord_5966900) baseStart_5966900 baseEnd_5966900 := by
    simpa [prefixWord, tailWord_5966900, baseEnd_5966900] using wordTrace_append hprefix tailTrace_5966900
  have hstable : (prefixWord ++ tailWord_5966900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966900).length < 2 ^ (prefixWord ++ tailWord_5966900).sum := by decide
  have hdescent : baseEnd_5966900 < baseStart_5966900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966909 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_5966909 : Nat := 118140960795 + 5966909 * 2 ^ 59
def prefixEnd_5966909 : Nat := 4983230072969 + 3 ^ 40 * 5966909 * 2
def baseEnd_5966909 : Nat := 1021297446212900058265397

theorem tailTrace_5966909 : CollatzResearch.WordTrace tailWord_5966909 prefixEnd_5966909 1021297446212900058265397 := by
  unfold tailWord_5966909
  simp only [CollatzResearch.WordTrace]
  refine ⟨217631050339915234770247781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145087366893276823180165187 217631050339915234770247781)
  ·
    refine ⟨40805821938734106519421459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217631050339915234770247781 40805821938734106519421459)
    ·
      refine ⟨61208732908101159779132189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40805821938734106519421459 61208732908101159779132189)
      ·
        refine ⟨22953274840537934917174571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61208732908101159779132189 22953274840537934917174571)
        ·
          refine ⟨34429912260806902375761857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22953274840537934917174571 34429912260806902375761857)
          ·
            refine ⟨25822434195605176781821393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34429912260806902375761857 25822434195605176781821393)
            ·
              refine ⟨19366825646703882586366045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25822434195605176781821393 19366825646703882586366045)
              ·
                refine ⟨7262559617513955969887267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19366825646703882586366045 7262559617513955969887267)
                ·
                  refine ⟨10893839426270933954830901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7262559617513955969887267 10893839426270933954830901)
                  ·
                    refine ⟨1021297446212900058265397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10893839426270933954830901 1021297446212900058265397)
                    ·
                      rfl

theorem cell23_5966909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_5966909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966909 prefixEnd_5966909 := by exact prefixLift 5966909
  have htrace : WordTrace (prefixWord ++ tailWord_5966909) baseStart_5966909 baseEnd_5966909 := by
    simpa [prefixWord, tailWord_5966909, baseEnd_5966909] using wordTrace_append hprefix tailTrace_5966909
  have hstable : (prefixWord ++ tailWord_5966909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966909).length < 2 ^ (prefixWord ++ tailWord_5966909).sum := by decide
  have hdescent : baseEnd_5966909 < baseStart_5966909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966946 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5966946 : Nat := 118140960795 + 5966946 * 2 ^ 59
def prefixEnd_5966946 : Nat := 4983230072969 + 3 ^ 40 * 5966946 * 2
def baseEnd_5966946 : Nat := 3063911337422916530033521

theorem tailTrace_5966946 : CollatzResearch.WordTrace tailWord_5966946 prefixEnd_5966946 3063911337422916530033521 := by
  unfold tailWord_5966946
  simp only [CollatzResearch.WordTrace]
  refine ⟨54408099960195297522336173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145088266560520793392896461 54408099960195297522336173)
  ·
    refine ⟨20403037485073236570876065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54408099960195297522336173 20403037485073236570876065)
    ·
      refine ⟨15302278113804927428157049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20403037485073236570876065 15302278113804927428157049)
      ·
        refine ⟨11476708585353695571117787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15302278113804927428157049 11476708585353695571117787)
        ·
          refine ⟨17215062878030543356676681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11476708585353695571117787 17215062878030543356676681)
          ·
            refine ⟨12911297158522907517507511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17215062878030543356676681 12911297158522907517507511)
            ·
              refine ⟨19366945737784361276261267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12911297158522907517507511 19366945737784361276261267)
              ·
                refine ⟨29050418606676541914391901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19366945737784361276261267 29050418606676541914391901)
                ·
                  refine ⟨10893906977503703217896963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29050418606676541914391901 10893906977503703217896963)
                  ·
                    refine ⟨16340860466255554826845445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10893906977503703217896963 16340860466255554826845445)
                    ·
                      refine ⟨3063911337422916530033521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16340860466255554826845445 3063911337422916530033521)
                      ·
                        rfl

theorem cell23_5966946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5966946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966946 prefixEnd_5966946 := by exact prefixLift 5966946
  have htrace : WordTrace (prefixWord ++ tailWord_5966946) baseStart_5966946 baseEnd_5966946 := by
    simpa [prefixWord, tailWord_5966946, baseEnd_5966946] using wordTrace_append hprefix tailTrace_5966946
  have hstable : (prefixWord ++ tailWord_5966946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966946).length < 2 ^ (prefixWord ++ tailWord_5966946).sum := by decide
  have hdescent : baseEnd_5966946 < baseStart_5966946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966949 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 3]
def baseStart_5966949 : Nat := 118140960795 + 5966949 * 2 ^ 59
def prefixEnd_5966949 : Nat := 4983230072969 + 3 ^ 40 * 5966949 * 2
def baseEnd_5966949 : Nat := 3063912877864880018296007

theorem tailTrace_5966949 : CollatzResearch.WordTrace tailWord_5966949 prefixEnd_5966949 3063912877864880018296007 := by
  unfold tailWord_5966949
  simp only [CollatzResearch.WordTrace]
  refine ⟨217632509259770321601703901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145088339506513547734469267 217632509259770321601703901)
  ·
    refine ⟨81612190972413870600638963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217632509259770321601703901 81612190972413870600638963)
    ·
      refine ⟨122418286458620805900958445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81612190972413870600638963 122418286458620805900958445)
      ·
        refine ⟨45906857421982802212859417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122418286458620805900958445 45906857421982802212859417)
        ·
          refine ⟨34430143066487101659644563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45906857421982802212859417 34430143066487101659644563)
          ·
            refine ⟨51645214599730652489466845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34430143066487101659644563 51645214599730652489466845)
            ·
              refine ⟨19366955474898994683550067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51645214599730652489466845 19366955474898994683550067)
              ·
                refine ⟨29050433212348492025325101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19366955474898994683550067 29050433212348492025325101)
                ·
                  refine ⟨10893912454630684509496913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29050433212348492025325101 10893912454630684509496913)
                  ·
                    refine ⟨8170434340973013382122685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10893912454630684509496913 8170434340973013382122685)
                    ·
                      refine ⟨3063912877864880018296007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8170434340973013382122685 3063912877864880018296007)
                      ·
                        rfl

theorem cell23_5966949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_5966949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966949 prefixEnd_5966949 := by exact prefixLift 5966949
  have htrace : WordTrace (prefixWord ++ tailWord_5966949) baseStart_5966949 baseEnd_5966949 := by
    simpa [prefixWord, tailWord_5966949, baseEnd_5966949] using wordTrace_append hprefix tailTrace_5966949
  have hstable : (prefixWord ++ tailWord_5966949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966949).length < 2 ^ (prefixWord ++ tailWord_5966949).sum := by decide
  have hdescent : baseEnd_5966949 < baseStart_5966949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966974 : List Nat := [4, 2, 4, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5966974 : Nat := 118140960795 + 5966974 * 2 ^ 59
def prefixEnd_5966974 : Nat := 4983230072969 + 3 ^ 40 * 5966974 * 2
def baseEnd_5966974 : Nat := 3063925714881242420483393

theorem tailTrace_5966974 : CollatzResearch.WordTrace tailWord_5966974 prefixEnd_5966974 3063925714881242420483393 := by
  unfold tailWord_5966974
  simp only [CollatzResearch.WordTrace]
  refine ⟨27204177635584968858920497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145088947389786500580909317 27204177635584968858920497)
  ·
    refine ⟨20403133226688726644190373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27204177635584968858920497 20403133226688726644190373)
    ·
      refine ⟨3825587480004136245785695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20403133226688726644190373 3825587480004136245785695)
      ·
        refine ⟨5738381220006204368678543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825587480004136245785695 5738381220006204368678543)
        ·
          refine ⟨8607571830009306553017815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5738381220006204368678543 8607571830009306553017815)
          ·
            refine ⟨12911357745013959829526723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8607571830009306553017815 12911357745013959829526723)
            ·
              refine ⟨19367036617520939744290085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12911357745013959829526723 19367036617520939744290085)
              ·
                refine ⟨3631319365785176202054391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19367036617520939744290085 3631319365785176202054391)
                ·
                  refine ⟨5446979048677764303081587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631319365785176202054391 5446979048677764303081587)
                  ·
                    refine ⟨8170468573016646454622381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5446979048677764303081587 8170468573016646454622381)
                    ·
                      refine ⟨3063925714881242420483393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8170468573016646454622381 3063925714881242420483393)
                      ·
                        rfl

theorem cell23_5966974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5966974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966974 prefixEnd_5966974 := by exact prefixLift 5966974
  have htrace : WordTrace (prefixWord ++ tailWord_5966974) baseStart_5966974 baseEnd_5966974 := by
    simpa [prefixWord, tailWord_5966974, baseEnd_5966974] using wordTrace_append hprefix tailTrace_5966974
  have hstable : (prefixWord ++ tailWord_5966974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966974).length < 2 ^ (prefixWord ++ tailWord_5966974).sum := by decide
  have hdescent : baseEnd_5966974 < baseStart_5966974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5966980 : List Nat := [2, 3, 2, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_5966980 : Nat := 118140960795 + 5966980 * 2 ^ 59
def prefixEnd_5966980 : Nat := 4983230072969 + 3 ^ 40 * 5966980 * 2
def baseEnd_5966980 : Nat := 3063928795765169397008365

theorem tailTrace_5966980 : CollatzResearch.WordTrace tailWord_5966980 prefixEnd_5966980 3063928795765169397008365 := by
  unfold tailWord_5966980
  simp only [CollatzResearch.WordTrace]
  refine ⟨108816819961329006948041197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145089093281772009264054929 108816819961329006948041197)
  ·
    refine ⟨40806307485498377605515449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108816819961329006948041197 40806307485498377605515449)
    ·
      refine ⟨30604730614123783204136587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40806307485498377605515449 30604730614123783204136587)
      ·
        refine ⟨45907095921185674806204881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30604730614123783204136587 45907095921185674806204881)
        ·
          refine ⟨34430321940889256104653661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45907095921185674806204881 34430321940889256104653661)
          ·
            refine ⟨12911370727833471039245123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34430321940889256104653661 12911370727833471039245123)
            ·
              refine ⟨19367056091750206558867685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12911370727833471039245123 19367056091750206558867685)
              ·
                refine ⟨3631323017203163729787691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19367056091750206558867685 3631323017203163729787691)
                ·
                  refine ⟨5446984525804745594681537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631323017203163729787691 5446984525804745594681537)
                  ·
                    refine ⟨4085238394353559196011153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5446984525804745594681537 4085238394353559196011153)
                    ·
                      refine ⟨3063928795765169397008365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085238394353559196011153 3063928795765169397008365)
                      ·
                        rfl

theorem cell23_5966980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_5966980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5966980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5966980 prefixEnd_5966980 := by exact prefixLift 5966980
  have htrace : WordTrace (prefixWord ++ tailWord_5966980) baseStart_5966980 baseEnd_5966980 := by
    simpa [prefixWord, tailWord_5966980, baseEnd_5966980] using wordTrace_append hprefix tailTrace_5966980
  have hstable : (prefixWord ++ tailWord_5966980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5966980).length < 2 ^ (prefixWord ++ tailWord_5966980).sum := by decide
  have hdescent : baseEnd_5966980 < baseStart_5966980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5966980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967023 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 1, 3, 2]
def baseStart_5967023 : Nat := 118140960795 + 5967023 * 2 ^ 59
def prefixEnd_5967023 : Nat := 4983230072969 + 3 ^ 40 * 5967023 * 2
def baseEnd_5967023 : Nat := 3063950875433312728770667

theorem tailTrace_5967023 : CollatzResearch.WordTrace tailWord_5967023 prefixEnd_5967023 3063950875433312728770667 := by
  unfold tailWord_5967023
  simp only [CollatzResearch.WordTrace]
  refine ⟨217635208261502232239897723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145090138841001488159931815 217635208261502232239897723)
  ·
    refine ⟨326452812392253348359846585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217635208261502232239897723 326452812392253348359846585)
    ·
      refine ⟨244839609294190011269884939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326452812392253348359846585 244839609294190011269884939)
      ·
        refine ⟨367259413941285016904827409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244839609294190011269884939 367259413941285016904827409)
        ·
          refine ⟨275444560455963762678620557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367259413941285016904827409 275444560455963762678620557)
          ·
            refine ⟨103291710170986411004482709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275444560455963762678620557 103291710170986411004482709)
            ·
              refine ⟨4841798914264988015835127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103291710170986411004482709 4841798914264988015835127)
              ·
                refine ⟨7262698371397482023752691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841798914264988015835127 7262698371397482023752691)
                ·
                  refine ⟨10894047557096223035629037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7262698371397482023752691 10894047557096223035629037)
                  ·
                    refine ⟨4085267833911083638360889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10894047557096223035629037 4085267833911083638360889)
                    ·
                      refine ⟨3063950875433312728770667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085267833911083638360889 3063950875433312728770667)
                      ·
                        rfl

theorem cell23_5967023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 3, 2].length) (baseStart_5967023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967023 prefixEnd_5967023 := by exact prefixLift 5967023
  have htrace : WordTrace (prefixWord ++ tailWord_5967023) baseStart_5967023 baseEnd_5967023 := by
    simpa [prefixWord, tailWord_5967023, baseEnd_5967023] using wordTrace_append hprefix tailTrace_5967023
  have hstable : (prefixWord ++ tailWord_5967023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967023).length < 2 ^ (prefixWord ++ tailWord_5967023).sum := by decide
  have hdescent : baseEnd_5967023 < baseStart_5967023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967076 : List Nat := [2, 3, 1, 1, 1, 2, 5, 3, 5]
def baseStart_5967076 : Nat := 118140960795 + 5967076 * 2 ^ 59
def prefixEnd_5967076 : Nat := 4983230072969 + 3 ^ 40 * 5967076 * 2
def baseEnd_5967076 : Nat := 340442009989777891267547

theorem tailTrace_5967076 : CollatzResearch.WordTrace tailWord_5967076 prefixEnd_5967076 340442009989777891267547 := by
  unfold tailWord_5967076
  simp only [CollatzResearch.WordTrace]
  refine ⟨108818570665155111145788541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145091427553540148194384721 108818570665155111145788541)
  ·
    refine ⟨40806963999433166679670703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108818570665155111145788541 40806963999433166679670703)
    ·
      refine ⟨61210445999149750019506055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40806963999433166679670703 61210445999149750019506055)
      ·
        refine ⟨91815668998724625029259083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61210445999149750019506055 91815668998724625029259083)
        ·
          refine ⟨137723503498086937543888625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91815668998724625029259083 137723503498086937543888625)
          ·
            refine ⟨103292627623565203157916469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137723503498086937543888625 103292627623565203157916469)
            ·
              refine ⟨9683683839709237796054669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103292627623565203157916469 9683683839709237796054669)
              ·
                refine ⟨3631381439890964173520501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9683683839709237796054669 3631381439890964173520501)
                ·
                  refine ⟨340442009989777891267547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3631381439890964173520501 340442009989777891267547)
                  ·
                    rfl

theorem cell23_5967076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_5967076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967076 prefixEnd_5967076 := by exact prefixLift 5967076
  have htrace : WordTrace (prefixWord ++ tailWord_5967076) baseStart_5967076 baseEnd_5967076 := by
    simpa [prefixWord, tailWord_5967076, baseEnd_5967076] using wordTrace_append hprefix tailTrace_5967076
  have hstable : (prefixWord ++ tailWord_5967076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967076).length < 2 ^ (prefixWord ++ tailWord_5967076).sum := by decide
  have hdescent : baseEnd_5967076 < baseStart_5967076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967109 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 4]
def baseStart_5967109 : Nat := 118140960795 + 5967109 * 2 ^ 59
def prefixEnd_5967109 : Nat := 4983230072969 + 3 ^ 40 * 5967109 * 2
def baseEnd_5967109 : Nat := 3063995034769599392295271

theorem tailTrace_5967109 : CollatzResearch.WordTrace tailWord_5967109 prefixEnd_5967109 3063995034769599392295271 := by
  unfold tailWord_5967109
  simp only [CollatzResearch.WordTrace]
  refine ⟨217638344939190668927528381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145092229959460445951685587 217638344939190668927528381)
  ·
    refine ⟨81614379352196500847823143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217638344939190668927528381 81614379352196500847823143)
    ·
      refine ⟨122421569028294751271734715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81614379352196500847823143 122421569028294751271734715)
      ·
        refine ⟨183632353542442126907602073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122421569028294751271734715 183632353542442126907602073)
        ·
          refine ⟨137724265156831595180701555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183632353542442126907602073 137724265156831595180701555)
          ·
            refine ⟨206586397735247392771052333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137724265156831595180701555 206586397735247392771052333)
            ·
              refine ⟨77469899150717772289144625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206586397735247392771052333 77469899150717772289144625)
              ·
                refine ⟨58102424363038329216858469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77469899150717772289144625 58102424363038329216858469)
                ·
                  refine ⟨10894204568069686728160963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58102424363038329216858469 10894204568069686728160963)
                  ·
                    refine ⟨16341306852104530092241445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10894204568069686728160963 16341306852104530092241445)
                    ·
                      refine ⟨3063995034769599392295271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16341306852104530092241445 3063995034769599392295271)
                      ·
                        rfl

theorem cell23_5967109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_5967109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967109 prefixEnd_5967109 := by exact prefixLift 5967109
  have htrace : WordTrace (prefixWord ++ tailWord_5967109) baseStart_5967109 baseEnd_5967109 := by
    simpa [prefixWord, tailWord_5967109, baseEnd_5967109] using wordTrace_append hprefix tailTrace_5967109
  have hstable : (prefixWord ++ tailWord_5967109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967109).length < 2 ^ (prefixWord ++ tailWord_5967109).sum := by decide
  have hdescent : baseEnd_5967109 < baseStart_5967109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967159 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_5967159 : Nat := 118140960795 + 5967159 * 2 ^ 59
def prefixEnd_5967159 : Nat := 4983230072969 + 3 ^ 40 * 5967159 * 2
def baseEnd_5967159 : Nat := 3064020708802324196670041

theorem tailTrace_5967159 : CollatzResearch.WordTrace tailWord_5967159 prefixEnd_5967159 3064020708802324196670041 := by
  unfold tailWord_5967159
  simp only [CollatzResearch.WordTrace]
  refine ⟨217640168589009527466848531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145093445726006351644565687 217640168589009527466848531)
  ·
    refine ⟨326460252883514291200272797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217640168589009527466848531 326460252883514291200272797)
    ·
      refine ⟨122422594831317859200102299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326460252883514291200272797 122422594831317859200102299)
      ·
        refine ⟨183633892246976788800153449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122422594831317859200102299 183633892246976788800153449)
        ·
          refine ⟨137725419185232591600115087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183633892246976788800153449 137725419185232591600115087)
          ·
            refine ⟨206588128777848887400172631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137725419185232591600115087 206588128777848887400172631)
            ·
              refine ⟨309882193166773331100258947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206588128777848887400172631 309882193166773331100258947)
              ·
                refine ⟨464823289750159996650388421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309882193166773331100258947 464823289750159996650388421)
                ·
                  refine ⟨87154366828154999371947829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 464823289750159996650388421 87154366828154999371947829)
                  ·
                    refine ⟨8170721890139531191120109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87154366828154999371947829 8170721890139531191120109)
                    ·
                      refine ⟨3064020708802324196670041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8170721890139531191120109 3064020708802324196670041)
                      ·
                        rfl

theorem cell23_5967159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_5967159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967159 prefixEnd_5967159 := by exact prefixLift 5967159
  have htrace : WordTrace (prefixWord ++ tailWord_5967159) baseStart_5967159 baseEnd_5967159 := by
    simpa [prefixWord, tailWord_5967159, baseEnd_5967159] using wordTrace_append hprefix tailTrace_5967159
  have hstable : (prefixWord ++ tailWord_5967159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967159).length < 2 ^ (prefixWord ++ tailWord_5967159).sum := by decide
  have hdescent : baseEnd_5967159 < baseStart_5967159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967166 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_5967166 : Nat := 118140960795 + 5967166 * 2 ^ 59
def prefixEnd_5967166 : Nat := 4983230072969 + 3 ^ 40 * 5967166 * 2
def baseEnd_5967166 : Nat := 340447144796322852142501

theorem tailTrace_5967166 : CollatzResearch.WordTrace tailWord_5967166 prefixEnd_5967166 340447144796322852142501 := by
  unfold tailWord_5967166
  simp only [CollatzResearch.WordTrace]
  refine ⟨27205052987498020957794169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145093615933322778441568901 27205052987498020957794169)
  ·
    refine ⟨20403789740623515718345627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27205052987498020957794169 20403789740623515718345627)
    ·
      refine ⟨30605684610935273577518441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20403789740623515718345627 30605684610935273577518441)
      ·
        refine ⟨22954263458201455183138831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30605684610935273577518441 22954263458201455183138831)
        ·
          refine ⟨34431395187302182774708247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22954263458201455183138831 34431395187302182774708247)
          ·
            refine ⟨51647092780953274162062371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34431395187302182774708247 51647092780953274162062371)
            ·
              refine ⟨77470639171429911243093557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51647092780953274162062371 77470639171429911243093557)
              ·
                refine ⟨7262872422321554179040021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77470639171429911243093557 7262872422321554179040021)
                ·
                  refine ⟨340447144796322852142501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7262872422321554179040021 340447144796322852142501)
                  ·
                    rfl

theorem cell23_5967166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_5967166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967166 prefixEnd_5967166 := by exact prefixLift 5967166
  have htrace : WordTrace (prefixWord ++ tailWord_5967166) baseStart_5967166 baseEnd_5967166 := by
    simpa [prefixWord, tailWord_5967166, baseEnd_5967166] using wordTrace_append hprefix tailTrace_5967166
  have hstable : (prefixWord ++ tailWord_5967166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967166).length < 2 ^ (prefixWord ++ tailWord_5967166).sum := by decide
  have hdescent : baseEnd_5967166 < baseStart_5967166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967174 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_5967174 : Nat := 118140960795 + 5967174 * 2 ^ 59
def prefixEnd_5967174 : Nat := 4983230072969 + 3 ^ 40 * 5967174 * 2
def baseEnd_5967174 : Nat := 1021342803670713879327491

theorem tailTrace_5967174 : CollatzResearch.WordTrace tailWord_5967174 prefixEnd_5967174 1021342803670713879327491 := by
  unfold tailWord_5967174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6801272365123599532145143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145093810455970123352429717 6801272365123599532145143)
  ·
    refine ⟨10201908547685399298217715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6801272365123599532145143 10201908547685399298217715)
    ·
      refine ⟨15302862821528098947326573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10201908547685399298217715 15302862821528098947326573)
      ·
        refine ⟨5738573558073037105247465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15302862821528098947326573 5738573558073037105247465)
        ·
          refine ⟨4303930168554777828935599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5738573558073037105247465 4303930168554777828935599)
          ·
            refine ⟨6455895252832166743403399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303930168554777828935599 6455895252832166743403399)
            ·
              refine ⟨9683842879248250115105099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6455895252832166743403399 9683842879248250115105099)
              ·
                refine ⟨14525764318872375172657649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9683842879248250115105099 14525764318872375172657649)
                ·
                  refine ⟨10894323239154281379493237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14525764318872375172657649 10894323239154281379493237)
                  ·
                    refine ⟨1021342803670713879327491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10894323239154281379493237 1021342803670713879327491)
                    ·
                      rfl

theorem cell23_5967174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_5967174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967174 prefixEnd_5967174 := by exact prefixLift 5967174
  have htrace : WordTrace (prefixWord ++ tailWord_5967174) baseStart_5967174 baseEnd_5967174 := by
    simpa [prefixWord, tailWord_5967174, baseEnd_5967174] using wordTrace_append hprefix tailTrace_5967174
  have hstable : (prefixWord ++ tailWord_5967174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967174).length < 2 ^ (prefixWord ++ tailWord_5967174).sum := by decide
  have hdescent : baseEnd_5967174 < baseStart_5967174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967253 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 3]
def baseStart_5967253 : Nat := 118140960795 + 5967253 * 2 ^ 59
def prefixEnd_5967253 : Nat := 4983230072969 + 3 ^ 40 * 5967253 * 2
def baseEnd_5967253 : Nat := 3064068975983846828894609

theorem tailTrace_5967253 : CollatzResearch.WordTrace tailWord_5967253 prefixEnd_5967253 3064068975983846828894609 := by
  unfold tailWord_5967253
  simp only [CollatzResearch.WordTrace]
  refine ⟨217643597050668981520770413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145095731367112654347180275 217643597050668981520770413)
  ·
    refine ⟨81616348894000868070288905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217643597050668981520770413 81616348894000868070288905)
    ·
      refine ⟨61212261670500651052716679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81616348894000868070288905 61212261670500651052716679)
      ·
        refine ⟨91818392505750976579075019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61212261670500651052716679 91818392505750976579075019)
        ·
          refine ⟨137727588758626464868612529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91818392505750976579075019 137727588758626464868612529)
          ·
            refine ⟨103295691568969848651459397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137727588758626464868612529 103295691568969848651459397)
            ·
              refine ⟨19367942169181846622148637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103295691568969848651459397 19367942169181846622148637)
              ·
                refine ⟨7262978313443192483305739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19367942169181846622148637 7262978313443192483305739)
                ·
                  refine ⟨10894467470164788724958609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7262978313443192483305739 10894467470164788724958609)
                  ·
                    refine ⟨8170850602623591543718957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10894467470164788724958609 8170850602623591543718957)
                    ·
                      refine ⟨3064068975983846828894609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8170850602623591543718957 3064068975983846828894609)
                      ·
                        rfl

theorem cell23_5967253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_5967253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967253 prefixEnd_5967253 := by exact prefixLift 5967253
  have htrace : WordTrace (prefixWord ++ tailWord_5967253) baseStart_5967253 baseEnd_5967253 := by
    simpa [prefixWord, tailWord_5967253, baseEnd_5967253] using wordTrace_append hprefix tailTrace_5967253
  have hstable : (prefixWord ++ tailWord_5967253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967253).length < 2 ^ (prefixWord ++ tailWord_5967253).sum := by decide
  have hdescent : baseEnd_5967253 < baseStart_5967253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967277 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_5967277 : Nat := 118140960795 + 5967277 * 2 ^ 59
def prefixEnd_5967277 : Nat := 4983230072969 + 3 ^ 40 * 5967277 * 2
def baseEnd_5967277 : Nat := 1021360433173184911664833

theorem tailTrace_5967277 : CollatzResearch.WordTrace tailWord_5967277 prefixEnd_5967277 1021360433173184911664833 := by
  unfold tailWord_5967277
  simp only [CollatzResearch.WordTrace]
  refine ⟨217644472402582033619644085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145096314935054689079762723 217644472402582033619644085)
  ·
    refine ⟨20404169287742065651841633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217644472402582033619644085 20404169287742065651841633)
    ·
      refine ⟨15303126965806549238881225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20404169287742065651841633 15303126965806549238881225)
      ·
        refine ⟨11477345224354911929160919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15303126965806549238881225 11477345224354911929160919)
        ·
          refine ⟨17216017836532367893741379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11477345224354911929160919 17216017836532367893741379)
          ·
            refine ⟨25824026754798551840612069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17216017836532367893741379 25824026754798551840612069)
            ·
              refine ⟨4842005016524728470114763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25824026754798551840612069 4842005016524728470114763)
              ·
                refine ⟨7263007524787092705172145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842005016524728470114763 7263007524787092705172145)
                ·
                  refine ⟨5447255643590319528879109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7263007524787092705172145 5447255643590319528879109)
                  ·
                    refine ⟨1021360433173184911664833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5447255643590319528879109 1021360433173184911664833)
                    ·
                      rfl

theorem cell23_5967277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_5967277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967277 prefixEnd_5967277 := by exact prefixLift 5967277
  have htrace : WordTrace (prefixWord ++ tailWord_5967277) baseStart_5967277 baseEnd_5967277 := by
    simpa [prefixWord, tailWord_5967277, baseEnd_5967277] using wordTrace_append hprefix tailTrace_5967277
  have hstable : (prefixWord ++ tailWord_5967277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967277).length < 2 ^ (prefixWord ++ tailWord_5967277).sum := by decide
  have hdescent : baseEnd_5967277 < baseStart_5967277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967300 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_5967300 : Nat := 118140960795 + 5967300 * 2 ^ 59
def prefixEnd_5967300 : Nat := 4983230072969 + 3 ^ 40 * 5967300 * 2
def baseEnd_5967300 : Nat := 3064093109574608145006893

theorem tailTrace_5967300 : CollatzResearch.WordTrace tailWord_5967300 prefixEnd_5967300 3064093109574608145006893 := by
  unfold tailWord_5967300
  simp only [CollatzResearch.WordTrace]
  refine ⟨108822655640749354273865677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145096874187665805698487569 108822655640749354273865677)
  ·
    refine ⟨40808495865281007852699629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108822655640749354273865677 40808495865281007852699629)
    ·
      refine ⟨15303185949480377944762361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40808495865281007852699629 15303185949480377944762361)
      ·
        refine ⟨11477389462110283458571771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15303185949480377944762361 11477389462110283458571771)
        ·
          refine ⟨17216084193165425187857657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11477389462110283458571771 17216084193165425187857657)
          ·
            refine ⟨12912063144874068890893243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17216084193165425187857657 12912063144874068890893243)
            ·
              refine ⟨19368094717311103336339865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12912063144874068890893243 19368094717311103336339865)
              ·
                refine ⟨14526071037983327502254899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19368094717311103336339865 14526071037983327502254899)
                ·
                  refine ⟨21789106556974991253382349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14526071037983327502254899 21789106556974991253382349)
                  ·
                    refine ⟨8170914958865621720018381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21789106556974991253382349 8170914958865621720018381)
                    ·
                      refine ⟨3064093109574608145006893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8170914958865621720018381 3064093109574608145006893)
                      ·
                        rfl

theorem cell23_5967300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_5967300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967300 prefixEnd_5967300 := by exact prefixLift 5967300
  have htrace : WordTrace (prefixWord ++ tailWord_5967300) baseStart_5967300 baseEnd_5967300 := by
    simpa [prefixWord, tailWord_5967300, baseEnd_5967300] using wordTrace_append hprefix tailTrace_5967300
  have hstable : (prefixWord ++ tailWord_5967300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967300).length < 2 ^ (prefixWord ++ tailWord_5967300).sum := by decide
  have hdescent : baseEnd_5967300 < baseStart_5967300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967310 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_5967310 : Nat := 118140960795 + 5967310 * 2 ^ 59
def prefixEnd_5967310 : Nat := 4983230072969 + 3 ^ 40 * 5967310 * 2
def baseEnd_5967310 : Nat := 3064098244381153105881847

theorem tailTrace_5967310 : CollatzResearch.WordTrace tailWord_5967310 prefixEnd_5967310 3064098244381153105881847 := by
  unfold tailWord_5967310
  simp only [CollatzResearch.WordTrace]
  refine ⟨27205709501432810031949423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145097117340974986837063589 27205709501432810031949423)
  ·
    refine ⟨40808564252149215047924135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27205709501432810031949423 40808564252149215047924135)
    ·
      refine ⟨61212846378223822571886203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40808564252149215047924135 61212846378223822571886203)
      ·
        refine ⟨91819269567335733857829305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61212846378223822571886203 91819269567335733857829305)
        ·
          refine ⟨68864452175501800393371979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91819269567335733857829305 68864452175501800393371979)
          ·
            refine ⟨103296678263252700590057969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68864452175501800393371979 103296678263252700590057969)
            ·
              refine ⟨77472508697439525442543477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103296678263252700590057969 77472508697439525442543477)
              ·
                refine ⟨7263047690384955510238451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77472508697439525442543477 7263047690384955510238451)
                ·
                  refine ⟨10894571535577433265357677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7263047690384955510238451 10894571535577433265357677)
                  ·
                    refine ⟨4085464325841537474509129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10894571535577433265357677 4085464325841537474509129)
                    ·
                      refine ⟨3064098244381153105881847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085464325841537474509129 3064098244381153105881847)
                      ·
                        rfl

theorem cell23_5967310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_5967310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967310 prefixEnd_5967310 := by exact prefixLift 5967310
  have htrace : WordTrace (prefixWord ++ tailWord_5967310) baseStart_5967310 baseEnd_5967310 := by
    simpa [prefixWord, tailWord_5967310, baseEnd_5967310] using wordTrace_append hprefix tailTrace_5967310
  have hstable : (prefixWord ++ tailWord_5967310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967310).length < 2 ^ (prefixWord ++ tailWord_5967310).sum := by decide
  have hdescent : baseEnd_5967310 < baseStart_5967310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967318 : List Nat := [5, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_5967318 : Nat := 118140960795 + 5967318 * 2 ^ 59
def prefixEnd_5967318 : Nat := 4983230072969 + 3 ^ 40 * 5967318 * 2
def baseEnd_5967318 : Nat := 3064102352226389074581811

theorem tailTrace_5967318 : CollatzResearch.WordTrace tailWord_5967318 prefixEnd_5967318 3064102352226389074581811 := by
  unfold tailWord_5967318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13602872987214593601367913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145097311863622331747924405 13602872987214593601367913)
  ·
    refine ⟨10202154740410945201025935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13602872987214593601367913 10202154740410945201025935)
    ·
      refine ⟨15303232110616417801538903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10202154740410945201025935 15303232110616417801538903)
      ·
        refine ⟨22954848165924626702308355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15303232110616417801538903 22954848165924626702308355)
        ·
          refine ⟨34432272248886940053462533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22954848165924626702308355 34432272248886940053462533)
          ·
            refine ⟨6456051046666301260024225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34432272248886940053462533 6456051046666301260024225)
            ·
              refine ⟨4842038284999725945018169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6456051046666301260024225 4842038284999725945018169)
              ·
                refine ⟨3631528713749794458763627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4842038284999725945018169 3631528713749794458763627)
                ·
                  refine ⟨5447293070624691688145441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631528713749794458763627 5447293070624691688145441)
                  ·
                    refine ⟨4085469802968518766109081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5447293070624691688145441 4085469802968518766109081)
                    ·
                      refine ⟨3064102352226389074581811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085469802968518766109081 3064102352226389074581811)
                      ·
                        rfl

theorem cell23_5967318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_5967318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967318 prefixEnd_5967318 := by exact prefixLift 5967318
  have htrace : WordTrace (prefixWord ++ tailWord_5967318) baseStart_5967318 baseEnd_5967318 := by
    simpa [prefixWord, tailWord_5967318, baseEnd_5967318] using wordTrace_append hprefix tailTrace_5967318
  have hstable : (prefixWord ++ tailWord_5967318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967318).length < 2 ^ (prefixWord ++ tailWord_5967318).sum := by decide
  have hdescent : baseEnd_5967318 < baseStart_5967318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967333 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_5967333 : Nat := 118140960795 + 5967333 * 2 ^ 59
def prefixEnd_5967333 : Nat := 4983230072969 + 3 ^ 40 * 5967333 * 2
def baseEnd_5967333 : Nat := 1021370018145402171964747

theorem tailTrace_5967333 : CollatzResearch.WordTrace tailWord_5967333 prefixEnd_5967333 1021370018145402171964747 := by
  unfold tailWord_5967333
  simp only [CollatzResearch.WordTrace]
  refine ⟨217646514890379155183682653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145097676593586103455788435 217646514890379155183682653)
  ·
    refine ⟨81617443083892183193880995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217646514890379155183682653 81617443083892183193880995)
    ·
      refine ⟨122426164625838274790821493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81617443083892183193880995 122426164625838274790821493)
      ·
        refine ⟨11477452933672338261639515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122426164625838274790821493 11477452933672338261639515)
        ·
          refine ⟨17216179400508507392459273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11477452933672338261639515 17216179400508507392459273)
          ·
            refine ⟨12912134550381380544344455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17216179400508507392459273 12912134550381380544344455)
            ·
              refine ⟨19368201825572070816516683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12912134550381380544344455 19368201825572070816516683)
              ·
                refine ⟨29052302738358106224775025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19368201825572070816516683 29052302738358106224775025)
                ·
                  refine ⟨21789227053768579668581269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29052302738358106224775025 21789227053768579668581269)
                  ·
                    refine ⟨1021370018145402171964747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21789227053768579668581269 1021370018145402171964747)
                    ·
                      rfl

theorem cell23_5967333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_5967333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967333 prefixEnd_5967333 := by exact prefixLift 5967333
  have htrace : WordTrace (prefixWord ++ tailWord_5967333) baseStart_5967333 baseEnd_5967333 := by
    simpa [prefixWord, tailWord_5967333, baseEnd_5967333] using wordTrace_append hprefix tailTrace_5967333
  have hstable : (prefixWord ++ tailWord_5967333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967333).length < 2 ^ (prefixWord ++ tailWord_5967333).sum := by decide
  have hdescent : baseEnd_5967333 < baseStart_5967333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967361 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_5967361 : Nat := 118140960795 + 5967361 * 2 ^ 59
def prefixEnd_5967361 : Nat := 4983230072969 + 3 ^ 40 * 5967361 * 2
def baseEnd_5967361 : Nat := 3064124431894532406344113

theorem tailTrace_5967361 : CollatzResearch.WordTrace tailWord_5967361 prefixEnd_5967361 3064124431894532406344113 := by
  unfold tailWord_5967361
  simp only [CollatzResearch.WordTrace]
  refine ⟨217647536134277715965701937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145098357422851810643801291 217647536134277715965701937)
  ·
    refine ⟨163235652100708286974276453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217647536134277715965701937 163235652100708286974276453)
    ·
      refine ⟨30606684768882803807676835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 163235652100708286974276453 30606684768882803807676835)
      ·
        refine ⟨45910027153324205711515253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30606684768882803807676835 45910027153324205711515253)
        ·
          refine ⟨4304065045624144285454555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45910027153324205711515253 4304065045624144285454555)
          ·
            refine ⟨6456097568436216428181833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304065045624144285454555 6456097568436216428181833)
            ·
              refine ⟨4842073176327162321136375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6456097568436216428181833 4842073176327162321136375)
              ·
                refine ⟨7263109764490743481704563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842073176327162321136375 7263109764490743481704563)
                ·
                  refine ⟨10894664646736115222556845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7263109764490743481704563 10894664646736115222556845)
                  ·
                    refine ⟨4085499242526043208458817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10894664646736115222556845 4085499242526043208458817)
                    ·
                      refine ⟨3064124431894532406344113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085499242526043208458817 3064124431894532406344113)
                      ·
                        rfl

theorem cell23_5967361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_5967361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967361 prefixEnd_5967361 := by exact prefixLift 5967361
  have htrace : WordTrace (prefixWord ++ tailWord_5967361) baseStart_5967361 baseEnd_5967361 := by
    simpa [prefixWord, tailWord_5967361, baseEnd_5967361] using wordTrace_append hprefix tailTrace_5967361
  have hstable : (prefixWord ++ tailWord_5967361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967361).length < 2 ^ (prefixWord ++ tailWord_5967361).sum := by decide
  have hdescent : baseEnd_5967361 < baseStart_5967361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967386 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_5967386 : Nat := 118140960795 + 5967386 * 2 ^ 59
def prefixEnd_5967386 : Nat := 4983230072969 + 3 ^ 40 * 5967386 * 2
def baseEnd_5967386 : Nat := 3064137268910894808531497

theorem tailTrace_5967386 : CollatzResearch.WordTrace tailWord_5967386 prefixEnd_5967386 3064137268910894808531497 := by
  unfold tailWord_5967386
  simp only [CollatzResearch.WordTrace]
  refine ⟨54412111989796786308840503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145098965306124763490241341 54412111989796786308840503)
  ·
    refine ⟨81618167984695179463260755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54412111989796786308840503 81618167984695179463260755)
    ·
      refine ⟨122427251977042769194891133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81618167984695179463260755 122427251977042769194891133)
      ·
        refine ⟨45910219491391038448084175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122427251977042769194891133 45910219491391038448084175)
        ·
          refine ⟨68865329237086557672126263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45910219491391038448084175 68865329237086557672126263)
          ·
            refine ⟨103297993855629836508189395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68865329237086557672126263 103297993855629836508189395)
            ·
              refine ⟨154946990783444754762284093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103297993855629836508189395 154946990783444754762284093)
              ·
                refine ⟨58105121543791783035856535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154946990783444754762284093 58105121543791783035856535)
                ·
                  refine ⟨87157682315687674553784803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58105121543791783035856535 87157682315687674553784803)
                  ·
                    refine ⟨130736523473531511830677205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87157682315687674553784803 130736523473531511830677205)
                    ·
                      refine ⟨3064137268910894808531497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130736523473531511830677205 3064137268910894808531497)
                      ·
                        rfl

theorem cell23_5967386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_5967386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967386 prefixEnd_5967386 := by exact prefixLift 5967386
  have htrace : WordTrace (prefixWord ++ tailWord_5967386) baseStart_5967386 baseEnd_5967386 := by
    simpa [prefixWord, tailWord_5967386, baseEnd_5967386] using wordTrace_append hprefix tailTrace_5967386
  have hstable : (prefixWord ++ tailWord_5967386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967386).length < 2 ^ (prefixWord ++ tailWord_5967386).sum := by decide
  have hdescent : baseEnd_5967386 < baseStart_5967386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967413 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_5967413 : Nat := 118140960795 + 5967413 * 2 ^ 59
def prefixEnd_5967413 : Nat := 4983230072969 + 3 ^ 40 * 5967413 * 2
def baseEnd_5967413 : Nat := 3064151132888566202893873

theorem tailTrace_5967413 : CollatzResearch.WordTrace tailWord_5967413 prefixEnd_5967413 3064151132888566202893873 := by
  unfold tailWord_5967413
  simp only [CollatzResearch.WordTrace]
  refine ⟨217649432730089328846594893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145099621820059552564396595 217649432730089328846594893)
  ·
    refine ⟨81618537273783498317473085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217649432730089328846594893 81618537273783498317473085)
    ·
      refine ⟨30606951477668811869052407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81618537273783498317473085 30606951477668811869052407)
      ·
        refine ⟨45910427216503217803578611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30606951477668811869052407 45910427216503217803578611)
        ·
          refine ⟨68865640824754826705367917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45910427216503217803578611 68865640824754826705367917)
          ·
            refine ⟨25824615309283060014512969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68865640824754826705367917 25824615309283060014512969)
            ·
              refine ⟨19368461481962295010884727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25824615309283060014512969 19368461481962295010884727)
              ·
                refine ⟨29052692222943442516327091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19368461481962295010884727 29052692222943442516327091)
                ·
                  refine ⟨43579038334415163774490637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29052692222943442516327091 43579038334415163774490637)
                  ·
                    refine ⟨16342139375405686415433989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43579038334415163774490637 16342139375405686415433989)
                    ·
                      refine ⟨3064151132888566202893873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16342139375405686415433989 3064151132888566202893873)
                      ·
                        rfl

theorem cell23_5967413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_5967413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967413 prefixEnd_5967413 := by exact prefixLift 5967413
  have htrace : WordTrace (prefixWord ++ tailWord_5967413) baseStart_5967413 baseEnd_5967413 := by
    simpa [prefixWord, tailWord_5967413, baseEnd_5967413] using wordTrace_append hprefix tailTrace_5967413
  have hstable : (prefixWord ++ tailWord_5967413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967413).length < 2 ^ (prefixWord ++ tailWord_5967413).sum := by decide
  have hdescent : baseEnd_5967413 < baseStart_5967413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967414 : List Nat := [5, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_5967414 : Nat := 118140960795 + 5967414 * 2 ^ 59
def prefixEnd_5967414 : Nat := 4983230072969 + 3 ^ 40 * 5967414 * 2
def baseEnd_5967414 : Nat := 340461294041024522109041

theorem tailTrace_5967414 : CollatzResearch.WordTrace tailWord_5967414 prefixEnd_5967414 340461294041024522109041 := by
  unfold tailWord_5967414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13603091825192856626086331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145099646135390470678254197 13603091825192856626086331)
  ·
    refine ⟨20404637737789284939129497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13603091825192856626086331 20404637737789284939129497)
    ·
      refine ⟨15303478303341963704347123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20404637737789284939129497 15303478303341963704347123)
      ·
        refine ⟨22955217455012945556520685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15303478303341963704347123 22955217455012945556520685)
        ·
          refine ⟨8608206545629854583695257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22955217455012945556520685 8608206545629854583695257)
          ·
            refine ⟨6456154909222390937771443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8608206545629854583695257 6456154909222390937771443)
            ·
              refine ⟨9684232363833586406657165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456154909222390937771443 9684232363833586406657165)
              ·
                refine ⟨3631587136437594902496437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9684232363833586406657165 3631587136437594902496437)
                ·
                  refine ⟨340461294041024522109041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3631587136437594902496437 340461294041024522109041)
                  ·
                    rfl

theorem cell23_5967414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_5967414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967414 prefixEnd_5967414 := by exact prefixLift 5967414
  have htrace : WordTrace (prefixWord ++ tailWord_5967414) baseStart_5967414 baseEnd_5967414 := by
    simpa [prefixWord, tailWord_5967414, baseEnd_5967414] using wordTrace_append hprefix tailTrace_5967414
  have hstable : (prefixWord ++ tailWord_5967414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967414).length < 2 ^ (prefixWord ++ tailWord_5967414).sum := by decide
  have hdescent : baseEnd_5967414 < baseStart_5967414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967463 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_5967463 : Nat := 118140960795 + 5967463 * 2 ^ 59
def prefixEnd_5967463 : Nat := 4983230072969 + 3 ^ 40 * 5967463 * 2
def baseEnd_5967463 : Nat := 3064176806921291007268643

theorem tailTrace_5967463 : CollatzResearch.WordTrace tailWord_5967463 prefixEnd_5967463 3064176806921291007268643 := by
  unfold tailWord_5967463
  simp only [CollatzResearch.WordTrace]
  refine ⟨217651256379908187385915043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145100837586605458257276695 217651256379908187385915043)
  ·
    refine ⟨326476884569862281078872565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217651256379908187385915043 326476884569862281078872565)
    ·
      refine ⟨30607207928424588851144303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 326476884569862281078872565 30607207928424588851144303)
      ·
        refine ⟨45910811892636883276716455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30607207928424588851144303 45910811892636883276716455)
        ·
          refine ⟨68866217838955324915074683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45910811892636883276716455 68866217838955324915074683)
          ·
            refine ⟨103299326758432987372612025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68866217838955324915074683 103299326758432987372612025)
            ·
              refine ⟨77474495068824740529459019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103299326758432987372612025 77474495068824740529459019)
              ·
                refine ⟨116211742603237110794188529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77474495068824740529459019 116211742603237110794188529)
                ·
                  refine ⟨87158806952427833095641397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116211742603237110794188529 87158806952427833095641397)
                  ·
                    refine ⟨8171138151790109352716381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87158806952427833095641397 8171138151790109352716381)
                    ·
                      refine ⟨3064176806921291007268643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8171138151790109352716381 3064176806921291007268643)
                      ·
                        rfl

theorem cell23_5967463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_5967463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967463 prefixEnd_5967463 := by exact prefixLift 5967463
  have htrace : WordTrace (prefixWord ++ tailWord_5967463) baseStart_5967463 baseEnd_5967463 := by
    simpa [prefixWord, tailWord_5967463, baseEnd_5967463] using wordTrace_append hprefix tailTrace_5967463
  have hstable : (prefixWord ++ tailWord_5967463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967463).length < 2 ^ (prefixWord ++ tailWord_5967463).sum := by decide
  have hdescent : baseEnd_5967463 < baseStart_5967463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967520 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_5967520 : Nat := 118140960795 + 5967520 * 2 ^ 59
def prefixEnd_5967520 : Nat := 4983230072969 + 3 ^ 40 * 5967520 * 2
def baseEnd_5967520 : Nat := 3064206075318597284255881

theorem tailTrace_5967520 : CollatzResearch.WordTrace tailWord_5967520 prefixEnd_5967520 3064206075318597284255881 := by
  unfold tailWord_5967520
  simp only [CollatzResearch.WordTrace]
  refine ⟨108826667670350843060370007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145102223560467790747160009 108826667670350843060370007)
  ·
    refine ⟨163240001505526264590555011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108826667670350843060370007 163240001505526264590555011)
    ·
      refine ⟨244860002258289396885832517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163240001505526264590555011 244860002258289396885832517)
      ·
        refine ⟨45911250423429261916093597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244860002258289396885832517 45911250423429261916093597)
        ·
          refine ⟨17216718908785973218535099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45911250423429261916093597 17216718908785973218535099)
          ·
            refine ⟨25825078363178959827802649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17216718908785973218535099 25825078363178959827802649)
            ·
              refine ⟨19368808772384219870851987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25825078363178959827802649 19368808772384219870851987)
              ·
                refine ⟨29053213158576329806277981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19368808772384219870851987 29053213158576329806277981)
                ·
                  refine ⟨10894954934466123677354243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29053213158576329806277981 10894954934466123677354243)
                  ·
                    refine ⟨16342432401699185516031365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10894954934466123677354243 16342432401699185516031365)
                    ·
                      refine ⟨3064206075318597284255881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16342432401699185516031365 3064206075318597284255881)
                      ·
                        rfl

theorem cell23_5967520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_5967520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967520 prefixEnd_5967520 := by exact prefixLift 5967520
  have htrace : WordTrace (prefixWord ++ tailWord_5967520) baseStart_5967520 baseEnd_5967520 := by
    simpa [prefixWord, tailWord_5967520, baseEnd_5967520] using wordTrace_append hprefix tailTrace_5967520
  have hstable : (prefixWord ++ tailWord_5967520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967520).length < 2 ^ (prefixWord ++ tailWord_5967520).sum := by decide
  have hdescent : baseEnd_5967520 < baseStart_5967520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967524 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_5967524 : Nat := 118140960795 + 5967524 * 2 ^ 59
def prefixEnd_5967524 : Nat := 4983230072969 + 3 ^ 40 * 5967524 * 2
def baseEnd_5967524 : Nat := 3064208129241215268605863

theorem tailTrace_5967524 : CollatzResearch.WordTrace tailWord_5967524 prefixEnd_5967524 3064208129241215268605863 := by
  unfold tailWord_5967524
  simp only [CollatzResearch.WordTrace]
  refine ⟨108826740616343597401942813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145102320821791463202590417 108826740616343597401942813)
  ·
    refine ⟨40810027731128849025728555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108826740616343597401942813 40810027731128849025728555)
    ·
      refine ⟨61215041596693273538592833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40810027731128849025728555 61215041596693273538592833)
      ·
        refine ⟨45911281197519955153944625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61215041596693273538592833 45911281197519955153944625)
        ·
          refine ⟨34433460898139966365458469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45911281197519955153944625 34433460898139966365458469)
          ·
            refine ⟨6456273918401243693523463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34433460898139966365458469 6456273918401243693523463)
            ·
              refine ⟨9684410877601865540285195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456273918401243693523463 9684410877601865540285195)
              ·
                refine ⟨14526616316402798310427793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684410877601865540285195 14526616316402798310427793)
                ·
                  refine ⟨10894962237302098732820845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14526616316402798310427793 10894962237302098732820845)
                  ·
                    refine ⟨4085610838988287024807817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10894962237302098732820845 4085610838988287024807817)
                    ·
                      refine ⟨3064208129241215268605863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085610838988287024807817 3064208129241215268605863)
                      ·
                        rfl

theorem cell23_5967524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_5967524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967524 prefixEnd_5967524 := by exact prefixLift 5967524
  have htrace : WordTrace (prefixWord ++ tailWord_5967524) baseStart_5967524 baseEnd_5967524 := by
    simpa [prefixWord, tailWord_5967524, baseEnd_5967524] using wordTrace_append hprefix tailTrace_5967524
  have hstable : (prefixWord ++ tailWord_5967524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967524).length < 2 ^ (prefixWord ++ tailWord_5967524).sum := by decide
  have hdescent : baseEnd_5967524 < baseStart_5967524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967534 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_5967534 : Nat := 118140960795 + 5967534 * 2 ^ 59
def prefixEnd_5967534 : Nat := 4983230072969 + 3 ^ 40 * 5967534 * 2
def baseEnd_5967534 : Nat := 1021404421349253409826939

theorem tailTrace_5967534 : CollatzResearch.WordTrace tailWord_5967534 prefixEnd_5967534 1021404421349253409826939 := by
  unfold tailWord_5967534
  simp only [CollatzResearch.WordTrace]
  refine ⟨27206730745331370813968707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145102563975100644341166437 27206730745331370813968707)
  ·
    refine ⟨40810096117997056220953061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27206730745331370813968707 40810096117997056220953061)
    ·
      refine ⟨7651893022124448041428699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40810096117997056220953061 7651893022124448041428699)
      ·
        refine ⟨11477839533186672062143049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7651893022124448041428699 11477839533186672062143049)
        ·
          refine ⟨8608379649890004046607287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11477839533186672062143049 8608379649890004046607287)
          ·
            refine ⟨12912569474835006069910931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8608379649890004046607287 12912569474835006069910931)
            ·
              refine ⟨19368854212252509104866397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12912569474835006069910931 19368854212252509104866397)
              ·
                refine ⟨7263320329594690914324899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19368854212252509104866397 7263320329594690914324899)
                ·
                  refine ⟨10894980494392036371487349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7263320329594690914324899 10894980494392036371487349)
                  ·
                    refine ⟨1021404421349253409826939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10894980494392036371487349 1021404421349253409826939)
                    ·
                      rfl

theorem cell23_5967534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_5967534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967534 prefixEnd_5967534 := by exact prefixLift 5967534
  have htrace : WordTrace (prefixWord ++ tailWord_5967534) baseStart_5967534 baseEnd_5967534 := by
    simpa [prefixWord, tailWord_5967534, baseEnd_5967534] using wordTrace_append hprefix tailTrace_5967534
  have hstable : (prefixWord ++ tailWord_5967534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967534).length < 2 ^ (prefixWord ++ tailWord_5967534).sum := by decide
  have hdescent : baseEnd_5967534 < baseStart_5967534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967543 : List Nat := [1, 1, 3, 1, 5, 2, 10]
def baseStart_5967543 : Nat := 118140960795 + 5967543 * 2 ^ 59
def prefixEnd_5967543 : Nat := 4983230072969 + 3 ^ 40 * 5967543 * 2
def baseEnd_5967543 : Nat := 37829850436711736966275

theorem tailTrace_5967543 : CollatzResearch.WordTrace tailWord_5967543 prefixEnd_5967543 37829850436711736966275 := by
  unfold tailWord_5967543
  simp only [CollatzResearch.WordTrace]
  refine ⟨217654174219618361048827283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145102782813078907365884855 217654174219618361048827283)
  ·
    refine ⟨326481261329427541573240925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217654174219618361048827283 326481261329427541573240925)
    ·
      refine ⟨122430472998535328089965347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326481261329427541573240925 122430472998535328089965347)
      ·
        refine ⟨183645709497802992134948021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122430472998535328089965347 183645709497802992134948021)
        ·
          refine ⟨17216785265419030512651377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183645709497802992134948021 17216785265419030512651377)
          ·
            refine ⟨12912588949064272884488533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17216785265419030512651377 12912588949064272884488533)
            ·
              refine ⟨37829850436711736966275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12912588949064272884488533 37829850436711736966275)
              ·
                rfl

theorem cell23_5967543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 10].length) (baseStart_5967543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967543 prefixEnd_5967543 := by exact prefixLift 5967543
  have htrace : WordTrace (prefixWord ++ tailWord_5967543) baseStart_5967543 baseEnd_5967543 := by
    simpa [prefixWord, tailWord_5967543, baseEnd_5967543] using wordTrace_append hprefix tailTrace_5967543
  have hstable : (prefixWord ++ tailWord_5967543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967543).length < 2 ^ (prefixWord ++ tailWord_5967543).sum := by decide
  have hdescent : baseEnd_5967543 < baseStart_5967543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967564 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_5967564 : Nat := 118140960795 + 5967564 * 2 ^ 59
def prefixEnd_5967564 : Nat := 4983230072969 + 3 ^ 40 * 5967564 * 2
def baseEnd_5967564 : Nat := 1021409556155798370701893

theorem tailTrace_5967564 : CollatzResearch.WordTrace tailWord_5967564 prefixEnd_5967564 1021409556155798370701893 := by
  unfold tailWord_5967564
  simp only [CollatzResearch.WordTrace]
  refine ⟨108827470076271140817670873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145103293435028187756894497 108827470076271140817670873)
  ·
    refine ⟨81620602557203355613253155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108827470076271140817670873 81620602557203355613253155)
    ·
      refine ⟨122430903835805033419879733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81620602557203355613253155 122430903835805033419879733)
      ·
        refine ⟨11477897234606721883113725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122430903835805033419879733 11477897234606721883113725)
        ·
          refine ⟨4304211462977520706167647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11477897234606721883113725 4304211462977520706167647)
          ·
            refine ⟨6456317194466281059251471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304211462977520706167647 6456317194466281059251471)
            ·
              refine ⟨9684475791699421588877207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456317194466281059251471 9684475791699421588877207)
              ·
                refine ⟨14526713687549132383315811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684475791699421588877207 14526713687549132383315811)
                ·
                  refine ⟨21790070531323698574973717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14526713687549132383315811 21790070531323698574973717)
                  ·
                    refine ⟨1021409556155798370701893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21790070531323698574973717 1021409556155798370701893)
                    ·
                      rfl

theorem cell23_5967564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_5967564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967564 prefixEnd_5967564 := by exact prefixLift 5967564
  have htrace : WordTrace (prefixWord ++ tailWord_5967564) baseStart_5967564 baseEnd_5967564 := by
    simpa [prefixWord, tailWord_5967564, baseEnd_5967564] using wordTrace_append hprefix tailTrace_5967564
  have hstable : (prefixWord ++ tailWord_5967564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967564).length < 2 ^ (prefixWord ++ tailWord_5967564).sum := by decide
  have hdescent : baseEnd_5967564 < baseStart_5967564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967583 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_5967583 : Nat := 118140960795 + 5967583 * 2 ^ 59
def prefixEnd_5967583 : Nat := 4983230072969 + 3 ^ 40 * 5967583 * 2
def baseEnd_5967583 : Nat := 3064238424599830537768091

theorem tailTrace_5967583 : CollatzResearch.WordTrace tailWord_5967583 prefixEnd_5967583 3064238424599830537768091 := by
  unfold tailWord_5967583
  simp only [CollatzResearch.WordTrace]
  refine ⟨217655633139473447880283403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145103755426315631920188935 217655633139473447880283403)
  ·
    refine ⟨326483449709210171820425105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217655633139473447880283403 326483449709210171820425105)
    ·
      refine ⟨244862587281907628865318829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326483449709210171820425105 244862587281907628865318829)
      ·
        refine ⟨91823470230715360824494561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244862587281907628865318829 91823470230715360824494561)
        ·
          refine ⟨68867602673036520618370921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91823470230715360824494561 68867602673036520618370921)
          ·
            refine ⟨51650702004777390463778191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68867602673036520618370921 51650702004777390463778191)
            ·
              refine ⟨77476053007166085695667287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51650702004777390463778191 77476053007166085695667287)
              ·
                refine ⟨116214079510749128543500931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77476053007166085695667287 116214079510749128543500931)
                ·
                  refine ⟨174321119266123692815251397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116214079510749128543500931 174321119266123692815251397)
                  ·
                    refine ⟨32685209862398192402859637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174321119266123692815251397 32685209862398192402859637)
                    ·
                      refine ⟨3064238424599830537768091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32685209862398192402859637 3064238424599830537768091)
                      ·
                        rfl

theorem cell23_5967583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_5967583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967583 prefixEnd_5967583 := by exact prefixLift 5967583
  have htrace : WordTrace (prefixWord ++ tailWord_5967583) baseStart_5967583 baseEnd_5967583 := by
    simpa [prefixWord, tailWord_5967583, baseEnd_5967583] using wordTrace_append hprefix tailTrace_5967583
  have hstable : (prefixWord ++ tailWord_5967583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967583).length < 2 ^ (prefixWord ++ tailWord_5967583).sum := by decide
  have hdescent : baseEnd_5967583 < baseStart_5967583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967593 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_5967593 : Nat := 118140960795 + 5967593 * 2 ^ 59
def prefixEnd_5967593 : Nat := 4983230072969 + 3 ^ 40 * 5967593 * 2
def baseEnd_5967593 : Nat := 3064243559406375498643045

theorem tailTrace_5967593 : CollatzResearch.WordTrace tailWord_5967593 prefixEnd_5967593 3064243559406375498643045 := by
  unfold tailWord_5967593
  simp only [CollatzResearch.WordTrace]
  refine ⟨217655997869437219588147433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145103998579624813058764955 217655997869437219588147433)
  ·
    refine ⟨163241998402077914691110575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217655997869437219588147433 163241998402077914691110575)
    ·
      refine ⟨244862997603116872036665863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163241998402077914691110575 244862997603116872036665863)
      ·
        refine ⟨367294496404675308054998795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244862997603116872036665863 367294496404675308054998795)
        ·
          refine ⟨550941744607012962082498193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367294496404675308054998795 550941744607012962082498193)
          ·
            refine ⟨413206308455259721561873645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550941744607012962082498193 413206308455259721561873645)
            ·
              refine ⟨154952365670722395585702617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413206308455259721561873645 154952365670722395585702617)
              ·
                refine ⟨116214274253041796689276963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154952365670722395585702617 116214274253041796689276963)
                ·
                  refine ⟨174321411379562695033915445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116214274253041796689276963 174321411379562695033915445)
                  ·
                    refine ⟨16342632316834002659429573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174321411379562695033915445 16342632316834002659429573)
                    ·
                      refine ⟨3064243559406375498643045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16342632316834002659429573 3064243559406375498643045)
                      ·
                        rfl

theorem cell23_5967593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_5967593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967593 prefixEnd_5967593 := by exact prefixLift 5967593
  have htrace : WordTrace (prefixWord ++ tailWord_5967593) baseStart_5967593 baseEnd_5967593 := by
    simpa [prefixWord, tailWord_5967593, baseEnd_5967593] using wordTrace_append hprefix tailTrace_5967593
  have hstable : (prefixWord ++ tailWord_5967593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967593).length < 2 ^ (prefixWord ++ tailWord_5967593).sum := by decide
  have hdescent : baseEnd_5967593 < baseStart_5967593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967603 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 4, 6]
def baseStart_5967603 : Nat := 118140960795 + 5967603 * 2 ^ 59
def prefixEnd_5967603 : Nat := 4983230072969 + 3 ^ 40 * 5967603 * 2
def baseEnd_5967603 : Nat := 1021416231404306819839333

theorem tailTrace_5967603 : CollatzResearch.WordTrace tailWord_5967603 prefixEnd_5967603 1021416231404306819839333 := by
  unfold tailWord_5967603
  simp only [CollatzResearch.WordTrace]
  refine ⟨217656362599400991296011463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145104241732933994197340975 217656362599400991296011463)
  ·
    refine ⟨326484543899101486944017195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217656362599400991296011463 326484543899101486944017195)
    ·
      refine ⟨489726815848652230416025793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326484543899101486944017195 489726815848652230416025793)
      ·
        refine ⟨367295111886489172812019345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489726815848652230416025793 367295111886489172812019345)
        ·
          refine ⟨275471333914866879609014509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367295111886489172812019345 275471333914866879609014509)
          ·
            refine ⟨103301750218075079853380441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275471333914866879609014509 103301750218075079853380441)
            ·
              refine ⟨77476312663556309890035331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103301750218075079853380441 77476312663556309890035331)
              ·
                refine ⟨116214468995334464835052997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77476312663556309890035331 116214468995334464835052997)
                ·
                  refine ⟨21790212936625212156572437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116214468995334464835052997 21790212936625212156572437)
                  ·
                    refine ⟨1021416231404306819839333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21790212936625212156572437 1021416231404306819839333)
                    ·
                      rfl

theorem cell23_5967603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 6].length) (baseStart_5967603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967603 prefixEnd_5967603 := by exact prefixLift 5967603
  have htrace : WordTrace (prefixWord ++ tailWord_5967603) baseStart_5967603 baseEnd_5967603 := by
    simpa [prefixWord, tailWord_5967603, baseEnd_5967603] using wordTrace_append hprefix tailTrace_5967603
  have hstable : (prefixWord ++ tailWord_5967603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967603).length < 2 ^ (prefixWord ++ tailWord_5967603).sum := by decide
  have hdescent : baseEnd_5967603 < baseStart_5967603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967622 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5967622 : Nat := 118140960795 + 5967622 * 2 ^ 59
def prefixEnd_5967622 : Nat := 4983230072969 + 3 ^ 40 * 5967622 * 2
def baseEnd_5967622 : Nat := 3064258450345355885180413

theorem tailTrace_5967622 : CollatzResearch.WordTrace tailWord_5967622 prefixEnd_5967622 3064258450345355885180413 := by
  unfold tailWord_5967622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6801782987072879923154785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 145104703724221438360635413 6801782987072879923154785)
  ·
    refine ⟨5101337240304659942366089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6801782987072879923154785 5101337240304659942366089)
    ·
      refine ⟨3826002930228494956774567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5101337240304659942366089 3826002930228494956774567)
      ·
        refine ⟨5739004395342742435161851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3826002930228494956774567 5739004395342742435161851)
        ·
          refine ⟨8608506593014113652742777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739004395342742435161851 8608506593014113652742777)
          ·
            refine ⟨6456379944760585239557083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8608506593014113652742777 6456379944760585239557083)
            ·
              refine ⟨9684569917140877859335625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456379944760585239557083 9684569917140877859335625)
              ·
                refine ⟨7263427437855658394501719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9684569917140877859335625 7263427437855658394501719)
                ·
                  refine ⟨10895141156783487591752579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7263427437855658394501719 10895141156783487591752579)
                  ·
                    refine ⟨16342711735175231387628869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10895141156783487591752579 16342711735175231387628869)
                    ·
                      refine ⟨3064258450345355885180413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16342711735175231387628869 3064258450345355885180413)
                      ·
                        rfl

theorem cell23_5967622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5967622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967622 prefixEnd_5967622 := by exact prefixLift 5967622
  have htrace : WordTrace (prefixWord ++ tailWord_5967622) baseStart_5967622 baseEnd_5967622 := by
    simpa [prefixWord, tailWord_5967622, baseEnd_5967622] using wordTrace_append hprefix tailTrace_5967622
  have hstable : (prefixWord ++ tailWord_5967622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967622).length < 2 ^ (prefixWord ++ tailWord_5967622).sum := by decide
  have hdescent : baseEnd_5967622 < baseStart_5967622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967630 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5967630 : Nat := 118140960795 + 5967630 * 2 ^ 59
def prefixEnd_5967630 : Nat := 4983230072969 + 3 ^ 40 * 5967630 * 2
def baseEnd_5967630 : Nat := 3064262558190591853880375

theorem tailTrace_5967630 : CollatzResearch.WordTrace tailWord_5967630 prefixEnd_5967630 3064262558190591853880375 := by
  unfold tailWord_5967630
  simp only [CollatzResearch.WordTrace]
  refine ⟨27207168421287896863405543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145104898246868783271496229 27207168421287896863405543)
  ·
    refine ⟨40810752631931845295108315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27207168421287896863405543 40810752631931845295108315)
    ·
      refine ⟨61216128947897767942662473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40810752631931845295108315 61216128947897767942662473)
      ·
        refine ⟨45912096710923325956996855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61216128947897767942662473 45912096710923325956996855)
        ·
          refine ⟨68868145066384988935495283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45912096710923325956996855 68868145066384988935495283)
          ·
            refine ⟨103302217599577483403242925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68868145066384988935495283 103302217599577483403242925)
            ·
              refine ⟨38738331599841556276216097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103302217599577483403242925 38738331599841556276216097)
              ·
                refine ⟨29053748699881167207162073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38738331599841556276216097 29053748699881167207162073)
                ·
                  refine ⟨21790311524910875405371555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29053748699881167207162073 21790311524910875405371555)
                  ·
                    refine ⟨32685467287366313108057333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21790311524910875405371555 32685467287366313108057333)
                    ·
                      refine ⟨3064262558190591853880375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32685467287366313108057333 3064262558190591853880375)
                      ·
                        rfl

theorem cell23_5967630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5967630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967630 prefixEnd_5967630 := by exact prefixLift 5967630
  have htrace : WordTrace (prefixWord ++ tailWord_5967630) baseStart_5967630 baseEnd_5967630 := by
    simpa [prefixWord, tailWord_5967630, baseEnd_5967630] using wordTrace_append hprefix tailTrace_5967630
  have hstable : (prefixWord ++ tailWord_5967630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967630).length < 2 ^ (prefixWord ++ tailWord_5967630).sum := by decide
  have hdescent : baseEnd_5967630 < baseStart_5967630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967633 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 9]
def baseStart_5967633 : Nat := 118140960795 + 5967633 * 2 ^ 59
def prefixEnd_5967633 : Nat := 4983230072969 + 3 ^ 40 * 5967633 * 2
def baseEnd_5967633 : Nat := 340473788736950593571429

theorem tailTrace_5967633 : CollatzResearch.WordTrace tailWord_5967633 prefixEnd_5967633 340473788736950593571429 := by
  unfold tailWord_5967633
  simp only [CollatzResearch.WordTrace]
  refine ⟨217657456789292306419603553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145104971192861537613069035 217657456789292306419603553)
  ·
    refine ⟨163243092591969229814702665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217657456789292306419603553 163243092591969229814702665)
    ·
      refine ⟨122432319443976922361026999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163243092591969229814702665 122432319443976922361026999)
      ·
        refine ⟨183648479165965383541540499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122432319443976922361026999 183648479165965383541540499)
        ·
          refine ⟨275472718748948075312310749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183648479165965383541540499 275472718748948075312310749)
          ·
            refine ⟨103302269530855528242116531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275472718748948075312310749 103302269530855528242116531)
            ·
              refine ⟨154953404296283292363174797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103302269530855528242116531 154953404296283292363174797)
              ·
                refine ⟨58107526611106234636190549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154953404296283292363174797 58107526611106234636190549)
                ·
                  refine ⟨340473788736950593571429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58107526611106234636190549 340473788736950593571429)
                  ·
                    rfl

theorem cell23_5967633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 9].length) (baseStart_5967633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967633 prefixEnd_5967633 := by exact prefixLift 5967633
  have htrace : WordTrace (prefixWord ++ tailWord_5967633) baseStart_5967633 baseEnd_5967633 := by
    simpa [prefixWord, tailWord_5967633, baseEnd_5967633] using wordTrace_append hprefix tailTrace_5967633
  have hstable : (prefixWord ++ tailWord_5967633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967633).length < 2 ^ (prefixWord ++ tailWord_5967633).sum := by decide
  have hdescent : baseEnd_5967633 < baseStart_5967633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967677 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_5967677 : Nat := 118140960795 + 5967677 * 2 ^ 59
def prefixEnd_5967677 : Nat := 4983230072969 + 3 ^ 40 * 5967677 * 2
def baseEnd_5967677 : Nat := 3064286691781353169992659

theorem tailTrace_5967677 : CollatzResearch.WordTrace tailWord_5967677 prefixEnd_5967677 3064286691781353169992659 := by
  unfold tailWord_5967677
  simp only [CollatzResearch.WordTrace]
  refine ⟨217659061601132901934205285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145106041067421934622803523 217659061601132901934205285)
  ·
    refine ⟨40811074050212419112663491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 217659061601132901934205285 40811074050212419112663491)
    ·
      refine ⟨61216611075318628668995237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40811074050212419112663491 61216611075318628668995237)
      ·
        refine ⟨11478114576622242875436607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61216611075318628668995237 11478114576622242875436607)
        ·
          refine ⟨17217171864933364313154911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11478114576622242875436607 17217171864933364313154911)
          ·
            refine ⟨25825757797400046469732367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17217171864933364313154911 25825757797400046469732367)
            ·
              refine ⟨38738636696100069704598551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25825757797400046469732367 38738636696100069704598551)
              ·
                refine ⟨58107955044150104556897827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38738636696100069704598551 58107955044150104556897827)
                ·
                  refine ⟨87161932566225156835346741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58107955044150104556897827 87161932566225156835346741)
                  ·
                    refine ⟨8171431178083608453313757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87161932566225156835346741 8171431178083608453313757)
                    ·
                      refine ⟨3064286691781353169992659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8171431178083608453313757 3064286691781353169992659)
                      ·
                        rfl

theorem cell23_5967677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_5967677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967677 prefixEnd_5967677 := by exact prefixLift 5967677
  have htrace : WordTrace (prefixWord ++ tailWord_5967677) baseStart_5967677 baseEnd_5967677 := by
    simpa [prefixWord, tailWord_5967677, baseEnd_5967677] using wordTrace_append hprefix tailTrace_5967677
  have hstable : (prefixWord ++ tailWord_5967677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967677).length < 2 ^ (prefixWord ++ tailWord_5967677).sum := by decide
  have hdescent : baseEnd_5967677 < baseStart_5967677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967697 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 2, 5]
def baseStart_5967697 : Nat := 118140960795 + 5967697 * 2 ^ 59
def prefixEnd_5967697 : Nat := 4983230072969 + 3 ^ 40 * 5967697 * 2
def baseEnd_5967697 : Nat := 1021432320464814363914189

theorem tailTrace_5967697 : CollatzResearch.WordTrace tailWord_5967697 prefixEnd_5967697 1021432320464814363914189 := by
  unfold tailWord_5967697
  simp only [CollatzResearch.WordTrace]
  refine ⟨217659791061060445349933345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145106527374040296899955563 217659791061060445349933345)
  ·
    refine ⟨163244843295795334012450009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217659791061060445349933345 163244843295795334012450009)
    ·
      refine ⟨122433632471846500509337507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163244843295795334012450009 122433632471846500509337507)
      ·
        refine ⟨183650448707769750764006261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122433632471846500509337507 183650448707769750764006261)
        ·
          refine ⟨17217229566353414134125587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183650448707769750764006261 17217229566353414134125587)
          ·
            refine ⟨25825844349530121201188381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17217229566353414134125587 25825844349530121201188381)
            ·
              refine ⟨9684691631073795450445643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25825844349530121201188381 9684691631073795450445643)
              ·
                refine ⟨14527037446610693175668465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684691631073795450445643 14527037446610693175668465)
                ·
                  refine ⟨10895278084958019881751349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14527037446610693175668465 10895278084958019881751349)
                  ·
                    refine ⟨1021432320464814363914189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10895278084958019881751349 1021432320464814363914189)
                    ·
                      rfl

theorem cell23_5967697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_5967697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967697 prefixEnd_5967697 := by exact prefixLift 5967697
  have htrace : WordTrace (prefixWord ++ tailWord_5967697) baseStart_5967697 baseEnd_5967697 := by
    simpa [prefixWord, tailWord_5967697, baseEnd_5967697] using wordTrace_append hprefix tailTrace_5967697
  have hstable : (prefixWord ++ tailWord_5967697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967697).length < 2 ^ (prefixWord ++ tailWord_5967697).sum := by decide
  have hdescent : baseEnd_5967697 < baseStart_5967697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967730 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_5967730 : Nat := 118140960795 + 5967730 * 2 ^ 59
def prefixEnd_5967730 : Nat := 4983230072969 + 3 ^ 40 * 5967730 * 2
def baseEnd_5967730 : Nat := 3064313906256041462629915

theorem tailTrace_5967730 : CollatzResearch.WordTrace tailWord_5967730 prefixEnd_5967730 3064313906256041462629915 := by
  unfold tailWord_5967730
  simp only [CollatzResearch.WordTrace]
  refine ⟨54415248667485222996471161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145107329779960594657256429 54415248667485222996471161)
  ·
    refine ⟨40811436500613917247353371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54415248667485222996471161 40811436500613917247353371)
    ·
      refine ⟨61217154750920875871030057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40811436500613917247353371 61217154750920875871030057)
      ·
        refine ⟨45912866063190656903272543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61217154750920875871030057 45912866063190656903272543)
        ·
          refine ⟨68869299094785985354908815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45912866063190656903272543 68869299094785985354908815)
          ·
            refine ⟨103303948642178978032363223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68869299094785985354908815 103303948642178978032363223)
            ·
              refine ⟨154955922963268467048544835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103303948642178978032363223 154955922963268467048544835)
              ·
                refine ⟨232433884444902700572817253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154955922963268467048544835 232433884444902700572817253)
                ·
                  refine ⟨43581353333419256357403235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232433884444902700572817253 43581353333419256357403235)
                  ·
                    refine ⟨65372030000128884536104853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43581353333419256357403235 65372030000128884536104853)
                    ·
                      refine ⟨3064313906256041462629915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65372030000128884536104853 3064313906256041462629915)
                      ·
                        rfl

theorem cell23_5967730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_5967730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967730 prefixEnd_5967730 := by exact prefixLift 5967730
  have htrace : WordTrace (prefixWord ++ tailWord_5967730) baseStart_5967730 baseEnd_5967730 := by
    simpa [prefixWord, tailWord_5967730, baseEnd_5967730] using wordTrace_append hprefix tailTrace_5967730
  have hstable : (prefixWord ++ tailWord_5967730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967730).length < 2 ^ (prefixWord ++ tailWord_5967730).sum := by decide
  have hdescent : baseEnd_5967730 < baseStart_5967730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967778 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_5967778 : Nat := 118140960795 + 5967778 * 2 ^ 59
def prefixEnd_5967778 : Nat := 4983230072969 + 3 ^ 40 * 5967778 * 2
def baseEnd_5967778 : Nat := 1021446184442485758276565

theorem tailTrace_5967778 : CollatzResearch.WordTrace tailWord_5967778 prefixEnd_5967778 1021446184442485758276565 := by
  unfold tailWord_5967778
  simp only [CollatzResearch.WordTrace]
  refine ⟨54415686343441749045907997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145108496915844664122421325 54415686343441749045907997)
  ·
    refine ⟨20405882378790655892215499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54415686343441749045907997 20405882378790655892215499)
    ·
      refine ⟨30608823568185983838323249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20405882378790655892215499 30608823568185983838323249)
      ·
        refine ⟨22956617676139487878742437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30608823568185983838323249 22956617676139487878742437)
        ·
          refine ⟨4304365814276153977264207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22956617676139487878742437 4304365814276153977264207)
          ·
            refine ⟨6456548721414230965896311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304365814276153977264207 6456548721414230965896311)
            ·
              refine ⟨9684823082121346448844467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456548721414230965896311 9684823082121346448844467)
              ·
                refine ⟨14527234623182019673266701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684823082121346448844467 14527234623182019673266701)
                ·
                  refine ⟨5447712983693257377475013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14527234623182019673266701 5447712983693257377475013)
                  ·
                    refine ⟨1021446184442485758276565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5447712983693257377475013 1021446184442485758276565)
                    ·
                      rfl

theorem cell23_5967778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_5967778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967778 prefixEnd_5967778 := by exact prefixLift 5967778
  have htrace : WordTrace (prefixWord ++ tailWord_5967778) baseStart_5967778 baseEnd_5967778 := by
    simpa [prefixWord, tailWord_5967778, baseEnd_5967778] using wordTrace_append hprefix tailTrace_5967778
  have hstable : (prefixWord ++ tailWord_5967778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967778).length < 2 ^ (prefixWord ++ tailWord_5967778).sum := by decide
  have hdescent : baseEnd_5967778 < baseStart_5967778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967807 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_5967807 : Nat := 118140960795 + 5967807 * 2 ^ 59
def prefixEnd_5967807 : Nat := 4983230072969 + 3 ^ 40 * 5967807 * 2
def baseEnd_5967807 : Nat := 3064353444266437661367061

theorem tailTrace_5967807 : CollatzResearch.WordTrace tailWord_5967807 prefixEnd_5967807 3064353444266437661367061 := by
  unfold tailWord_5967807
  simp only [CollatzResearch.WordTrace]
  refine ⟨217663803090661934136437675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145109202060441289424291783 217663803090661934136437675)
  ·
    refine ⟨326495704635992901204656513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217663803090661934136437675 326495704635992901204656513)
    ·
      refine ⟨244871778476994675903492385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326495704635992901204656513 244871778476994675903492385)
      ·
        refine ⟨183653833857746006927619289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244871778476994675903492385 183653833857746006927619289)
        ·
          refine ⟨137740375393309505195714467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183653833857746006927619289 137740375393309505195714467)
          ·
            refine ⟨206610563089964257793571701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137740375393309505195714467 206610563089964257793571701)
            ·
              refine ⟨19369740289684149168147347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206610563089964257793571701 19369740289684149168147347)
              ·
                refine ⟨29054610434526223752221021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19369740289684149168147347 29054610434526223752221021)
                ·
                  refine ⟨10895478912947333907082883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29054610434526223752221021 10895478912947333907082883)
                  ·
                    refine ⟨16343218369421000860624325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10895478912947333907082883 16343218369421000860624325)
                    ·
                      refine ⟨3064353444266437661367061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16343218369421000860624325 3064353444266437661367061)
                      ·
                        rfl

theorem cell23_5967807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_5967807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967807 prefixEnd_5967807 := by exact prefixLift 5967807
  have htrace : WordTrace (prefixWord ++ tailWord_5967807) baseStart_5967807 baseEnd_5967807 := by
    simpa [prefixWord, tailWord_5967807, baseEnd_5967807] using wordTrace_append hprefix tailTrace_5967807
  have hstable : (prefixWord ++ tailWord_5967807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967807).length < 2 ^ (prefixWord ++ tailWord_5967807).sum := by decide
  have hdescent : baseEnd_5967807 < baseStart_5967807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967854 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_5967854 : Nat := 118140960795 + 5967854 * 2 ^ 59
def prefixEnd_5967854 : Nat := 4983230072969 + 3 ^ 40 * 5967854 * 2
def baseEnd_5967854 : Nat := 3064377577857198977479345

theorem tailTrace_5967854 : CollatzResearch.WordTrace tailWord_5967854 prefixEnd_5967854 3064377577857198977479345 := by
  unfold tailWord_5967854
  simp only [CollatzResearch.WordTrace]
  refine ⟨27208189665186457645424827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145110344880994440775599077 27208189665186457645424827)
  ·
    refine ⟨40812284497779686468137241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27208189665186457645424827 40812284497779686468137241)
    ·
      refine ⟨30609213373334764851102931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40812284497779686468137241 30609213373334764851102931)
      ·
        refine ⟨45913820060002147276654397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30609213373334764851102931 45913820060002147276654397)
        ·
          refine ⟨17217682522500805228745399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45913820060002147276654397 17217682522500805228745399)
          ·
            refine ⟨25826523783751207843118099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17217682522500805228745399 25826523783751207843118099)
            ·
              refine ⟨38739785675626811764677149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25826523783751207843118099 38739785675626811764677149)
              ·
                refine ⟨14527419628360054411753931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38739785675626811764677149 14527419628360054411753931)
                ·
                  refine ⟨21791129442540081617630897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14527419628360054411753931 21791129442540081617630897)
                  ·
                    refine ⟨16343347081905061213223173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21791129442540081617630897 16343347081905061213223173)
                    ·
                      refine ⟨3064377577857198977479345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16343347081905061213223173 3064377577857198977479345)
                      ·
                        rfl

theorem cell23_5967854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_5967854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967854 prefixEnd_5967854 := by exact prefixLift 5967854
  have htrace : WordTrace (prefixWord ++ tailWord_5967854) baseStart_5967854 baseEnd_5967854 := by
    simpa [prefixWord, tailWord_5967854, baseEnd_5967854] using wordTrace_append hprefix tailTrace_5967854
  have hstable : (prefixWord ++ tailWord_5967854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967854).length < 2 ^ (prefixWord ++ tailWord_5967854).sum := by decide
  have hdescent : baseEnd_5967854 < baseStart_5967854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967885 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_5967885 : Nat := 118140960795 + 5967885 * 2 ^ 59
def prefixEnd_5967885 : Nat := 4983230072969 + 3 ^ 40 * 5967885 * 2
def baseEnd_5967885 : Nat := 1021464498585829452063901

theorem tailTrace_5967885 : CollatzResearch.WordTrace tailWord_5967885 prefixEnd_5967885 1021464498585829452063901 := by
  unfold tailWord_5967885
  simp only [CollatzResearch.WordTrace]
  refine ⟨217666647984379353457777109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145111098656252902305184739 217666647984379353457777109)
  ·
    refine ⟨5101562062133891096666651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 217666647984379353457777109 5101562062133891096666651)
    ·
      refine ⟨7652343093200836644999977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5101562062133891096666651 7652343093200836644999977)
      ·
        refine ⟨5739257319900627483749983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7652343093200836644999977 5739257319900627483749983)
        ·
          refine ⟨8608885979850941225624975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739257319900627483749983 8608885979850941225624975)
          ·
            refine ⟨12913328969776411838437463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8608885979850941225624975 12913328969776411838437463)
            ·
              refine ⟨19369993454664617757656195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12913328969776411838437463 19369993454664617757656195)
              ·
                refine ⟨29054990181996926636484293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19369993454664617757656195 29054990181996926636484293)
                ·
                  refine ⟨5447810659124423744340805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29054990181996926636484293 5447810659124423744340805)
                  ·
                    refine ⟨1021464498585829452063901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5447810659124423744340805 1021464498585829452063901)
                    ·
                      rfl

theorem cell23_5967885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_5967885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967885 prefixEnd_5967885 := by exact prefixLift 5967885
  have htrace : WordTrace (prefixWord ++ tailWord_5967885) baseStart_5967885 baseEnd_5967885 := by
    simpa [prefixWord, tailWord_5967885, baseEnd_5967885] using wordTrace_append hprefix tailTrace_5967885
  have hstable : (prefixWord ++ tailWord_5967885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967885).length < 2 ^ (prefixWord ++ tailWord_5967885).sum := by decide
  have hdescent : baseEnd_5967885 < baseStart_5967885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967891 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 3]
def baseStart_5967891 : Nat := 118140960795 + 5967891 * 2 ^ 59
def prefixEnd_5967891 : Nat := 4983230072969 + 3 ^ 40 * 5967891 * 2
def baseEnd_5967891 : Nat := 3064396576641415332716675

theorem tailTrace_5967891 : CollatzResearch.WordTrace tailWord_5967891 prefixEnd_5967891 3064396576641415332716675 := by
  unfold tailWord_5967891
  simp only [CollatzResearch.WordTrace]
  refine ⟨217666866822357616482495527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145111244548238410988330351 217666866822357616482495527)
  ·
    refine ⟨326500300233536424723743291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217666866822357616482495527 326500300233536424723743291)
    ·
      refine ⟨489750450350304637085614937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326500300233536424723743291 489750450350304637085614937)
      ·
        refine ⟨367312837762728477814211203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489750450350304637085614937 367312837762728477814211203)
        ·
          refine ⟨550969256644092716721316805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367312837762728477814211203 550969256644092716721316805)
          ·
            refine ⟨103306735620767384385246901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 550969256644092716721316805 103306735620767384385246901)
            ·
              refine ⟨9685006464446942286116897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103306735620767384385246901 9685006464446942286116897)
              ·
                refine ⟨7263754848335206714587673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9685006464446942286116897 7263754848335206714587673)
                ·
                  refine ⟨5447816136251405035940755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7263754848335206714587673 5447816136251405035940755)
                  ·
                    refine ⟨8171724204377107553911133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5447816136251405035940755 8171724204377107553911133)
                    ·
                      refine ⟨3064396576641415332716675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8171724204377107553911133 3064396576641415332716675)
                      ·
                        rfl

theorem cell23_5967891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 1, 3].length) (baseStart_5967891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967891 prefixEnd_5967891 := by exact prefixLift 5967891
  have htrace : WordTrace (prefixWord ++ tailWord_5967891) baseStart_5967891 baseEnd_5967891 := by
    simpa [prefixWord, tailWord_5967891, baseEnd_5967891] using wordTrace_append hprefix tailTrace_5967891
  have hstable : (prefixWord ++ tailWord_5967891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967891).length < 2 ^ (prefixWord ++ tailWord_5967891).sum := by decide
  have hdescent : baseEnd_5967891 < baseStart_5967891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967892 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5967892 : Nat := 118140960795 + 5967892 * 2 ^ 59
def prefixEnd_5967892 : Nat := 4983230072969 + 3 ^ 40 * 5967892 * 2
def baseEnd_5967892 : Nat := 3064397090122069828804171

theorem tailTrace_5967892 : CollatzResearch.WordTrace tailWord_5967892 prefixEnd_5967892 3064397090122069828804171 := by
  unfold tailWord_5967892
  simp only [CollatzResearch.WordTrace]
  refine ⟨108833451647676996826640965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145111268863569329102187953 108833451647676996826640965)
  ·
    refine ⟨20406272183939436904995181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108833451647676996826640965 20406272183939436904995181)
    ·
      refine ⟨7652352068977288839373193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20406272183939436904995181 7652352068977288839373193)
      ·
        refine ⟨5739264051732966629529895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7652352068977288839373193 5739264051732966629529895)
        ·
          refine ⟨8608896077599449944294843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739264051732966629529895 8608896077599449944294843)
          ·
            refine ⟨12913344116399174916442265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8608896077599449944294843 12913344116399174916442265)
            ·
              refine ⟨9685008087299381187331699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12913344116399174916442265 9685008087299381187331699)
              ·
                refine ⟨14527512130949071780997549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9685008087299381187331699 14527512130949071780997549)
                ·
                  refine ⟨5447817049105901917874081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14527512130949071780997549 5447817049105901917874081)
                  ·
                    refine ⟨4085862786829426438405561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5447817049105901917874081 4085862786829426438405561)
                    ·
                      refine ⟨3064397090122069828804171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085862786829426438405561 3064397090122069828804171)
                      ·
                        rfl

theorem cell23_5967892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5967892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967892 prefixEnd_5967892 := by exact prefixLift 5967892
  have htrace : WordTrace (prefixWord ++ tailWord_5967892) baseStart_5967892 baseEnd_5967892 := by
    simpa [prefixWord, tailWord_5967892, baseEnd_5967892] using wordTrace_append hprefix tailTrace_5967892
  have hstable : (prefixWord ++ tailWord_5967892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967892).length < 2 ^ (prefixWord ++ tailWord_5967892).sum := by decide
  have hdescent : baseEnd_5967892 < baseStart_5967892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967907 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 2, 6]
def baseStart_5967907 : Nat := 118140960795 + 5967907 * 2 ^ 59
def prefixEnd_5967907 : Nat := 4983230072969 + 3 ^ 40 * 5967907 * 2
def baseEnd_5967907 : Nat := 1021468264110629090038867

theorem tailTrace_5967907 : CollatzResearch.WordTrace tailWord_5967907 prefixEnd_5967907 1021468264110629090038867 := by
  unfold tailWord_5967907
  simp only [CollatzResearch.WordTrace]
  refine ⟨217667450390299651215077975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145111633593533100810051983 217667450390299651215077975)
  ·
    refine ⟨326501175585449476822616963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217667450390299651215077975 326501175585449476822616963)
    ·
      refine ⟨489751763378174215233925445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326501175585449476822616963 489751763378174215233925445)
      ·
        refine ⟨91828455633407665356361021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 489751763378174215233925445 91828455633407665356361021)
        ·
          refine ⟨34435670862527874508635383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91828455633407665356361021 34435670862527874508635383)
          ·
            refine ⟨51653506293791811762953075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34435670862527874508635383 51653506293791811762953075)
            ·
              refine ⟨77480259440687717644429613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51653506293791811762953075 77480259440687717644429613)
              ·
                refine ⟨29055097290257894116661105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77480259440687717644429613 29055097290257894116661105)
                ·
                  refine ⟨21791322967693420587495829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29055097290257894116661105 21791322967693420587495829)
                  ·
                    refine ⟨1021468264110629090038867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21791322967693420587495829 1021468264110629090038867)
                    ·
                      rfl

theorem cell23_5967907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 6].length) (baseStart_5967907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967907 prefixEnd_5967907 := by exact prefixLift 5967907
  have htrace : WordTrace (prefixWord ++ tailWord_5967907) baseStart_5967907 baseEnd_5967907 := by
    simpa [prefixWord, tailWord_5967907, baseEnd_5967907] using wordTrace_append hprefix tailTrace_5967907
  have hstable : (prefixWord ++ tailWord_5967907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967907).length < 2 ^ (prefixWord ++ tailWord_5967907).sum := by decide
  have hdescent : baseEnd_5967907 < baseStart_5967907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967908 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_5967908 : Nat := 118140960795 + 5967908 * 2 ^ 59
def prefixEnd_5967908 : Nat := 4983230072969 + 3 ^ 40 * 5967908 * 2
def baseEnd_5967908 : Nat := 3064405305812541766204097

theorem tailTrace_5967908 : CollatzResearch.WordTrace tailWord_5967908 prefixEnd_5967908 3064405305812541766204097 := by
  unfold tailWord_5967908
  simp only [CollatzResearch.WordTrace]
  refine ⟨108833743431648014192932189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145111657908864018923909585 108833743431648014192932189)
  ·
    refine ⟨40812653786868005322349571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108833743431648014192932189 40812653786868005322349571)
    ·
      refine ⟨61218980680302007983524357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40812653786868005322349571 61218980680302007983524357)
      ·
        refine ⟨11478558877556626496910817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61218980680302007983524357 11478558877556626496910817)
        ·
          refine ⟨8608919158167469872683113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11478558877556626496910817 8608919158167469872683113)
          ·
            refine ⟨6456689368625602404512335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8608919158167469872683113 6456689368625602404512335)
            ·
              refine ⟨9685034052938403606768503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456689368625602404512335 9685034052938403606768503)
              ·
                refine ⟨14527551079407605410152755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9685034052938403606768503 14527551079407605410152755)
                ·
                  refine ⟨21791326619111408115229133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14527551079407605410152755 21791326619111408115229133)
                  ·
                    refine ⟨8171747482166778043210925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21791326619111408115229133 8171747482166778043210925)
                    ·
                      refine ⟨3064405305812541766204097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8171747482166778043210925 3064405305812541766204097)
                      ·
                        rfl

theorem cell23_5967908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_5967908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967908 prefixEnd_5967908 := by exact prefixLift 5967908
  have htrace : WordTrace (prefixWord ++ tailWord_5967908) baseStart_5967908 baseEnd_5967908 := by
    simpa [prefixWord, tailWord_5967908, baseEnd_5967908] using wordTrace_append hprefix tailTrace_5967908
  have hstable : (prefixWord ++ tailWord_5967908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967908).length < 2 ^ (prefixWord ++ tailWord_5967908).sum := by decide
  have hdescent : baseEnd_5967908 < baseStart_5967908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967918 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_5967918 : Nat := 118140960795 + 5967918 * 2 ^ 59
def prefixEnd_5967918 : Nat := 4983230072969 + 3 ^ 40 * 5967918 * 2
def baseEnd_5967918 : Nat := 3064410440619086727079051

theorem tailTrace_5967918 : CollatzResearch.WordTrace tailWord_5967918 prefixEnd_5967918 3064410440619086727079051 := by
  unfold tailWord_5967918
  simp only [CollatzResearch.WordTrace]
  refine ⟨27208481449157475011716051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145111901062173200062485605 27208481449157475011716051)
  ·
    refine ⟨40812722173736212517574077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27208481449157475011716051 40812722173736212517574077)
    ·
      refine ⟨15304770815151079694090279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40812722173736212517574077 15304770815151079694090279)
      ·
        refine ⟨22957156222726619541135419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15304770815151079694090279 22957156222726619541135419)
        ·
          refine ⟨34435734334089929311703129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22957156222726619541135419 34435734334089929311703129)
          ·
            refine ⟨25826800750567446983777347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34435734334089929311703129 25826800750567446983777347)
            ·
              refine ⟨38740201125851170475666021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25826800750567446983777347 38740201125851170475666021)
              ·
                refine ⟨7263787711097094464187379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38740201125851170475666021 7263787711097094464187379)
                ·
                  refine ⟨10895681566645641696281069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7263787711097094464187379 10895681566645641696281069)
                  ·
                    refine ⟨4085880587492115636105401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10895681566645641696281069 4085880587492115636105401)
                    ·
                      refine ⟨3064410440619086727079051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085880587492115636105401 3064410440619086727079051)
                      ·
                        rfl

theorem cell23_5967918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_5967918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967918 prefixEnd_5967918 := by exact prefixLift 5967918
  have htrace : WordTrace (prefixWord ++ tailWord_5967918) baseStart_5967918 baseEnd_5967918 := by
    simpa [prefixWord, tailWord_5967918, baseEnd_5967918] using wordTrace_append hprefix tailTrace_5967918
  have hstable : (prefixWord ++ tailWord_5967918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967918).length < 2 ^ (prefixWord ++ tailWord_5967918).sum := by decide
  have hdescent : baseEnd_5967918 < baseStart_5967918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967927 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_5967927 : Nat := 118140960795 + 5967927 * 2 ^ 59
def prefixEnd_5967927 : Nat := 4983230072969 + 3 ^ 40 * 5967927 * 2
def baseEnd_5967927 : Nat := 3064415061944977191866509

theorem tailTrace_5967927 : CollatzResearch.WordTrace tailWord_5967927 prefixEnd_5967927 3064415061944977191866509 := by
  unfold tailWord_5967927
  simp only [CollatzResearch.WordTrace]
  refine ⟨217668179850227194630806035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145112119900151463087204023 217668179850227194630806035)
  ·
    refine ⟨326502269775340791946209053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217668179850227194630806035 326502269775340791946209053)
    ·
      refine ⟨122438351165752796979828395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326502269775340791946209053 122438351165752796979828395)
      ·
        refine ⟨183657526748629195469742593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122438351165752796979828395 183657526748629195469742593)
        ·
          refine ⟨137743145061471896602306945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183657526748629195469742593 137743145061471896602306945)
          ·
            refine ⟨103307358796103922451730209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137743145061471896602306945 103307358796103922451730209)
            ·
              refine ⟨77480519097077941838797657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103307358796103922451730209 77480519097077941838797657)
              ·
                refine ⟨58110389322808456379098243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77480519097077941838797657 58110389322808456379098243)
                ·
                  refine ⟨87165583984212684568647365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58110389322808456379098243 87165583984212684568647365)
                  ·
                    refine ⟨16343546997039878356621381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87165583984212684568647365 16343546997039878356621381)
                    ·
                      refine ⟨3064415061944977191866509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16343546997039878356621381 3064415061944977191866509)
                      ·
                        rfl

theorem cell23_5967927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_5967927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967927 prefixEnd_5967927 := by exact prefixLift 5967927
  have htrace : WordTrace (prefixWord ++ tailWord_5967927) baseStart_5967927 baseEnd_5967927 := by
    simpa [prefixWord, tailWord_5967927, baseEnd_5967927] using wordTrace_append hprefix tailTrace_5967927
  have hstable : (prefixWord ++ tailWord_5967927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967927).length < 2 ^ (prefixWord ++ tailWord_5967927).sum := by decide
  have hdescent : baseEnd_5967927 < baseStart_5967927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967967 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 1, 7]
def baseStart_5967967 : Nat := 118140960795 + 5967967 * 2 ^ 59
def prefixEnd_5967967 : Nat := 4983230072969 + 3 ^ 40 * 5967967 * 2
def baseEnd_5967967 : Nat := 1021478533723719011788775

theorem tailTrace_5967967 : CollatzResearch.WordTrace tailWord_5967967 prefixEnd_5967967 1021478533723719011788775 := by
  unfold tailWord_5967967
  simp only [CollatzResearch.WordTrace]
  refine ⟨217669638770082281462262155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145113092513388187641508103 217669638770082281462262155)
  ·
    refine ⟨326504458155123422193393233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217669638770082281462262155 326504458155123422193393233)
    ·
      refine ⟨244878343616342566645044925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326504458155123422193393233 244878343616342566645044925)
      ·
        refine ⟨91829378856128462491891847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244878343616342566645044925 91829378856128462491891847)
        ·
          refine ⟨137744068284192693737837771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91829378856128462491891847 137744068284192693737837771)
          ·
            refine ⟨206616102426289040606756657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137744068284192693737837771 206616102426289040606756657)
            ·
              refine ⟨154962076819716780455067493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206616102426289040606756657 154962076819716780455067493)
              ·
                refine ⟨29055389403696896335325155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154962076819716780455067493 29055389403696896335325155)
                ·
                  refine ⟨43583084105545344502987733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29055389403696896335325155 43583084105545344502987733)
                  ·
                    refine ⟨1021478533723719011788775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43583084105545344502987733 1021478533723719011788775)
                    ·
                      rfl

theorem cell23_5967967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_5967967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967967 prefixEnd_5967967 := by exact prefixLift 5967967
  have htrace : WordTrace (prefixWord ++ tailWord_5967967) baseStart_5967967 baseEnd_5967967 := by
    simpa [prefixWord, tailWord_5967967, baseEnd_5967967] using wordTrace_append hprefix tailTrace_5967967
  have hstable : (prefixWord ++ tailWord_5967967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967967).length < 2 ^ (prefixWord ++ tailWord_5967967).sum := by decide
  have hdescent : baseEnd_5967967 < baseStart_5967967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967977 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_5967977 : Nat := 118140960795 + 5967977 * 2 ^ 59
def prefixEnd_5967977 : Nat := 4983230072969 + 3 ^ 40 * 5967977 * 2
def baseEnd_5967977 : Nat := 3064440735977701996241279

theorem tailTrace_5967977 : CollatzResearch.WordTrace tailWord_5967977 prefixEnd_5967977 3064440735977701996241279 := by
  unfold tailWord_5967977
  simp only [CollatzResearch.WordTrace]
  refine ⟨217670003500046053170126185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145113335666697368780084123 217670003500046053170126185)
  ·
    refine ⟨163252502625034539877594639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217670003500046053170126185 163252502625034539877594639)
    ·
      refine ⟨244878753937551809816391959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163252502625034539877594639 244878753937551809816391959)
      ·
        refine ⟨367318130906327714724587939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244878753937551809816391959 367318130906327714724587939)
        ·
          refine ⟨550977196359491572086881909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367318130906327714724587939 550977196359491572086881909)
          ·
            refine ⟨51654112158702334883145179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 550977196359491572086881909 51654112158702334883145179)
            ·
              refine ⟨77481168238053502324717769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51654112158702334883145179 77481168238053502324717769)
              ·
                refine ⟨58110876178540126743538327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77481168238053502324717769 58110876178540126743538327)
                ·
                  refine ⟨87166314267810190115307491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58110876178540126743538327 87166314267810190115307491)
                  ·
                    refine ⟨130749471401715285172961237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87166314267810190115307491 130749471401715285172961237)
                    ·
                      refine ⟨3064440735977701996241279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130749471401715285172961237 3064440735977701996241279)
                      ·
                        rfl

theorem cell23_5967977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_5967977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967977 prefixEnd_5967977 := by exact prefixLift 5967977
  have htrace : WordTrace (prefixWord ++ tailWord_5967977) baseStart_5967977 baseEnd_5967977 := by
    simpa [prefixWord, tailWord_5967977, baseEnd_5967977] using wordTrace_append hprefix tailTrace_5967977
  have hstable : (prefixWord ++ tailWord_5967977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967977).length < 2 ^ (prefixWord ++ tailWord_5967977).sum := by decide
  have hdescent : baseEnd_5967977 < baseStart_5967977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5967984 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 2, 5]
def baseStart_5967984 : Nat := 118140960795 + 5967984 * 2 ^ 59
def prefixEnd_5967984 : Nat := 4983230072969 + 3 ^ 40 * 5967984 * 2
def baseEnd_5967984 : Nat := 1021481443447427822951249

theorem tailTrace_5967984 : CollatzResearch.WordTrace tailWord_5967984 prefixEnd_5967984 1021481443447427822951249 := by
  unfold tailWord_5967984
  simp only [CollatzResearch.WordTrace]
  refine ⟨108835129405510346682815503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145113505874013795577087337 108835129405510346682815503)
  ·
    refine ⟨163252694108265520024223255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108835129405510346682815503 163252694108265520024223255)
    ·
      refine ⟨244879041162398280036334883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163252694108265520024223255 244879041162398280036334883)
      ·
        refine ⟨367318561743597420054502325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244879041162398280036334883 367318561743597420054502325)
        ·
          refine ⟨34436115163462258130109593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 367318561743597420054502325 34436115163462258130109593)
          ·
            refine ⟨25827086372596693597582195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34436115163462258130109593 25827086372596693597582195)
            ·
              refine ⟨38740629558895040396373293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25827086372596693597582195 38740629558895040396373293)
              ·
                refine ⟨14527736084585640148639985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38740629558895040396373293 14527736084585640148639985)
                ·
                  refine ⟨10895802063439230111479989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14527736084585640148639985 10895802063439230111479989)
                  ·
                    refine ⟨1021481443447427822951249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10895802063439230111479989 1021481443447427822951249)
                    ·
                      rfl

theorem cell23_5967984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_5967984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5967984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5967984 prefixEnd_5967984 := by exact prefixLift 5967984
  have htrace : WordTrace (prefixWord ++ tailWord_5967984) baseStart_5967984 baseEnd_5967984 := by
    simpa [prefixWord, tailWord_5967984, baseEnd_5967984] using wordTrace_append hprefix tailTrace_5967984
  have hstable : (prefixWord ++ tailWord_5967984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5967984).length < 2 ^ (prefixWord ++ tailWord_5967984).sum := by decide
  have hdescent : baseEnd_5967984 < baseStart_5967984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5967984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968021 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 2, 4, 2]
def baseStart_5968021 : Nat := 118140960795 + 5968021 * 2 ^ 59
def prefixEnd_5968021 : Nat := 4983230072969 + 3 ^ 40 * 5968021 * 2
def baseEnd_5968021 : Nat := 3064463329126499824091077

theorem tailTrace_5968021 : CollatzResearch.WordTrace tailWord_5968021 prefixEnd_5968021 3064463329126499824091077 := by
  unfold tailWord_5968021
  simp only [CollatzResearch.WordTrace]
  refine ⟨217671608311886648684727917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145114405541257765789818611 217671608311886648684727917)
  ·
    refine ⟨81626853116957493256772969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217671608311886648684727917 81626853116957493256772969)
    ·
      refine ⟨61220139837718119942579727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81626853116957493256772969 61220139837718119942579727)
      ·
        refine ⟨91830209756577179913869591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61220139837718119942579727 91830209756577179913869591)
        ·
          refine ⟨137745314634865769870804387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91830209756577179913869591 137745314634865769870804387)
          ·
            refine ⟨206617971952298654806206581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137745314634865769870804387 206617971952298654806206581)
            ·
              refine ⟨19370434870527998888081867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206617971952298654806206581 19370434870527998888081867)
              ·
                refine ⟨29055652305791998332122801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19370434870527998888081867 29055652305791998332122801)
                ·
                  refine ⟨21791739229343998749092101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29055652305791998332122801 21791739229343998749092101)
                  ·
                    refine ⟨4085951105501999765454769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21791739229343998749092101 4085951105501999765454769)
                    ·
                      refine ⟨3064463329126499824091077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085951105501999765454769 3064463329126499824091077)
                      ·
                        rfl

theorem cell23_5968021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_5968021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968021 prefixEnd_5968021 := by exact prefixLift 5968021
  have htrace : WordTrace (prefixWord ++ tailWord_5968021) baseStart_5968021 baseEnd_5968021 := by
    simpa [prefixWord, tailWord_5968021, baseEnd_5968021] using wordTrace_append hprefix tailTrace_5968021
  have hstable : (prefixWord ++ tailWord_5968021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968021).length < 2 ^ (prefixWord ++ tailWord_5968021).sum := by decide
  have hdescent : baseEnd_5968021 < baseStart_5968021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968022 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_5968022 : Nat := 118140960795 + 5968022 * 2 ^ 59
def prefixEnd_5968022 : Nat := 4983230072969 + 3 ^ 40 * 5968022 * 2
def baseEnd_5968022 : Nat := 340495982511906035575397

theorem tailTrace_5968022 : CollatzResearch.WordTrace tailWord_5968022 prefixEnd_5968022 340495982511906035575397 := by
  unfold tailWord_5968022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13604477799055189115969645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145114429856588683903676213 13604477799055189115969645)
  ·
    refine ⟨5101679174645695918488617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13604477799055189115969645 5101679174645695918488617)
    ·
      refine ⟨3826259380984271938866463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5101679174645695918488617 3826259380984271938866463)
      ·
        refine ⟨5739389071476407908299695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3826259380984271938866463 5739389071476407908299695)
        ·
          refine ⟨8609083607214611862449543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739389071476407908299695 8609083607214611862449543)
          ·
            refine ⟨12913625410821917793674315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8609083607214611862449543 12913625410821917793674315)
            ·
              refine ⟨19370438116232876690511473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12913625410821917793674315 19370438116232876690511473)
              ·
                refine ⟨14527828587174657517883605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19370438116232876690511473 14527828587174657517883605)
                ·
                  refine ⟨340495982511906035575397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14527828587174657517883605 340495982511906035575397)
                  ·
                    rfl

theorem cell23_5968022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_5968022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968022 prefixEnd_5968022 := by exact prefixLift 5968022
  have htrace : WordTrace (prefixWord ++ tailWord_5968022) baseStart_5968022 baseEnd_5968022 := by
    simpa [prefixWord, tailWord_5968022, baseEnd_5968022] using wordTrace_append hprefix tailTrace_5968022
  have hstable : (prefixWord ++ tailWord_5968022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968022).length < 2 ^ (prefixWord ++ tailWord_5968022).sum := by decide
  have hdescent : baseEnd_5968022 < baseStart_5968022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968031 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 5, 4]
def baseStart_5968031 : Nat := 118140960795 + 5968031 * 2 ^ 59
def prefixEnd_5968031 : Nat := 4983230072969 + 3 ^ 40 * 5968031 * 2
def baseEnd_5968031 : Nat := 1021489487977681594988677

theorem tailTrace_5968031 : CollatzResearch.WordTrace tailWord_5968031 prefixEnd_5968031 1021489487977681594988677 := by
  unfold tailWord_5968031
  simp only [CollatzResearch.WordTrace]
  refine ⟨217671973041850420392591947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145114648694566946928394631 217671973041850420392591947)
  ·
    refine ⟨326507959562775630588887921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217671973041850420392591947 326507959562775630588887921)
    ·
      refine ⟨244880969672081722941665941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326507959562775630588887921 244880969672081722941665941)
      ·
        refine ⟨11478795453378830762890591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 244880969672081722941665941 11478795453378830762890591)
        ·
          refine ⟨17218193180068246144335887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11478795453378830762890591 17218193180068246144335887)
          ·
            refine ⟨25827289770102369216503831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17218193180068246144335887 25827289770102369216503831)
            ·
              refine ⟨38740934655153553824755747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25827289770102369216503831 38740934655153553824755747)
              ·
                refine ⟨58111401982730330737133621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38740934655153553824755747 58111401982730330737133621)
                ·
                  refine ⟨5447943935880968506606277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58111401982730330737133621 5447943935880968506606277)
                  ·
                    refine ⟨1021489487977681594988677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5447943935880968506606277 1021489487977681594988677)
                    ·
                      rfl

theorem cell23_5968031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 4].length) (baseStart_5968031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968031 prefixEnd_5968031 := by exact prefixLift 5968031
  have htrace : WordTrace (prefixWord ++ tailWord_5968031) baseStart_5968031 baseEnd_5968031 := by
    simpa [prefixWord, tailWord_5968031, baseEnd_5968031] using wordTrace_append hprefix tailTrace_5968031
  have hstable : (prefixWord ++ tailWord_5968031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968031).length < 2 ^ (prefixWord ++ tailWord_5968031).sum := by decide
  have hdescent : baseEnd_5968031 < baseStart_5968031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968064 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_5968064 : Nat := 118140960795 + 5968064 * 2 ^ 59
def prefixEnd_5968064 : Nat := 4983230072969 + 3 ^ 40 * 5968064 * 2
def baseEnd_5968064 : Nat := 3064485408794643155853379

theorem tailTrace_5968064 : CollatzResearch.WordTrace tailWord_5968064 prefixEnd_5968064 3064485408794643155853379 := by
  unfold tailWord_5968064
  simp only [CollatzResearch.WordTrace]
  refine ⟨108836588325365433514271623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145115451100487244685695497 108836588325365433514271623)
  ·
    refine ⟨163254882488048150271407435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108836588325365433514271623 163254882488048150271407435)
    ·
      refine ⟨244882323732072225407111153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163254882488048150271407435 244882323732072225407111153)
      ·
        refine ⟨183661742799054169055333365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244882323732072225407111153 183661742799054169055333365)
        ·
          refine ⟨17218288387411328348937503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183661742799054169055333365 17218288387411328348937503)
          ·
            refine ⟨25827432581116992523406255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17218288387411328348937503 25827432581116992523406255)
            ·
              refine ⟨38741148871675488785109383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25827432581116992523406255 38741148871675488785109383)
              ·
                refine ⟨58111723307513233177664075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38741148871675488785109383 58111723307513233177664075)
                ·
                  refine ⟨87167584961269849766496113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58111723307513233177664075 87167584961269849766496113)
                  ·
                    refine ⟨65375688720952387324872085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87167584961269849766496113 65375688720952387324872085)
                    ·
                      refine ⟨3064485408794643155853379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65375688720952387324872085 3064485408794643155853379)
                      ·
                        rfl

theorem cell23_5968064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_5968064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968064 prefixEnd_5968064 := by exact prefixLift 5968064
  have htrace : WordTrace (prefixWord ++ tailWord_5968064) baseStart_5968064 baseEnd_5968064 := by
    simpa [prefixWord, tailWord_5968064, baseEnd_5968064] using wordTrace_append hprefix tailTrace_5968064
  have hstable : (prefixWord ++ tailWord_5968064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968064).length < 2 ^ (prefixWord ++ tailWord_5968064).sum := by decide
  have hdescent : baseEnd_5968064 < baseStart_5968064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968065 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 3, 4]
def baseStart_5968065 : Nat := 118140960795 + 5968065 * 2 ^ 59
def prefixEnd_5968065 : Nat := 4983230072969 + 3 ^ 40 * 5968065 * 2
def baseEnd_5968065 : Nat := 1021495307425099217313625

theorem tailTrace_5968065 : CollatzResearch.WordTrace tailWord_5968065 prefixEnd_5968065 1021495307425099217313625 := by
  unfold tailWord_5968065
  simp only [CollatzResearch.WordTrace]
  refine ⟨217673213123727244199329649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145115475415818162799553099 217673213123727244199329649)
  ·
    refine ⟨163254909842795433149497237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217673213123727244199329649 163254909842795433149497237)
    ·
      refine ⟨7652573898881035928882683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 163254909842795433149497237 7652573898881035928882683)
      ·
        refine ⟨11478860848321553893324025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7652573898881035928882683 11478860848321553893324025)
        ·
          refine ⟨8609145636241165419993019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11478860848321553893324025 8609145636241165419993019)
          ·
            refine ⟨12913718454361748129989529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8609145636241165419993019 12913718454361748129989529)
            ·
              refine ⟨9685288840771311097492147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12913718454361748129989529 9685288840771311097492147)
              ·
                refine ⟨14527933261156966646238221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9685288840771311097492147 14527933261156966646238221)
                ·
                  refine ⟨5447974972933862492339333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14527933261156966646238221 5447974972933862492339333)
                  ·
                    refine ⟨1021495307425099217313625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5447974972933862492339333 1021495307425099217313625)
                    ·
                      rfl

theorem cell23_5968065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_5968065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968065 prefixEnd_5968065 := by exact prefixLift 5968065
  have htrace : WordTrace (prefixWord ++ tailWord_5968065) baseStart_5968065 baseEnd_5968065 := by
    simpa [prefixWord, tailWord_5968065, baseEnd_5968065] using wordTrace_append hprefix tailTrace_5968065
  have hstable : (prefixWord ++ tailWord_5968065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968065).length < 2 ^ (prefixWord ++ tailWord_5968065).sum := by decide
  have hdescent : baseEnd_5968065 < baseStart_5968065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968078 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 6]
def baseStart_5968078 : Nat := 118140960795 + 5968078 * 2 ^ 59
def prefixEnd_5968078 : Nat := 4983230072969 + 3 ^ 40 * 5968078 * 2
def baseEnd_5968078 : Nat := 340499177502645122342035

theorem tailTrace_5968078 : CollatzResearch.WordTrace tailWord_5968078 prefixEnd_5968078 340499177502645122342035 := by
  unfold tailWord_5968078
  simp only [CollatzResearch.WordTrace]
  refine ⟨27209210909085018427444111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145115791515120098279701925 27209210909085018427444111)
  ·
    refine ⟨40813816363627527641166167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27209210909085018427444111 40813816363627527641166167)
    ·
      refine ⟨61220724545441291461749251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40813816363627527641166167 61220724545441291461749251)
      ·
        refine ⟨91831086818161937192623877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61220724545441291461749251 91831086818161937192623877)
        ·
          refine ⟨17218328778405363223616977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91831086818161937192623877 17218328778405363223616977)
          ·
            refine ⟨12913746583804022417712733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17218328778405363223616977 12913746583804022417712733)
            ·
              refine ⟨4842654968926508406642275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12913746583804022417712733 4842654968926508406642275)
              ·
                refine ⟨7263982453389762609963413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842654968926508406642275 7263982453389762609963413)
                ·
                  refine ⟨340499177502645122342035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7263982453389762609963413 340499177502645122342035)
                  ·
                    rfl

theorem cell23_5968078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_5968078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968078 prefixEnd_5968078 := by exact prefixLift 5968078
  have htrace : WordTrace (prefixWord ++ tailWord_5968078) baseStart_5968078 baseEnd_5968078 := by
    simpa [prefixWord, tailWord_5968078, baseEnd_5968078] using wordTrace_append hprefix tailTrace_5968078
  have hstable : (prefixWord ++ tailWord_5968078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968078).length < 2 ^ (prefixWord ++ tailWord_5968078).sum := by decide
  have hdescent : baseEnd_5968078 < baseStart_5968078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968081 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 1, 5, 2]
def baseStart_5968081 : Nat := 118140960795 + 5968081 * 2 ^ 59
def prefixEnd_5968081 : Nat := 4983230072969 + 3 ^ 40 * 5968081 * 2
def baseEnd_5968081 : Nat := 3064494137965769589340801

theorem tailTrace_5968081 : CollatzResearch.WordTrace tailWord_5968081 prefixEnd_5968081 3064494137965769589340801 := by
  unfold tailWord_5968081
  simp only [CollatzResearch.WordTrace]
  refine ⟨217673796691669278931912097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145115864461112852621274731 217673796691669278931912097)
  ·
    refine ⟨163255347518751959198934073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217673796691669278931912097 163255347518751959198934073)
    ·
      refine ⟨122441510639063969399200555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163255347518751959198934073 122441510639063969399200555)
      ·
        refine ⟨183662265958595954098800833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122441510639063969399200555 183662265958595954098800833)
        ·
          refine ⟨137746699468946965574100625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183662265958595954098800833 137746699468946965574100625)
          ·
            refine ⟨103310024601710224180575469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137746699468946965574100625 103310024601710224180575469)
            ·
              refine ⟨38741259225641334067715801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103310024601710224180575469 38741259225641334067715801)
              ·
                refine ⟨29055944419231000550786851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38741259225641334067715801 29055944419231000550786851)
                ·
                  refine ⟨43583916628846500826180277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29055944419231000550786851 43583916628846500826180277)
                  ·
                    refine ⟨4085992183954359452454401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43583916628846500826180277 4085992183954359452454401)
                    ·
                      refine ⟨3064494137965769589340801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4085992183954359452454401 3064494137965769589340801)
                      ·
                        rfl

theorem cell23_5968081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_5968081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968081 prefixEnd_5968081 := by exact prefixLift 5968081
  have htrace : WordTrace (prefixWord ++ tailWord_5968081) baseStart_5968081 baseEnd_5968081 := by
    simpa [prefixWord, tailWord_5968081, baseEnd_5968081] using wordTrace_append hprefix tailTrace_5968081
  have hstable : (prefixWord ++ tailWord_5968081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968081).length < 2 ^ (prefixWord ++ tailWord_5968081).sum := by decide
  have hdescent : baseEnd_5968081 < baseStart_5968081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968088 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 3, 1, 3]
def baseStart_5968088 : Nat := 118140960795 + 5968088 * 2 ^ 59
def prefixEnd_5968088 : Nat := 4983230072969 + 3 ^ 40 * 5968088 * 2
def baseEnd_5968088 : Nat := 3064497732330351061953269

theorem tailTrace_5968088 : CollatzResearch.WordTrace tailWord_5968088 prefixEnd_5968088 3064497732330351061953269 := by
  unfold tailWord_5968088
  simp only [CollatzResearch.WordTrace]
  refine ⟨108837026001321959563708459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145116034668429279418277945 108837026001321959563708459)
  ·
    refine ⟨163255539001982939345562689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108837026001321959563708459 163255539001982939345562689)
    ·
      refine ⟨122441654251487204509172017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163255539001982939345562689 122441654251487204509172017)
      ·
        refine ⟨91831240688615403381879013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122441654251487204509172017 91831240688615403381879013)
        ·
          refine ⟨17218357629115388134102315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91831240688615403381879013 17218357629115388134102315)
          ·
            refine ⟨25827536443673082201153473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17218357629115388134102315 25827536443673082201153473)
            ·
              refine ⟨19370652332754811650865105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25827536443673082201153473 19370652332754811650865105)
              ·
                refine ⟨14527989249566108738148829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19370652332754811650865105 14527989249566108738148829)
                ·
                  refine ⟨5447995968587290776805811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14527989249566108738148829 5447995968587290776805811)
                  ·
                    refine ⟨8171993952880936165208717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5447995968587290776805811 8171993952880936165208717)
                    ·
                      refine ⟨3064497732330351061953269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8171993952880936165208717 3064497732330351061953269)
                      ·
                        rfl

theorem cell23_5968088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_5968088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968088 prefixEnd_5968088 := by exact prefixLift 5968088
  have htrace : WordTrace (prefixWord ++ tailWord_5968088) baseStart_5968088 baseEnd_5968088 := by
    simpa [prefixWord, tailWord_5968088, baseEnd_5968088] using wordTrace_append hprefix tailTrace_5968088
  have hstable : (prefixWord ++ tailWord_5968088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968088).length < 2 ^ (prefixWord ++ tailWord_5968088).sum := by decide
  have hdescent : baseEnd_5968088 < baseStart_5968088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968099 : List Nat := [1, 1, 1, 8, 2, 1, 1, 3, 1, 4]
def baseStart_5968099 : Nat := 118140960795 + 5968099 * 2 ^ 59
def prefixEnd_5968099 : Nat := 4983230072969 + 3 ^ 40 * 5968099 * 2
def baseEnd_5968099 : Nat := 1021501126872516839638573

theorem tailTrace_5968099 : CollatzResearch.WordTrace tailWord_5968099 prefixEnd_5968099 1021501126872516839638573 := by
  unfold tailWord_5968099
  simp only [CollatzResearch.WordTrace]
  refine ⟨217674453205604068006067351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145116302137069378670711567 217674453205604068006067351)
  ·
    refine ⟨326511679808406102009101027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217674453205604068006067351 326511679808406102009101027)
    ·
      refine ⟨489767519712609153013651541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326511679808406102009101027 489767519712609153013651541)
      ·
        refine ⟨5739463121632138511878729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 489767519712609153013651541 5739463121632138511878729)
        ·
          refine ⟨4304597341224103883909047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5739463121632138511878729 4304597341224103883909047)
          ·
            refine ⟨6456896011836155825863571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304597341224103883909047 6456896011836155825863571)
            ·
              refine ⟨9685344017754233738795357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456896011836155825863571 9685344017754233738795357)
              ·
                refine ⟨3632004006657837652048259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9685344017754233738795357 3632004006657837652048259)
                ·
                  refine ⟨5448006009986756478072389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632004006657837652048259 5448006009986756478072389)
                  ·
                    refine ⟨1021501126872516839638573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5448006009986756478072389 1021501126872516839638573)
                    ·
                      rfl

theorem cell23_5968099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 4].length) (baseStart_5968099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968099 prefixEnd_5968099 := by exact prefixLift 5968099
  have htrace : WordTrace (prefixWord ++ tailWord_5968099) baseStart_5968099 baseEnd_5968099 := by
    simpa [prefixWord, tailWord_5968099, baseEnd_5968099] using wordTrace_append hprefix tailTrace_5968099
  have hstable : (prefixWord ++ tailWord_5968099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968099).length < 2 ^ (prefixWord ++ tailWord_5968099).sum := by decide
  have hdescent : baseEnd_5968099 < baseStart_5968099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968122 : List Nat := [3, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3]
def baseStart_5968122 : Nat := 118140960795 + 5968122 * 2 ^ 59
def prefixEnd_5968122 : Nat := 4983230072969 + 3 ^ 40 * 5968122 * 2
def baseEnd_5968122 : Nat := 3064515190672603928928113

theorem tailTrace_5968122 : CollatzResearch.WordTrace tailWord_5968122 prefixEnd_5968122 3064515190672603928928113 := by
  unfold tailWord_5968122
  simp only [CollatzResearch.WordTrace]
  refine ⟨54418823021130185733538655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145116861389680495289436413 54418823021130185733538655)
  ·
    refine ⟨81628234531695278600307983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54418823021130185733538655 81628234531695278600307983)
    ·
      refine ⟨122442351797542917900461975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81628234531695278600307983 122442351797542917900461975)
      ·
        refine ⟨183663527696314376850692963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122442351797542917900461975 183663527696314376850692963)
        ·
          refine ⟨275495291544471565276039445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183663527696314376850692963 275495291544471565276039445)
          ·
            refine ⟨12913841791147104622314349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 275495291544471565276039445 12913841791147104622314349)
            ·
              refine ⟨4842690671680164233367881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12913841791147104622314349 4842690671680164233367881)
              ·
                refine ⟨3632018003760123175025911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4842690671680164233367881 3632018003760123175025911)
                ·
                  refine ⟨5448027005640184762538867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632018003760123175025911 5448027005640184762538867)
                  ·
                    refine ⟨8172040508460277143808301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5448027005640184762538867 8172040508460277143808301)
                    ·
                      refine ⟨3064515190672603928928113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172040508460277143808301 3064515190672603928928113)
                      ·
                        rfl

theorem cell23_5968122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3].length) (baseStart_5968122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968122 prefixEnd_5968122 := by exact prefixLift 5968122
  have htrace : WordTrace (prefixWord ++ tailWord_5968122) baseStart_5968122 baseEnd_5968122 := by
    simpa [prefixWord, tailWord_5968122, baseEnd_5968122] using wordTrace_append hprefix tailTrace_5968122
  have hstable : (prefixWord ++ tailWord_5968122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968122).length < 2 ^ (prefixWord ++ tailWord_5968122).sum := by decide
  have hdescent : baseEnd_5968122 < baseStart_5968122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968131 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 3]
def baseStart_5968131 : Nat := 118140960795 + 5968131 * 2 ^ 59
def prefixEnd_5968131 : Nat := 4983230072969 + 3 ^ 40 * 5968131 * 2
def baseEnd_5968131 : Nat := 3064519811998494393715571

theorem tailTrace_5968131 : CollatzResearch.WordTrace tailWord_5968131 prefixEnd_5968131 3064519811998494393715571 := by
  unfold tailWord_5968131
  simp only [CollatzResearch.WordTrace]
  refine ⟨217675620341488137471232247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145117080227658758314154831 217675620341488137471232247)
  ·
    refine ⟨326513430512232206206848371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217675620341488137471232247 326513430512232206206848371)
    ·
      refine ⟨489770145768348309310272557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326513430512232206206848371 489770145768348309310272557)
      ·
        refine ⟨183663804663130615991352209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489770145768348309310272557 183663804663130615991352209)
        ·
          refine ⟨137747853497347961993514157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183663804663130615991352209 137747853497347961993514157)
          ·
            refine ⟨51655445061505485747567809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137747853497347961993514157 51655445061505485747567809)
            ·
              refine ⟨38741583796129114310675857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51655445061505485747567809 38741583796129114310675857)
              ·
                refine ⟨29056187847096835733006893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38741583796129114310675857 29056187847096835733006893)
                ·
                  refine ⟨10896070442661313399877585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29056187847096835733006893 10896070442661313399877585)
                  ·
                    refine ⟨8172052831995985049908189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10896070442661313399877585 8172052831995985049908189)
                    ·
                      refine ⟨3064519811998494393715571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172052831995985049908189 3064519811998494393715571)
                      ·
                        rfl

theorem cell23_5968131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_5968131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968131 prefixEnd_5968131 := by exact prefixLift 5968131
  have htrace : WordTrace (prefixWord ++ tailWord_5968131) baseStart_5968131 baseEnd_5968131 := by
    simpa [prefixWord, tailWord_5968131, baseEnd_5968131] using wordTrace_append hprefix tailTrace_5968131
  have hstable : (prefixWord ++ tailWord_5968131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968131).length < 2 ^ (prefixWord ++ tailWord_5968131).sum := by decide
  have hdescent : baseEnd_5968131 < baseStart_5968131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968161 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_5968161 : Nat := 118140960795 + 5968161 * 2 ^ 59
def prefixEnd_5968161 : Nat := 4983230072969 + 3 ^ 40 * 5968161 * 2
def baseEnd_5968161 : Nat := 3064535216418129276340433

theorem tailTrace_5968161 : CollatzResearch.WordTrace tailWord_5968161 prefixEnd_5968161 3064535216418129276340433 := by
  unfold tailWord_5968161
  simp only [CollatzResearch.WordTrace]
  refine ⟨217676714531379452594824337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145117809687586301729882891 217676714531379452594824337)
  ·
    refine ⟨163257535898534589446118253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217676714531379452594824337 163257535898534589446118253)
    ·
      refine ⟨61221575961950471042294345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163257535898534589446118253 61221575961950471042294345)
      ·
        refine ⟨45916181971462853281720759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61221575961950471042294345 45916181971462853281720759)
        ·
          refine ⟨68874272957194279922581139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45916181971462853281720759 68874272957194279922581139)
          ·
            refine ⟨103311409435791419883871709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68874272957194279922581139 103311409435791419883871709)
            ·
              refine ⟨38741778538421782456451891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103311409435791419883871709 38741778538421782456451891)
              ·
                refine ⟨58112667807632673684677837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38741778538421782456451891 58112667807632673684677837)
                ·
                  refine ⟨21792250427862252631754189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58112667807632673684677837 21792250427862252631754189)
                  ·
                    refine ⟨8172093910448344736907821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21792250427862252631754189 8172093910448344736907821)
                    ·
                      refine ⟨3064535216418129276340433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172093910448344736907821 3064535216418129276340433)
                      ·
                        rfl

theorem cell23_5968161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_5968161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968161 prefixEnd_5968161 := by exact prefixLift 5968161
  have htrace : WordTrace (prefixWord ++ tailWord_5968161) baseStart_5968161 baseEnd_5968161 := by
    simpa [prefixWord, tailWord_5968161, baseEnd_5968161] using wordTrace_append hprefix tailTrace_5968161
  have hstable : (prefixWord ++ tailWord_5968161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968161).length < 2 ^ (prefixWord ++ tailWord_5968161).sum := by decide
  have hdescent : baseEnd_5968161 < baseStart_5968161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968165 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 1, 1, 5]
def baseStart_5968165 : Nat := 118140960795 + 5968165 * 2 ^ 59
def prefixEnd_5968165 : Nat := 4983230072969 + 3 ^ 40 * 5968165 * 2
def baseEnd_5968165 : Nat := 3064537270340747260690415

theorem tailTrace_5968165 : CollatzResearch.WordTrace tailWord_5968165 prefixEnd_5968165 3064537270340747260690415 := by
  unfold tailWord_5968165
  simp only [CollatzResearch.WordTrace]
  refine ⟨217676860423364961277969949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145117906948909974185313299 217676860423364961277969949)
  ·
    refine ⟨81628822658761860479238731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 217676860423364961277969949 81628822658761860479238731)
    ·
      refine ⟨122443233988142790718858097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81628822658761860479238731 122443233988142790718858097)
      ·
        refine ⟨91832425491107093039143573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122443233988142790718858097 91832425491107093039143573)
        ·
          refine ⟨4304644944895644986209855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91832425491107093039143573 4304644944895644986209855)
          ·
            refine ⟨6456967417343467479314783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304644944895644986209855 6456967417343467479314783)
            ·
              refine ⟨9685451126015201218972175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456967417343467479314783 9685451126015201218972175)
              ·
                refine ⟨14528176689022801828458263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9685451126015201218972175 14528176689022801828458263)
                ·
                  refine ⟨21792265033534202742687395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14528176689022801828458263 21792265033534202742687395)
                  ·
                    refine ⟨32688397550301304114031093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21792265033534202742687395 32688397550301304114031093)
                    ·
                      refine ⟨3064537270340747260690415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32688397550301304114031093 3064537270340747260690415)
                      ·
                        rfl

theorem cell23_5968165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_5968165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968165 prefixEnd_5968165 := by exact prefixLift 5968165
  have htrace : WordTrace (prefixWord ++ tailWord_5968165) baseStart_5968165 baseEnd_5968165 := by
    simpa [prefixWord, tailWord_5968165, baseEnd_5968165] using wordTrace_append hprefix tailTrace_5968165
  have hstable : (prefixWord ++ tailWord_5968165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968165).length < 2 ^ (prefixWord ++ tailWord_5968165).sum := by decide
  have hdescent : baseEnd_5968165 < baseStart_5968165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968173 : List Nat := [1, 5, 3, 1, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5968173 : Nat := 118140960795 + 5968173 * 2 ^ 59
def prefixEnd_5968173 : Nat := 4983230072969 + 3 ^ 40 * 5968173 * 2
def baseEnd_5968173 : Nat := 3064541378185983229390379

theorem tailTrace_5968173 : CollatzResearch.WordTrace tailWord_5968173 prefixEnd_5968173 3064541378185983229390379 := by
  unfold tailWord_5968173
  simp only [CollatzResearch.WordTrace]
  refine ⟨217677152207335978644261173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145118101471557319096174115 217677152207335978644261173)
  ·
    refine ⟨20407233019437747997899485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217677152207335978644261173 20407233019437747997899485)
    ·
      refine ⟨7652712382289155499212307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20407233019437747997899485 7652712382289155499212307)
      ·
        refine ⟨11479068573433733248818461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7652712382289155499212307 11479068573433733248818461)
        ·
          refine ⟨4304650715037649968306923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11479068573433733248818461 4304650715037649968306923)
          ·
            refine ⟨6456976072556474952460385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304650715037649968306923 6456976072556474952460385)
            ·
              refine ⟨4842732054417356214345289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6456976072556474952460385 4842732054417356214345289)
              ·
                refine ⟨3632049040813017160758967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4842732054417356214345289 3632049040813017160758967)
                ·
                  refine ⟨5448073561219525741138451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632049040813017160758967 5448073561219525741138451)
                  ·
                    refine ⟨8172110341829288611707677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5448073561219525741138451 8172110341829288611707677)
                    ·
                      refine ⟨3064541378185983229390379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172110341829288611707677 3064541378185983229390379)
                      ·
                        rfl

theorem cell23_5968173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5968173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968173 prefixEnd_5968173 := by exact prefixLift 5968173
  have htrace : WordTrace (prefixWord ++ tailWord_5968173) baseStart_5968173 baseEnd_5968173 := by
    simpa [prefixWord, tailWord_5968173, baseEnd_5968173] using wordTrace_append hprefix tailTrace_5968173
  have hstable : (prefixWord ++ tailWord_5968173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968173).length < 2 ^ (prefixWord ++ tailWord_5968173).sum := by decide
  have hdescent : baseEnd_5968173 < baseStart_5968173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968188 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_5968188 : Nat := 118140960795 + 5968188 * 2 ^ 59
def prefixEnd_5968188 : Nat := 4983230072969 + 3 ^ 40 * 5968188 * 2
def baseEnd_5968188 : Nat := 3064549080395800670702809

theorem tailTrace_5968188 : CollatzResearch.WordTrace tailWord_5968188 prefixEnd_5968188 3064549080395800670702809 := by
  unfold tailWord_5968188
  simp only [CollatzResearch.WordTrace]
  refine ⟨108838849651140818103028609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145118466201521090804038145 108838849651140818103028609)
  ·
    refine ⟨81629137238355613577271457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108838849651140818103028609 81629137238355613577271457)
    ·
      refine ⟨61221852928766710182953593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81629137238355613577271457 61221852928766710182953593)
      ·
        refine ⟨45916389696575032637215195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61221852928766710182953593 45916389696575032637215195)
        ·
          refine ⟨68874584544862548955822793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45916389696575032637215195 68874584544862548955822793)
          ·
            refine ⟨51655938408646911716867095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68874584544862548955822793 51655938408646911716867095)
            ·
              refine ⟨77483907612970367575300643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51655938408646911716867095 77483907612970367575300643)
              ·
                refine ⟨116225861419455551362950965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77483907612970367575300643 116225861419455551362950965)
                ·
                  refine ⟨10896174508073957940276653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116225861419455551362950965 10896174508073957940276653)
                  ·
                    refine ⟨4086065440527734227603745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10896174508073957940276653 4086065440527734227603745)
                    ·
                      refine ⟨3064549080395800670702809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4086065440527734227603745 3064549080395800670702809)
                      ·
                        rfl

theorem cell23_5968188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_5968188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968188 prefixEnd_5968188 := by exact prefixLift 5968188
  have htrace : WordTrace (prefixWord ++ tailWord_5968188) baseStart_5968188 baseEnd_5968188 := by
    simpa [prefixWord, tailWord_5968188, baseEnd_5968188] using wordTrace_append hprefix tailTrace_5968188
  have hstable : (prefixWord ++ tailWord_5968188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968188).length < 2 ^ (prefixWord ++ tailWord_5968188).sum := by decide
  have hdescent : baseEnd_5968188 < baseStart_5968188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968246 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5968246 : Nat := 118140960795 + 5968246 * 2 ^ 59
def prefixEnd_5968246 : Nat := 4983230072969 + 3 ^ 40 * 5968246 * 2
def baseEnd_5968246 : Nat := 3064578862273761443777543

theorem tailTrace_5968246 : CollatzResearch.WordTrace tailWord_5968246 prefixEnd_5968246 3064578862273761443777543 := by
  unfold tailWord_5968246
  simp only [CollatzResearch.WordTrace]
  refine ⟨13604988421004469506979287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145119876490714341407779061 13604988421004469506979287)
  ·
    refine ⟨20407482631506704260468931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13604988421004469506979287 20407482631506704260468931)
    ·
      refine ⟨30611223947260056390703397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20407482631506704260468931 30611223947260056390703397)
      ·
        refine ⟨5739604490111260573256887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30611223947260056390703397 5739604490111260573256887)
        ·
          refine ⟨8609406735166890859885331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739604490111260573256887 8609406735166890859885331)
          ·
            refine ⟨12914110102750336289827997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8609406735166890859885331 12914110102750336289827997)
            ·
              refine ⟨4842791288531376108685499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12914110102750336289827997 4842791288531376108685499)
              ·
                refine ⟨7264186932797064163028249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842791288531376108685499 7264186932797064163028249)
                ·
                  refine ⟨5448140199597798122271187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7264186932797064163028249 5448140199597798122271187)
                  ·
                    refine ⟨8172210299396697183406781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5448140199597798122271187 8172210299396697183406781)
                    ·
                      refine ⟨3064578862273761443777543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172210299396697183406781 3064578862273761443777543)
                      ·
                        rfl

theorem cell23_5968246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5968246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968246 prefixEnd_5968246 := by exact prefixLift 5968246
  have htrace : WordTrace (prefixWord ++ tailWord_5968246) baseStart_5968246 baseEnd_5968246 := by
    simpa [prefixWord, tailWord_5968246, baseEnd_5968246] using wordTrace_append hprefix tailTrace_5968246
  have hstable : (prefixWord ++ tailWord_5968246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968246).length < 2 ^ (prefixWord ++ tailWord_5968246).sum := by decide
  have hdescent : baseEnd_5968246 < baseStart_5968246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968281 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_5968281 : Nat := 118140960795 + 5968281 * 2 ^ 59
def prefixEnd_5968281 : Nat := 4983230072969 + 3 ^ 40 * 5968281 * 2
def baseEnd_5968281 : Nat := 3064596834096668806839881

theorem tailTrace_5968281 : CollatzResearch.WordTrace tailWord_5968281 prefixEnd_5968281 3064596834096668806839881 := by
  unfold tailWord_5968281
  simp only [CollatzResearch.WordTrace]
  refine ⟨217681091290944713089192697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145120727527296475392795131 217681091290944713089192697)
  ·
    refine ⟨163260818468208534816894523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217681091290944713089192697 163260818468208534816894523)
    ·
      refine ⟨244891227702312802225341785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163260818468208534816894523 244891227702312802225341785)
      ·
        refine ⟨183668420776734601669006339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244891227702312802225341785 183668420776734601669006339)
        ·
          refine ⟨275502631165101902503509509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183668420776734601669006339 275502631165101902503509509)
          ·
            refine ⟨51656743343456606719408033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 275502631165101902503509509 51656743343456606719408033)
            ·
              refine ⟨38742557507592455039556025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51656743343456606719408033 38742557507592455039556025)
              ·
                refine ⟨29056918130694341279667019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38742557507592455039556025 29056918130694341279667019)
                ·
                  refine ⟨43585377196041511919500529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29056918130694341279667019 43585377196041511919500529)
                  ·
                    refine ⟨32689032897031133939625397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43585377196041511919500529 32689032897031133939625397)
                    ·
                      refine ⟨3064596834096668806839881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32689032897031133939625397 3064596834096668806839881)
                      ·
                        rfl

theorem cell23_5968281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_5968281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968281 prefixEnd_5968281 := by exact prefixLift 5968281
  have htrace : WordTrace (prefixWord ++ tailWord_5968281) baseStart_5968281 baseEnd_5968281 := by
    simpa [prefixWord, tailWord_5968281, baseEnd_5968281] using wordTrace_append hprefix tailTrace_5968281
  have hstable : (prefixWord ++ tailWord_5968281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968281).length < 2 ^ (prefixWord ++ tailWord_5968281).sum := by decide
  have hdescent : baseEnd_5968281 < baseStart_5968281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968288 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 2, 5]
def baseStart_5968288 : Nat := 118140960795 + 5968288 * 2 ^ 59
def prefixEnd_5968288 : Nat := 4983230072969 + 3 ^ 40 * 5968288 * 2
def baseEnd_5968288 : Nat := 1021533476153750093150783

theorem tailTrace_5968288 : CollatzResearch.WordTrace tailWord_5968288 prefixEnd_5968288 1021533476153750093150783 := by
  unfold tailWord_5968288
  simp only [CollatzResearch.WordTrace]
  refine ⟨108840673300959676642348759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145120897734612902189798345 108840673300959676642348759)
  ·
    refine ⟨163261009951439514963523139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108840673300959676642348759 163261009951439514963523139)
    ·
      refine ⟨244891514927159272445284709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163261009951439514963523139 244891514927159272445284709)
      ·
        refine ⟨45917159048842363583490883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244891514927159272445284709 45917159048842363583490883)
        ·
          refine ⟨68875738573263545375236325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45917159048842363583490883 68875738573263545375236325)
          ·
            refine ⟨12914200982486914757856811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68875738573263545375236325 12914200982486914757856811)
            ·
              refine ⟨19371301473730372136785217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12914200982486914757856811 19371301473730372136785217)
              ·
                refine ⟨14528476105297779102588913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19371301473730372136785217 14528476105297779102588913)
                ·
                  refine ⟨10896357078973334326941685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14528476105297779102588913 10896357078973334326941685)
                  ·
                    refine ⟨1021533476153750093150783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10896357078973334326941685 1021533476153750093150783)
                    ·
                      rfl

theorem cell23_5968288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_5968288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968288 prefixEnd_5968288 := by exact prefixLift 5968288
  have htrace : WordTrace (prefixWord ++ tailWord_5968288) baseStart_5968288 baseEnd_5968288 := by
    simpa [prefixWord, tailWord_5968288, baseEnd_5968288] using wordTrace_append hprefix tailTrace_5968288
  have hstable : (prefixWord ++ tailWord_5968288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968288).length < 2 ^ (prefixWord ++ tailWord_5968288).sum := by decide
  have hdescent : baseEnd_5968288 < baseStart_5968288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968335 : List Nat := [1, 1, 2, 1, 1, 4, 1, 7, 1, 4]
def baseStart_5968335 : Nat := 118140960795 + 5968335 * 2 ^ 59
def prefixEnd_5968335 : Nat := 4983230072969 + 3 ^ 40 * 5968335 * 2
def baseEnd_5968335 : Nat := 1021541520684003865188211

theorem tailTrace_5968335 : CollatzResearch.WordTrace tailWord_5968335 prefixEnd_5968335 1021541520684003865188211 := by
  unfold tailWord_5968335
  simp only [CollatzResearch.WordTrace]
  refine ⟨217683060832749080311658459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145122040555166053541105639 217683060832749080311658459)
  ·
    refine ⟨326524591249123620467487689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217683060832749080311658459 326524591249123620467487689)
    ·
      refine ⟨244893443436842715350615767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 326524591249123620467487689 244893443436842715350615767)
      ·
        refine ⟨367340165155264073025923651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244893443436842715350615767 367340165155264073025923651)
        ·
          refine ⟨551010247732896109538885477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367340165155264073025923651 551010247732896109538885477)
          ·
            refine ⟨103314421449918020538541027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 551010247732896109538885477 103314421449918020538541027)
            ·
              refine ⟨154971632174877030807811541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103314421449918020538541027 154971632174877030807811541)
              ·
                refine ⟨3632147629098680409558083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154971632174877030807811541 3632147629098680409558083)
                ·
                  refine ⟨5448221443648020614337125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632147629098680409558083 5448221443648020614337125)
                  ·
                    refine ⟨1021541520684003865188211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5448221443648020614337125 1021541520684003865188211)
                    ·
                      rfl

theorem cell23_5968335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 4].length) (baseStart_5968335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968335 prefixEnd_5968335 := by exact prefixLift 5968335
  have htrace : WordTrace (prefixWord ++ tailWord_5968335) baseStart_5968335 baseEnd_5968335 := by
    simpa [prefixWord, tailWord_5968335, baseEnd_5968335] using wordTrace_append hprefix tailTrace_5968335
  have hstable : (prefixWord ++ tailWord_5968335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968335).length < 2 ^ (prefixWord ++ tailWord_5968335).sum := by decide
  have hdescent : baseEnd_5968335 < baseStart_5968335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968342 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_5968342 : Nat := 118140960795 + 5968342 * 2 ^ 59
def prefixEnd_5968342 : Nat := 4983230072969 + 3 ^ 40 * 5968342 * 2
def baseEnd_5968342 : Nat := 3064628156416593068177101

theorem tailTrace_5968342 : CollatzResearch.WordTrace tailWord_5968342 prefixEnd_5968342 3064628156416593068177101 := by
  unfold tailWord_5968342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605207258982732531697705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145122210762482480338108853 13605207258982732531697705)
  ·
    refine ⟨10203905444237049398773279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13605207258982732531697705 10203905444237049398773279)
    ·
      refine ⟨15305858166355574098159919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10203905444237049398773279 15305858166355574098159919)
      ·
        refine ⟨22958787249533361147239879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15305858166355574098159919 22958787249533361147239879)
        ·
          refine ⟨34438180874300041720859819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22958787249533361147239879 34438180874300041720859819)
          ·
            refine ⟨51657271311450062581289729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34438180874300041720859819 51657271311450062581289729)
            ·
              refine ⟨38742953483587546935967297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51657271311450062581289729 38742953483587546935967297)
              ·
                refine ⟨29057215112690660201975473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38742953483587546935967297 29057215112690660201975473)
                ·
                  refine ⟨21792911334517995151481605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29057215112690660201975473 21792911334517995151481605)
                  ·
                    refine ⟨4086170875222124090902801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21792911334517995151481605 4086170875222124090902801)
                    ·
                      refine ⟨3064628156416593068177101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4086170875222124090902801 3064628156416593068177101)
                      ·
                        rfl

theorem cell23_5968342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_5968342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968342 prefixEnd_5968342 := by exact prefixLift 5968342
  have htrace : WordTrace (prefixWord ++ tailWord_5968342) baseStart_5968342 baseEnd_5968342 := by
    simpa [prefixWord, tailWord_5968342, baseEnd_5968342] using wordTrace_append hprefix tailTrace_5968342
  have hstable : (prefixWord ++ tailWord_5968342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968342).length < 2 ^ (prefixWord ++ tailWord_5968342).sum := by decide
  have hdescent : baseEnd_5968342 < baseStart_5968342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968365 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 6]
def baseStart_5968365 : Nat := 118140960795 + 5968365 * 2 ^ 59
def prefixEnd_5968365 : Nat := 4983230072969 + 3 ^ 40 * 5968365 * 2
def baseEnd_5968365 : Nat := 340515551830182942021055

theorem tailTrace_5968365 : CollatzResearch.WordTrace tailWord_5968365 prefixEnd_5968365 340515551830182942021055 := by
  unfold tailWord_5968365
  simp only [CollatzResearch.WordTrace]
  refine ⟨217684155022640395435250549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145122770015093596956833699 217684155022640395435250549)
  ·
    refine ⟨20407889533372537072054739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 217684155022640395435250549 20407889533372537072054739)
    ·
      refine ⟨30611834300058805608082109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20407889533372537072054739 30611834300058805608082109)
      ·
        refine ⟨11479437862522052103030791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30611834300058805608082109 11479437862522052103030791)
        ·
          refine ⟨17219156793783078154546187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11479437862522052103030791 17219156793783078154546187)
          ·
            refine ⟨25828735190674617231819281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17219156793783078154546187 25828735190674617231819281)
            ·
              refine ⟨19371551393005962923864461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25828735190674617231819281 19371551393005962923864461)
              ·
                refine ⟨7264331772377236096449173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19371551393005962923864461 7264331772377236096449173)
                ·
                  refine ⟨340515551830182942021055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7264331772377236096449173 340515551830182942021055)
                  ·
                    rfl

theorem cell23_5968365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_5968365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968365 prefixEnd_5968365 := by exact prefixLift 5968365
  have htrace : WordTrace (prefixWord ++ tailWord_5968365) baseStart_5968365 baseEnd_5968365 := by
    simpa [prefixWord, tailWord_5968365, baseEnd_5968365] using wordTrace_append hprefix tailTrace_5968365
  have hstable : (prefixWord ++ tailWord_5968365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968365).length < 2 ^ (prefixWord ++ tailWord_5968365).sum := by decide
  have hdescent : baseEnd_5968365 < baseStart_5968365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968371 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 7]
def baseStart_5968371 : Nat := 118140960795 + 5968371 * 2 ^ 59
def prefixEnd_5968371 : Nat := 4983230072969 + 3 ^ 40 * 5968371 * 2
def baseEnd_5968371 : Nat := 3064643047355573454714467

theorem tailTrace_5968371 : CollatzResearch.WordTrace tailWord_5968371 prefixEnd_5968371 3064643047355573454714467 := by
  unfold tailWord_5968371
  simp only [CollatzResearch.WordTrace]
  refine ⟨217684373860618658459968967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145122915907079105639979311 217684373860618658459968967)
  ·
    refine ⟨326526560790927987689953451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217684373860618658459968967 326526560790927987689953451)
    ·
      refine ⟨489789841186391981534930177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326526560790927987689953451 489789841186391981534930177)
      ·
        refine ⟨367342380889793986151197633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489789841186391981534930177 367342380889793986151197633)
        ·
          refine ⟨275506785667345489613398225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367342380889793986151197633 275506785667345489613398225)
          ·
            refine ⟨206630089250509117210048669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275506785667345489613398225 206630089250509117210048669)
            ·
              refine ⟨77486283468940918953768251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206630089250509117210048669 77486283468940918953768251)
              ·
                refine ⟨116229425203411378430652377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77486283468940918953768251 116229425203411378430652377)
                ·
                  refine ⟨87172068902558533822989283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116229425203411378430652377 87172068902558533822989283)
                  ·
                    refine ⟨130758103353837800734483925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 87172068902558533822989283 130758103353837800734483925)
                    ·
                      refine ⟨3064643047355573454714467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 130758103353837800734483925 3064643047355573454714467)
                      ·
                        rfl

theorem cell23_5968371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_5968371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968371 prefixEnd_5968371 := by exact prefixLift 5968371
  have htrace : WordTrace (prefixWord ++ tailWord_5968371) baseStart_5968371 baseEnd_5968371 := by
    simpa [prefixWord, tailWord_5968371, baseEnd_5968371] using wordTrace_append hprefix tailTrace_5968371
  have hstable : (prefixWord ++ tailWord_5968371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968371).length < 2 ^ (prefixWord ++ tailWord_5968371).sum := by decide
  have hdescent : baseEnd_5968371 < baseStart_5968371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968386 : List Nat := [3, 4, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_5968386 : Nat := 118140960795 + 5968386 * 2 ^ 59
def prefixEnd_5968386 : Nat := 4983230072969 + 3 ^ 40 * 5968386 * 2
def baseEnd_5968386 : Nat := 1021550249855130298675633

theorem tailTrace_5968386 : CollatzResearch.WordTrace tailWord_5968386 prefixEnd_5968386 1021550249855130298675633 := by
  unfold tailWord_5968386
  simp only [CollatzResearch.WordTrace]
  refine ⟨54421230238891079005441253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145123280637042877347843341 54421230238891079005441253)
  ·
    refine ⟨10203980669792077313520235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54421230238891079005441253 10203980669792077313520235)
    ·
      refine ⟨15305971004688115970280353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10203980669792077313520235 15305971004688115970280353)
      ·
        refine ⟨11479478253516086977710265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15305971004688115970280353 11479478253516086977710265)
        ·
          refine ⟨8609608690137065233282699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11479478253516086977710265 8609608690137065233282699)
          ·
            refine ⟨12914413035205597849924049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8609608690137065233282699 12914413035205597849924049)
            ·
              refine ⟨9685809776404198387443037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12914413035205597849924049 9685809776404198387443037)
              ·
                refine ⟨3632178666151574395291139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9685809776404198387443037 3632178666151574395291139)
                ·
                  refine ⟨5448267999227361592936709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632178666151574395291139 5448267999227361592936709)
                  ·
                    refine ⟨1021550249855130298675633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5448267999227361592936709 1021550249855130298675633)
                    ·
                      rfl

theorem cell23_5968386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_5968386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968386 prefixEnd_5968386 := by exact prefixLift 5968386
  have htrace : WordTrace (prefixWord ++ tailWord_5968386) baseStart_5968386 baseEnd_5968386 := by
    simpa [prefixWord, tailWord_5968386, baseEnd_5968386] using wordTrace_append hprefix tailTrace_5968386
  have hstable : (prefixWord ++ tailWord_5968386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968386).length < 2 ^ (prefixWord ++ tailWord_5968386).sum := by decide
  have hdescent : baseEnd_5968386 < baseStart_5968386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968395 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 1, 5]
def baseStart_5968395 : Nat := 118140960795 + 5968395 * 2 ^ 59
def prefixEnd_5968395 : Nat := 4983230072969 + 3 ^ 40 * 5968395 * 2
def baseEnd_5968395 : Nat := 1021551790297093786938119

theorem tailTrace_5968395 : CollatzResearch.WordTrace tailWord_5968395 prefixEnd_5968395 1021551790297093786938119 := by
  unfold tailWord_5968395
  simp only [CollatzResearch.WordTrace]
  refine ⟨217685249212531710558842639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145123499475021140372561759 217685249212531710558842639)
  ·
    refine ⟨326527873818797565838263959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217685249212531710558842639 326527873818797565838263959)
    ·
      refine ⟨489791810728196348757395939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326527873818797565838263959 489791810728196348757395939)
      ·
        refine ⟨734687716092294523136093909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489791810728196348757395939 734687716092294523136093909)
        ·
          refine ⟨17219243345913152886002201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 734687716092294523136093909 17219243345913152886002201)
          ·
            refine ⟨12914432509434864664501651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17219243345913152886002201 12914432509434864664501651)
            ·
              refine ⟨19371648764152296996752477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12914432509434864664501651 19371648764152296996752477)
              ·
                refine ⟨7264368286557111373782179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19371648764152296996752477 7264368286557111373782179)
                ·
                  refine ⟨10896552429835667060673269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7264368286557111373782179 10896552429835667060673269)
                  ·
                    refine ⟨1021551790297093786938119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10896552429835667060673269 1021551790297093786938119)
                    ·
                      rfl

theorem cell23_5968395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 5].length) (baseStart_5968395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968395 prefixEnd_5968395 := by exact prefixLift 5968395
  have htrace : WordTrace (prefixWord ++ tailWord_5968395) baseStart_5968395 baseEnd_5968395 := by
    simpa [prefixWord, tailWord_5968395, baseEnd_5968395] using wordTrace_append hprefix tailTrace_5968395
  have hstable : (prefixWord ++ tailWord_5968395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968395).length < 2 ^ (prefixWord ++ tailWord_5968395).sum := by decide
  have hdescent : baseEnd_5968395 < baseStart_5968395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968432 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 3, 2, 2]
def baseStart_5968432 : Nat := 118140960795 + 5968432 * 2 ^ 59
def prefixEnd_5968432 : Nat := 4983230072969 + 3 ^ 40 * 5968432 * 2
def baseEnd_5968432 : Nat := 3064674369675497716051687

theorem tailTrace_5968432 : CollatzResearch.WordTrace tailWord_5968432 prefixEnd_5968432 3064674369675497716051687 := by
  unfold tailWord_5968432
  simp only [CollatzResearch.WordTrace]
  refine ⟨108843299356698832938969775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145124399142265110585293033 108843299356698832938969775)
  ·
    refine ⟨163264949035048249408454663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108843299356698832938969775 163264949035048249408454663)
    ·
      refine ⟨244897423552572374112681995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163264949035048249408454663 244897423552572374112681995)
      ·
        refine ⟨367346135328858561169022993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244897423552572374112681995 367346135328858561169022993)
        ·
          refine ⟨275509601496643920876767245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367346135328858561169022993 275509601496643920876767245)
          ·
            refine ⟨103316100561241470328787717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275509601496643920876767245 103316100561241470328787717)
            ·
              refine ⟨19371768855232775686647697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103316100561241470328787717 19371768855232775686647697)
              ·
                refine ⟨14528826641424581764985773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19371768855232775686647697 14528826641424581764985773)
                ·
                  refine ⟨5448309990534218161869665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14528826641424581764985773 5448309990534218161869665)
                  ·
                    refine ⟨4086232492900663621402249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5448309990534218161869665 4086232492900663621402249)
                    ·
                      refine ⟨3064674369675497716051687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4086232492900663621402249 3064674369675497716051687)
                      ·
                        rfl

theorem cell23_5968432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 3, 2, 2].length) (baseStart_5968432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968432 prefixEnd_5968432 := by exact prefixLift 5968432
  have htrace : WordTrace (prefixWord ++ tailWord_5968432) baseStart_5968432 baseEnd_5968432 := by
    simpa [prefixWord, tailWord_5968432, baseEnd_5968432] using wordTrace_append hprefix tailTrace_5968432
  have hstable : (prefixWord ++ tailWord_5968432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968432).length < 2 ^ (prefixWord ++ tailWord_5968432).sum := by decide
  have hdescent : baseEnd_5968432 < baseStart_5968432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968476 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5968476 : Nat := 118140960795 + 5968476 * 2 ^ 59
def prefixEnd_5968476 : Nat := 4983230072969 + 3 ^ 40 * 5968476 * 2
def baseEnd_5968476 : Nat := 1021565654274765181300495

theorem tailTrace_5968476 : CollatzResearch.WordTrace tailWord_5968476 prefixEnd_5968476 1021565654274765181300495 := by
  unfold tailWord_5968476
  simp only [CollatzResearch.WordTrace]
  refine ⟨108844101762619130696270641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145125469016825507595027521 108844101762619130696270641)
  ·
    refine ⟨81633076321964348022202981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108844101762619130696270641 81633076321964348022202981)
    ·
      refine ⟨15306201810368315254163059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81633076321964348022202981 15306201810368315254163059)
      ·
        refine ⟨22959302715552472881244589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15306201810368315254163059 22959302715552472881244589)
        ·
          refine ⟨8609738518332177330466721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22959302715552472881244589 8609738518332177330466721)
          ·
            refine ⟨6457303888749132997850041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8609738518332177330466721 6457303888749132997850041)
            ·
              refine ⟨4842977916561849748387531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6457303888749132997850041 4842977916561849748387531)
              ·
                refine ⟨7264466874842774622581297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842977916561849748387531 7264466874842774622581297)
                ·
                  refine ⟨5448350156132080966935973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7264466874842774622581297 5448350156132080966935973)
                  ·
                    refine ⟨1021565654274765181300495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5448350156132080966935973 1021565654274765181300495)
                    ·
                      rfl

theorem cell23_5968476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5968476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968476 prefixEnd_5968476 := by exact prefixLift 5968476
  have htrace : WordTrace (prefixWord ++ tailWord_5968476) baseStart_5968476 baseEnd_5968476 := by
    simpa [prefixWord, tailWord_5968476, baseEnd_5968476] using wordTrace_append hprefix tailTrace_5968476
  have hstable : (prefixWord ++ tailWord_5968476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968476).length < 2 ^ (prefixWord ++ tailWord_5968476).sum := by decide
  have hdescent : baseEnd_5968476 < baseStart_5968476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968532 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_5968532 : Nat := 118140960795 + 5968532 * 2 ^ 59
def prefixEnd_5968532 : Nat := 4983230072969 + 3 ^ 40 * 5968532 * 2
def baseEnd_5968532 : Nat := 1021575239246982441600409

theorem tailTrace_5968532 : CollatzResearch.WordTrace tailWord_5968532 prefixEnd_5968532 1021575239246982441600409 := by
  unfold tailWord_5968532
  simp only [CollatzResearch.WordTrace]
  refine ⟨108845123006517691478289925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145126830675356921971053233 108845123006517691478289925)
  ·
    refine ⟨20408460563722067152179361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108845123006517691478289925 20408460563722067152179361)
    ·
      refine ⟨15306345422791550364134521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20408460563722067152179361 15306345422791550364134521)
      ·
        refine ⟨11479759067093662773100891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15306345422791550364134521 11479759067093662773100891)
        ·
          refine ⟨17219638600640494159651337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11479759067093662773100891 17219638600640494159651337)
          ·
            refine ⟨12914728950480370619738503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17219638600640494159651337 12914728950480370619738503)
            ·
              refine ⟨19372093425720555929607755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12914728950480370619738503 19372093425720555929607755)
              ·
                refine ⟨29058140138580833894411633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19372093425720555929607755 29058140138580833894411633)
                ·
                  refine ⟨21793605103935625420808725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29058140138580833894411633 21793605103935625420808725)
                  ·
                    refine ⟨1021575239246982441600409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21793605103935625420808725 1021575239246982441600409)
                    ·
                      rfl

theorem cell23_5968532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_5968532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968532 prefixEnd_5968532 := by exact prefixLift 5968532
  have htrace : WordTrace (prefixWord ++ tailWord_5968532) baseStart_5968532 baseEnd_5968532 := by
    simpa [prefixWord, tailWord_5968532, baseEnd_5968532] using wordTrace_append hprefix tailTrace_5968532
  have hstable : (prefixWord ++ tailWord_5968532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968532).length < 2 ^ (prefixWord ++ tailWord_5968532).sum := by decide
  have hdescent : baseEnd_5968532 < baseStart_5968532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968535 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_5968535 : Nat := 118140960795 + 5968535 * 2 ^ 59
def prefixEnd_5968535 : Nat := 4983230072969 + 3 ^ 40 * 5968535 * 2
def baseEnd_5968535 : Nat := 3064727258182910813063713

theorem tailTrace_5968535 : CollatzResearch.WordTrace tailWord_5968535 prefixEnd_5968535 3064727258182910813063713 := by
  unfold tailWord_5968535
  simp only [CollatzResearch.WordTrace]
  refine ⟨217690355432024514468939059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145126903621349676312626039 217690355432024514468939059)
  ·
    refine ⟨326535533148036771703408589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217690355432024514468939059 326535533148036771703408589)
    ·
      refine ⟨122450824930513789388778221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326535533148036771703408589 122450824930513789388778221)
      ·
        refine ⟨45919059348942671020791833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122450824930513789388778221 45919059348942671020791833)
        ·
          refine ⟨34439294511707003265593875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45919059348942671020791833 34439294511707003265593875)
          ·
            refine ⟨51658941767560504898390813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34439294511707003265593875 51658941767560504898390813)
            ·
              refine ⟨19372103162835189336896555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51658941767560504898390813 19372103162835189336896555)
              ·
                refine ⟨29058154744252784005344833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19372103162835189336896555 29058154744252784005344833)
                ·
                  refine ⟨21793616058189588004008625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29058154744252784005344833 21793616058189588004008625)
                  ·
                    refine ⟨16345212043642191003006469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21793616058189588004008625 16345212043642191003006469)
                    ·
                      refine ⟨3064727258182910813063713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16345212043642191003006469 3064727258182910813063713)
                      ·
                        rfl

theorem cell23_5968535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_5968535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968535 prefixEnd_5968535 := by exact prefixLift 5968535
  have htrace : WordTrace (prefixWord ++ tailWord_5968535) baseStart_5968535 baseEnd_5968535 := by
    simpa [prefixWord, tailWord_5968535, baseEnd_5968535] using wordTrace_append hprefix tailTrace_5968535
  have hstable : (prefixWord ++ tailWord_5968535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968535).length < 2 ^ (prefixWord ++ tailWord_5968535).sum := by decide
  have hdescent : baseEnd_5968535 < baseStart_5968535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968542 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_5968542 : Nat := 118140960795 + 5968542 * 2 ^ 59
def prefixEnd_5968542 : Nat := 4983230072969 + 3 ^ 40 * 5968542 * 2
def baseEnd_5968542 : Nat := 3064730852547492285676181

theorem tailTrace_5968542 : CollatzResearch.WordTrace tailWord_5968542 prefixEnd_5968542 3064730852547492285676181 := by
  unfold tailWord_5968542
  simp only [CollatzResearch.WordTrace]
  refine ⟨27211326342874894333055485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145127073828666103109629253 27211326342874894333055485)
  ·
    refine ⟨10204247378578085374895807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27211326342874894333055485 10204247378578085374895807)
    ·
      refine ⟨15306371067867128062343711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10204247378578085374895807 15306371067867128062343711)
      ·
        refine ⟨22959556601800692093515567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15306371067867128062343711 22959556601800692093515567)
        ·
          refine ⟨34439334902701038140273351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22959556601800692093515567 34439334902701038140273351)
          ·
            refine ⟨51659002354051557210410027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34439334902701038140273351 51659002354051557210410027)
            ·
              refine ⟨77488503531077335815615041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51659002354051557210410027 77488503531077335815615041)
              ·
                refine ⟨58116377648308001861711281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77488503531077335815615041 58116377648308001861711281)
                ·
                  refine ⟨43587283236231001396283461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58116377648308001861711281 43587283236231001396283461)
                  ·
                    refine ⟨8172615606793312761803149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43587283236231001396283461 8172615606793312761803149)
                    ·
                      refine ⟨3064730852547492285676181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172615606793312761803149 3064730852547492285676181)
                      ·
                        rfl

theorem cell23_5968542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_5968542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968542 prefixEnd_5968542 := by exact prefixLift 5968542
  have htrace : WordTrace (prefixWord ++ tailWord_5968542) baseStart_5968542 baseEnd_5968542 := by
    simpa [prefixWord, tailWord_5968542, baseEnd_5968542] using wordTrace_append hprefix tailTrace_5968542
  have hstable : (prefixWord ++ tailWord_5968542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968542).length < 2 ^ (prefixWord ++ tailWord_5968542).sum := by decide
  have hdescent : baseEnd_5968542 < baseStart_5968542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968632 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_5968632 : Nat := 118140960795 + 5968632 * 2 ^ 59
def prefixEnd_5968632 : Nat := 4983230072969 + 3 ^ 40 * 5968632 * 2
def baseEnd_5968632 : Nat := 3064777065806396933550767

theorem tailTrace_5968632 : CollatzResearch.WordTrace tailWord_5968632 prefixEnd_5968632 3064777065806396933550767 := by
  unfold tailWord_5968632
  simp only [CollatzResearch.WordTrace]
  refine ⟨108846946656336550017610075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145129262208448733356813433 108846946656336550017610075)
  ·
    refine ⟨163270419984504825026415113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108846946656336550017610075 163270419984504825026415113)
    ·
      refine ⟨122452814988378618769811335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163270419984504825026415113 122452814988378618769811335)
      ·
        refine ⟨183679222482567928154717003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122452814988378618769811335 183679222482567928154717003)
        ·
          refine ⟨275518833723851892232075505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183679222482567928154717003 275518833723851892232075505)
          ·
            refine ⟨206639125292888919174056629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275518833723851892232075505 206639125292888919174056629)
            ·
              refine ⟨19372417996208336172567809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 206639125292888919174056629 19372417996208336172567809)
              ·
                refine ⟨14529313497156252129425857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19372417996208336172567809 14529313497156252129425857)
                ·
                  refine ⟨10896985122867189097069393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14529313497156252129425857 10896985122867189097069393)
                  ·
                    refine ⟨8172738842150391822802045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10896985122867189097069393 8172738842150391822802045)
                    ·
                      refine ⟨3064777065806396933550767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172738842150391822802045 3064777065806396933550767)
                      ·
                        rfl

theorem cell23_5968632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_5968632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968632 prefixEnd_5968632 := by exact prefixLift 5968632
  have htrace : WordTrace (prefixWord ++ tailWord_5968632) baseStart_5968632 baseEnd_5968632 := by
    simpa [prefixWord, tailWord_5968632, baseEnd_5968632] using wordTrace_append hprefix tailTrace_5968632
  have hstable : (prefixWord ++ tailWord_5968632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968632).length < 2 ^ (prefixWord ++ tailWord_5968632).sum := by decide
  have hdescent : baseEnd_5968632 < baseStart_5968632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968689 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 2, 3, 2]
def baseStart_5968689 : Nat := 118140960795 + 5968689 * 2 ^ 59
def prefixEnd_5968689 : Nat := 4983230072969 + 3 ^ 40 * 5968689 * 2
def baseEnd_5968689 : Nat := 3064806334203703210538005

theorem tailTrace_5968689 : CollatzResearch.WordTrace tailWord_5968689 prefixEnd_5968689 3064806334203703210538005 := by
  unfold tailWord_5968689
  simp only [CollatzResearch.WordTrace]
  refine ⟨217695972273466598770045121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145130648182311065846696747 217695972273466598770045121)
  ·
    refine ⟨163271979205099949077533841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217695972273466598770045121 163271979205099949077533841)
    ·
      refine ⟨122453984403824961808150381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163271979205099949077533841 122453984403824961808150381)
      ·
        refine ⟨45920244151434360678056393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122453984403824961808150381 45920244151434360678056393)
        ·
          refine ⟨34440183113575770508542295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45920244151434360678056393 34440183113575770508542295)
          ·
            refine ⟨51660274670363655762813443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34440183113575770508542295 51660274670363655762813443)
            ·
              refine ⟨77490412005545483644220165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51660274670363655762813443 77490412005545483644220165)
              ·
                refine ⟨14529452251039778183291281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77490412005545483644220165 14529452251039778183291281)
                ·
                  refine ⟨10897089188279833637468461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14529452251039778183291281 10897089188279833637468461)
                  ·
                    refine ⟨4086408445604937614050673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10897089188279833637468461 4086408445604937614050673)
                    ·
                      refine ⟨3064806334203703210538005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4086408445604937614050673 3064806334203703210538005)
                      ·
                        rfl

theorem cell23_5968689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_5968689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968689 prefixEnd_5968689 := by exact prefixLift 5968689
  have htrace : WordTrace (prefixWord ++ tailWord_5968689) baseStart_5968689 baseEnd_5968689 := by
    simpa [prefixWord, tailWord_5968689, baseEnd_5968689] using wordTrace_append hprefix tailTrace_5968689
  have hstable : (prefixWord ++ tailWord_5968689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968689).length < 2 ^ (prefixWord ++ tailWord_5968689).sum := by decide
  have hdescent : baseEnd_5968689 < baseStart_5968689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968695 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 3, 6]
def baseStart_5968695 : Nat := 118140960795 + 5968695 * 2 ^ 59
def prefixEnd_5968695 : Nat := 4983230072969 + 3 ^ 40 * 5968695 * 2
def baseEnd_5968695 : Nat := 1021603138362543395687659

theorem tailTrace_5968695 : CollatzResearch.WordTrace tailWord_5968695 prefixEnd_5968695 1021603138362543395687659 := by
  unfold tailWord_5968695
  simp only [CollatzResearch.WordTrace]
  refine ⟨217696191111444861794763539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145130794074296574529842359 217696191111444861794763539)
  ·
    refine ⟨326544286667167292692145309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217696191111444861794763539 326544286667167292692145309)
    ·
      refine ⟨122454107500187734759554491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 326544286667167292692145309 122454107500187734759554491)
      ·
        refine ⟨183681161250281602139331737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122454107500187734759554491 183681161250281602139331737)
        ·
          refine ⟨137760870937711201604498803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183681161250281602139331737 137760870937711201604498803)
          ·
            refine ⟨206641306406566802406748205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137760870937711201604498803 206641306406566802406748205)
            ·
              refine ⟨77490489902462550902530577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206641306406566802406748205 77490489902462550902530577)
              ·
                refine ⟨58117867426846913176897933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77490489902462550902530577 58117867426846913176897933)
                ·
                  refine ⟨21794200285067592441336725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58117867426846913176897933 21794200285067592441336725)
                  ·
                    refine ⟨1021603138362543395687659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21794200285067592441336725 1021603138362543395687659)
                    ·
                      rfl

theorem cell23_5968695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_5968695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968695 prefixEnd_5968695 := by exact prefixLift 5968695
  have htrace : WordTrace (prefixWord ++ tailWord_5968695) baseStart_5968695 baseEnd_5968695 := by
    simpa [prefixWord, tailWord_5968695, baseEnd_5968695] using wordTrace_append hprefix tailTrace_5968695
  have hstable : (prefixWord ++ tailWord_5968695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968695).length < 2 ^ (prefixWord ++ tailWord_5968695).sum := by decide
  have hdescent : baseEnd_5968695 < baseStart_5968695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968696 : List Nat := [2, 1, 2, 1, 3, 2, 3, 4, 1, 1, 3]
def baseStart_5968696 : Nat := 118140960795 + 5968696 * 2 ^ 59
def prefixEnd_5968696 : Nat := 4983230072969 + 3 ^ 40 * 5968696 * 2
def baseEnd_5968696 : Nat := 3064809928568284683150473

theorem tailTrace_5968696 : CollatzResearch.WordTrace tailWord_5968696 prefixEnd_5968696 3064809928568284683150473 := by
  unfold tailWord_5968696
  simp only [CollatzResearch.WordTrace]
  refine ⟨108848113792220619482774971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145130818389627492643699961 108848113792220619482774971)
  ·
    refine ⟨163272170688330929224162457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108848113792220619482774971 163272170688330929224162457)
    ·
      refine ⟨122454128016248196918121843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163272170688330929224162457 122454128016248196918121843)
      ·
        refine ⟨183681192024372295377182765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122454128016248196918121843 183681192024372295377182765)
        ·
          refine ⟨68880447009139610766443537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183681192024372295377182765 68880447009139610766443537)
          ·
            refine ⟨51660335256854708074832653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68880447009139610766443537 51660335256854708074832653)
            ·
              refine ⟨19372625721320515528062245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51660335256854708074832653 19372625721320515528062245)
              ·
                refine ⟨3632367322747596661511671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19372625721320515528062245 3632367322747596661511671)
                ·
                  refine ⟨5448550984121394992267507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632367322747596661511671 5448550984121394992267507)
                  ·
                    refine ⟨8172826476182092488401261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5448550984121394992267507 8172826476182092488401261)
                    ·
                      refine ⟨3064809928568284683150473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172826476182092488401261 3064809928568284683150473)
                      ·
                        rfl

theorem cell23_5968696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 1, 3].length) (baseStart_5968696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968696 prefixEnd_5968696 := by exact prefixLift 5968696
  have htrace : WordTrace (prefixWord ++ tailWord_5968696) baseStart_5968696 baseEnd_5968696 := by
    simpa [prefixWord, tailWord_5968696, baseEnd_5968696] using wordTrace_append hprefix tailTrace_5968696
  have hstable : (prefixWord ++ tailWord_5968696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968696).length < 2 ^ (prefixWord ++ tailWord_5968696).sum := by decide
  have hdescent : baseEnd_5968696 < baseStart_5968696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968712 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 1, 6]
def baseStart_5968712 : Nat := 118140960795 + 5968712 * 2 ^ 59
def prefixEnd_5968712 : Nat := 4983230072969 + 3 ^ 40 * 5968712 * 2
def baseEnd_5968712 : Nat := 1021606048086252206850133

theorem tailTrace_5968712 : CollatzResearch.WordTrace tailWord_5968712 prefixEnd_5968712 1021606048086252206850133 := by
  unfold tailWord_5968712
  simp only [CollatzResearch.WordTrace]
  refine ⟨108848405576191636849066195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145131207434922182465421593 108848405576191636849066195)
  ·
    refine ⟨163272608364287455273599293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108848405576191636849066195 163272608364287455273599293)
    ·
      refine ⟨61227228136607795727599735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 163272608364287455273599293 61227228136607795727599735)
      ·
        refine ⟨91840842204911693591399603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61227228136607795727599735 91840842204911693591399603)
        ·
          refine ⟨137761263307367540387099405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91840842204911693591399603 137761263307367540387099405)
          ·
            refine ⟨51660473740262827645162277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137761263307367540387099405 51660473740262827645162277)
            ·
              refine ⟨9686338826299280183467927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51660473740262827645162277 9686338826299280183467927)
              ·
                refine ⟨14529508239448920275201891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9686338826299280183467927 14529508239448920275201891)
                ·
                  refine ⟨21794262359173380412802837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14529508239448920275201891 21794262359173380412802837)
                  ·
                    refine ⟨1021606048086252206850133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21794262359173380412802837 1021606048086252206850133)
                    ·
                      rfl

theorem cell23_5968712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_5968712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968712 prefixEnd_5968712 := by exact prefixLift 5968712
  have htrace : WordTrace (prefixWord ++ tailWord_5968712) baseStart_5968712 baseEnd_5968712 := by
    simpa [prefixWord, tailWord_5968712, baseEnd_5968712] using wordTrace_append hprefix tailTrace_5968712
  have hstable : (prefixWord ++ tailWord_5968712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968712).length < 2 ^ (prefixWord ++ tailWord_5968712).sum := by decide
  have hdescent : baseEnd_5968712 < baseStart_5968712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968745 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_5968745 : Nat := 118140960795 + 5968745 * 2 ^ 59
def prefixEnd_5968745 : Nat := 4983230072969 + 3 ^ 40 * 5968745 * 2
def baseEnd_5968745 : Nat := 3064835089120354991437747

theorem tailTrace_5968745 : CollatzResearch.WordTrace tailWord_5968745 prefixEnd_5968745 3064835089120354991437747 := by
  unfold tailWord_5968745
  simp only [CollatzResearch.WordTrace]
  refine ⟨217698014761263720334083689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145132009840842480222722459 217698014761263720334083689)
  ·
    refine ⟨163273511070947790250562767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217698014761263720334083689 163273511070947790250562767)
    ·
      refine ⟨244910266606421685375844151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163273511070947790250562767 244910266606421685375844151)
      ·
        refine ⟨367365399909632528063766227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244910266606421685375844151 367365399909632528063766227)
        ·
          refine ⟨551048099864448792095649341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367365399909632528063766227 551048099864448792095649341)
          ·
            refine ⟨206643037449168297035868503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 551048099864448792095649341 206643037449168297035868503)
            ·
              refine ⟨309964556173752445553802755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206643037449168297035868503 309964556173752445553802755)
              ·
                refine ⟨464946834260628668330704133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309964556173752445553802755 464946834260628668330704133)
                ·
                  refine ⟨87177531423867875312007025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 464946834260628668330704133 87177531423867875312007025)
                  ·
                    refine ⟨65383148567900906484005269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87177531423867875312007025 65383148567900906484005269)
                    ·
                      refine ⟨3064835089120354991437747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65383148567900906484005269 3064835089120354991437747)
                      ·
                        rfl

theorem cell23_5968745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_5968745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968745 prefixEnd_5968745 := by exact prefixLift 5968745
  have htrace : WordTrace (prefixWord ++ tailWord_5968745) baseStart_5968745 baseEnd_5968745 := by
    simpa [prefixWord, tailWord_5968745, baseEnd_5968745] using wordTrace_append hprefix tailTrace_5968745
  have hstable : (prefixWord ++ tailWord_5968745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968745).length < 2 ^ (prefixWord ++ tailWord_5968745).sum := by decide
  have hdescent : baseEnd_5968745 < baseStart_5968745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968752 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3]
def baseStart_5968752 : Nat := 118140960795 + 5968752 * 2 ^ 59
def prefixEnd_5968752 : Nat := 4983230072969 + 3 ^ 40 * 5968752 * 2
def baseEnd_5968752 : Nat := 3064838683484936464050215

theorem tailTrace_5968752 : CollatzResearch.WordTrace tailWord_5968752 prefixEnd_5968752 3064838683484936464050215 := by
  unfold tailWord_5968752
  simp only [CollatzResearch.WordTrace]
  refine ⟨108849135036119180264794255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145132180048158907019725673 108849135036119180264794255)
  ·
    refine ⟨163273702554178770397191383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108849135036119180264794255 163273702554178770397191383)
    ·
      refine ⟨244910553831268155595787075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163273702554178770397191383 244910553831268155595787075)
      ·
        refine ⟨367365830746902233393680613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244910553831268155595787075 367365830746902233393680613)
        ·
          refine ⟨68881093265044168761315115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 367365830746902233393680613 68881093265044168761315115)
          ·
            refine ⟨103321639897566253141972673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68881093265044168761315115 103321639897566253141972673)
            ·
              refine ⟨77491229923174689856479505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103321639897566253141972673 77491229923174689856479505)
              ·
                refine ⟨58118422442381017392359629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77491229923174689856479505 58118422442381017392359629)
                ·
                  refine ⟨21794408415892881522134861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58118422442381017392359629 21794408415892881522134861)
                  ·
                    refine ⟨8172903155959830570800573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21794408415892881522134861 8172903155959830570800573)
                    ·
                      refine ⟨3064838683484936464050215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172903155959830570800573 3064838683484936464050215)
                      ·
                        rfl

theorem cell23_5968752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_5968752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968752 prefixEnd_5968752 := by exact prefixLift 5968752
  have htrace : WordTrace (prefixWord ++ tailWord_5968752) baseStart_5968752 baseEnd_5968752 := by
    simpa [prefixWord, tailWord_5968752, baseEnd_5968752] using wordTrace_append hprefix tailTrace_5968752
  have hstable : (prefixWord ++ tailWord_5968752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968752).length < 2 ^ (prefixWord ++ tailWord_5968752).sum := by decide
  have hdescent : baseEnd_5968752 < baseStart_5968752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968753 : List Nat := [1, 2, 2, 2, 1, 4, 2, 4, 1, 2, 2]
def baseStart_5968753 : Nat := 118140960795 + 5968753 * 2 ^ 59
def prefixEnd_5968753 : Nat := 4983230072969 + 3 ^ 40 * 5968753 * 2
def baseEnd_5968753 : Nat := 3064839196965590960137711

theorem tailTrace_5968753 : CollatzResearch.WordTrace tailWord_5968753 prefixEnd_5968753 3064839196965590960137711 := by
  unfold tailWord_5968753
  simp only [CollatzResearch.WordTrace]
  refine ⟨217698306545234737700374913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145132204363489825133583275 217698306545234737700374913)
  ·
    refine ⟨163273729908926053275281185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 217698306545234737700374913 163273729908926053275281185)
    ·
      refine ⟨122455297431694539956460889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163273729908926053275281185 122455297431694539956460889)
      ·
        refine ⟨91841473073770904967345667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122455297431694539956460889 91841473073770904967345667)
        ·
          refine ⟨137762209610656357451018501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91841473073770904967345667 137762209610656357451018501)
          ·
            refine ⟨25830414301998067022065969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137762209610656357451018501 25830414301998067022065969)
            ·
              refine ⟨19372810726498550266549477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25830414301998067022065969 19372810726498550266549477)
              ·
                refine ⟨3632402011218478174978027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19372810726498550266549477 3632402011218478174978027)
                ·
                  refine ⟨5448603016827717262467041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632402011218478174978027 5448603016827717262467041)
                  ·
                    refine ⟨4086452262620787946850281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5448603016827717262467041 4086452262620787946850281)
                    ·
                      refine ⟨3064839196965590960137711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4086452262620787946850281 3064839196965590960137711)
                      ·
                        rfl

theorem cell23_5968753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_5968753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968753 prefixEnd_5968753 := by exact prefixLift 5968753
  have htrace : WordTrace (prefixWord ++ tailWord_5968753) baseStart_5968753 baseEnd_5968753 := by
    simpa [prefixWord, tailWord_5968753, baseEnd_5968753] using wordTrace_append hprefix tailTrace_5968753
  have hstable : (prefixWord ++ tailWord_5968753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968753).length < 2 ^ (prefixWord ++ tailWord_5968753).sum := by decide
  have hdescent : baseEnd_5968753 < baseStart_5968753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968755 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 1, 9]
def baseStart_5968755 : Nat := 118140960795 + 5968755 * 2 ^ 59
def prefixEnd_5968755 : Nat := 4983230072969 + 3 ^ 40 * 5968755 * 2
def baseEnd_5968755 : Nat := 1021613407975633317437567

theorem tailTrace_5968755 : CollatzResearch.WordTrace tailWord_5968755 prefixEnd_5968755 1021613407975633317437567 := by
  unfold tailWord_5968755
  simp only [CollatzResearch.WordTrace]
  refine ⟨217698379491227492041947719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145132252994151661361298479 217698379491227492041947719)
  ·
    refine ⟨326547569236841238062921579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217698379491227492041947719 326547569236841238062921579)
    ·
      refine ⟨489821353855261857094382369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326547569236841238062921579 489821353855261857094382369)
      ·
        refine ⟨367366015391446392820786777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489821353855261857094382369 367366015391446392820786777)
        ·
          refine ⟨275524511543584794615590083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367366015391446392820786777 275524511543584794615590083)
          ·
            refine ⟨413286767315377191923385125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275524511543584794615590083 413286767315377191923385125)
            ·
              refine ⟨77491268871633223485634711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 413286767315377191923385125 77491268871633223485634711)
              ·
                refine ⟨116236903307449835228452067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77491268871633223485634711 116236903307449835228452067)
                ·
                  refine ⟨174355354961174752842678101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116236903307449835228452067 174355354961174752842678101)
                  ·
                    refine ⟨1021613407975633317437567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 174355354961174752842678101 1021613407975633317437567)
                    ·
                      rfl

theorem cell23_5968755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 9].length) (baseStart_5968755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968755 prefixEnd_5968755 := by exact prefixLift 5968755
  have htrace : WordTrace (prefixWord ++ tailWord_5968755) baseStart_5968755 baseEnd_5968755 := by
    simpa [prefixWord, tailWord_5968755, baseEnd_5968755] using wordTrace_append hprefix tailTrace_5968755
  have hstable : (prefixWord ++ tailWord_5968755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968755).length < 2 ^ (prefixWord ++ tailWord_5968755).sum := by decide
  have hdescent : baseEnd_5968755 < baseStart_5968755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968766 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5968766 : Nat := 118140960795 + 5968766 * 2 ^ 59
def prefixEnd_5968766 : Nat := 4983230072969 + 3 ^ 40 * 5968766 * 2
def baseEnd_5968766 : Nat := 3064845872214099409275151

theorem tailTrace_5968766 : CollatzResearch.WordTrace tailWord_5968766 prefixEnd_5968766 3064845872214099409275151 := by
  unfold tailWord_5968766
  simp only [CollatzResearch.WordTrace]
  refine ⟨27212347586773455115074769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 145132520462791760613732101 27212347586773455115074769)
  ·
    refine ⟨20409260690080091336306077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27212347586773455115074769 20409260690080091336306077)
    ·
      refine ⟨7653472758780034251114779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20409260690080091336306077 7653472758780034251114779)
      ·
        refine ⟨11480209138170051376672169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7653472758780034251114779 11480209138170051376672169)
        ·
          refine ⟨8610156853627538532504127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11480209138170051376672169 8610156853627538532504127)
          ·
            refine ⟨12915235280441307798756191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8610156853627538532504127 12915235280441307798756191)
            ·
              refine ⟨19372852920661961698134287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12915235280441307798756191 19372852920661961698134287)
              ·
                refine ⟨29059279380992942547201431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19372852920661961698134287 29059279380992942547201431)
                ·
                  refine ⟨43588919071489413820802147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29059279380992942547201431 43588919071489413820802147)
                  ·
                    refine ⟨65383378607234120731203221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43588919071489413820802147 65383378607234120731203221)
                    ·
                      refine ⟨3064845872214099409275151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65383378607234120731203221 3064845872214099409275151)
                      ·
                        rfl

theorem cell23_5968766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5968766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968766 prefixEnd_5968766 := by exact prefixLift 5968766
  have htrace : WordTrace (prefixWord ++ tailWord_5968766) baseStart_5968766 baseEnd_5968766 := by
    simpa [prefixWord, tailWord_5968766, baseEnd_5968766] using wordTrace_append hprefix tailTrace_5968766
  have hstable : (prefixWord ++ tailWord_5968766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968766).length < 2 ^ (prefixWord ++ tailWord_5968766).sum := by decide
  have hdescent : baseEnd_5968766 < baseStart_5968766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968770 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5968770 : Nat := 118140960795 + 5968770 * 2 ^ 59
def prefixEnd_5968770 : Nat := 4983230072969 + 3 ^ 40 * 5968770 * 2
def baseEnd_5968770 : Nat := 3064847926136717393625133

theorem tailTrace_5968770 : CollatzResearch.WordTrace tailWord_5968770 prefixEnd_5968770 3064847926136717393625133 := by
  unfold tailWord_5968770
  simp only [CollatzResearch.WordTrace]
  refine ⟨54424731646543287400935941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 145132617724115433069162509 54424731646543287400935941)
  ·
    refine ⟨10204637183726866387675489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54424731646543287400935941 10204637183726866387675489)
    ·
      refine ⟨7653477887795149790756617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10204637183726866387675489 7653477887795149790756617)
      ·
        refine ⟨5740108415846362343067463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7653477887795149790756617 5740108415846362343067463)
        ·
          refine ⟨8610162623769543514601195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5740108415846362343067463 8610162623769543514601195)
          ·
            refine ⟨12915243935654315271901793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8610162623769543514601195 12915243935654315271901793)
            ·
              refine ⟨9686432951740736453926345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12915243935654315271901793 9686432951740736453926345)
              ·
                refine ⟨7264824713805552340444759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9686432951740736453926345 7264824713805552340444759)
                ·
                  refine ⟨10897237070708328510667139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7264824713805552340444759 10897237070708328510667139)
                  ·
                    refine ⟨16345855606062492766000709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10897237070708328510667139 16345855606062492766000709)
                    ·
                      refine ⟨3064847926136717393625133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16345855606062492766000709 3064847926136717393625133)
                      ·
                        rfl

theorem cell23_5968770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5968770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968770 prefixEnd_5968770 := by exact prefixLift 5968770
  have htrace : WordTrace (prefixWord ++ tailWord_5968770) baseStart_5968770 baseEnd_5968770 := by
    simpa [prefixWord, tailWord_5968770, baseEnd_5968770] using wordTrace_append hprefix tailTrace_5968770
  have hstable : (prefixWord ++ tailWord_5968770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968770).length < 2 ^ (prefixWord ++ tailWord_5968770).sum := by decide
  have hdescent : baseEnd_5968770 < baseStart_5968770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968779 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 3, 3, 2]
def baseStart_5968779 : Nat := 118140960795 + 5968779 * 2 ^ 59
def prefixEnd_5968779 : Nat := 4983230072969 + 3 ^ 40 * 5968779 * 2
def baseEnd_5968779 : Nat := 3064852547462607858412591

theorem tailTrace_5968779 : CollatzResearch.WordTrace tailWord_5968779 prefixEnd_5968779 3064852547462607858412591 := by
  unfold tailWord_5968779
  simp only [CollatzResearch.WordTrace]
  refine ⟨217699254843140544140821391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145132836562093696093880927 217699254843140544140821391)
  ·
    refine ⟨326548882264710816211232087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217699254843140544140821391 326548882264710816211232087)
    ·
      refine ⟨489823323397066224316848131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326548882264710816211232087 489823323397066224316848131)
      ·
        refine ⟨734734985095599336475272197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489823323397066224316848131 734734985095599336475272197)
        ·
          refine ⟨137762809705424875589113537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 734734985095599336475272197 137762809705424875589113537)
          ·
            refine ⟨103322107279068656691835153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137762809705424875589113537 103322107279068656691835153)
            ·
              refine ⟨77491580459301492518876365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103322107279068656691835153 77491580459301492518876365)
              ·
                refine ⟨29059342672238059694578637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77491580459301492518876365 29059342672238059694578637)
                ·
                  refine ⟨10897253502089272385466989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29059342672238059694578637 10897253502089272385466989)
                  ·
                    refine ⟨4086470063283477144550121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10897253502089272385466989 4086470063283477144550121)
                    ·
                      refine ⟨3064852547462607858412591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4086470063283477144550121 3064852547462607858412591)
                      ·
                        rfl

theorem cell23_5968779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 3, 2].length) (baseStart_5968779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968779 prefixEnd_5968779 := by exact prefixLift 5968779
  have htrace : WordTrace (prefixWord ++ tailWord_5968779) baseStart_5968779 baseEnd_5968779 := by
    simpa [prefixWord, tailWord_5968779, baseEnd_5968779] using wordTrace_append hprefix tailTrace_5968779
  have hstable : (prefixWord ++ tailWord_5968779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968779).length < 2 ^ (prefixWord ++ tailWord_5968779).sum := by decide
  have hdescent : baseEnd_5968779 < baseStart_5968779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5968790 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5968790 : Nat := 118140960795 + 5968790 * 2 ^ 59
def prefixEnd_5968790 : Nat := 4983230072969 + 3 ^ 40 * 5968790 * 2
def baseEnd_5968790 : Nat := 3064858195749807315375041

theorem tailTrace_5968790 : CollatzResearch.WordTrace tailWord_5968790 prefixEnd_5968790 3064858195749807315375041 := by
  unfold tailWord_5968790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13606228502881293313716989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 145133104030733795346314549 13606228502881293313716989)
  ·
    refine ⟨5102335688580484992643871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13606228502881293313716989 5102335688580484992643871)
    ·
      refine ⟨7653503532870727488965807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5102335688580484992643871 7653503532870727488965807)
      ·
        refine ⟨11480255299306091233448711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7653503532870727488965807 11480255299306091233448711)
        ·
          refine ⟨17220382948959136850173067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11480255299306091233448711 17220382948959136850173067)
          ·
            refine ⟨25830574423438705275259601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17220382948959136850173067 25830574423438705275259601)
            ·
              refine ⟨19372930817579028956444701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25830574423438705275259601 19372930817579028956444701)
              ·
                refine ⟨7264849056592135858666763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19372930817579028956444701 7264849056592135858666763)
                ·
                  refine ⟨10897273584888203788000145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7264849056592135858666763 10897273584888203788000145)
                  ·
                    refine ⟨8172955188666152841000109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10897273584888203788000145 8172955188666152841000109)
                    ·
                      refine ⟨3064858195749807315375041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8172955188666152841000109 3064858195749807315375041)
                      ·
                        rfl

theorem cell23_5968790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5968790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5968790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5968790 prefixEnd_5968790 := by exact prefixLift 5968790
  have htrace : WordTrace (prefixWord ++ tailWord_5968790) baseStart_5968790 baseEnd_5968790 := by
    simpa [prefixWord, tailWord_5968790, baseEnd_5968790] using wordTrace_append hprefix tailTrace_5968790
  have hstable : (prefixWord ++ tailWord_5968790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5968790).length < 2 ^ (prefixWord ++ tailWord_5968790).sum := by decide
  have hdescent : baseEnd_5968790 < baseStart_5968790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5968790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
