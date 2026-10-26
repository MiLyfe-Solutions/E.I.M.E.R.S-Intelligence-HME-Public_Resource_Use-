import V185TrunkScan22Chunk433

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3868631 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 1, 8]
def baseStart_3868631 : Nat := 118140960795 + 3868631 * 2 ^ 59
def prefixEnd_3868631 : Nat := 4983230072969 + 3 ^ 40 * 3868631 * 2
def baseEnd_3868631 : Nat := 1324311451922639131413997

theorem tailTrace_3868631 : CollatzResearch.WordTrace tailWord_3868631 prefixEnd_3868631 1324311451922639131413997 := by
  unfold tailWord_3868631
  simp only [CollatzResearch.WordTrace]
  refine ⟨141100564447618071418133747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94067042965078714278755831 141100564447618071418133747)
  ·
    refine ⟨211650846671427107127200621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141100564447618071418133747 211650846671427107127200621)
    ·
      refine ⟨79369067501785165172700233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211650846671427107127200621 79369067501785165172700233)
      ·
        refine ⟨59526800626338873879525175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79369067501785165172700233 59526800626338873879525175)
        ·
          refine ⟨89290200939508310819287763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59526800626338873879525175 89290200939508310819287763)
          ·
            refine ⟨133935301409262466228931645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89290200939508310819287763 133935301409262466228931645)
            ·
              refine ⟨50225738028473424835849367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133935301409262466228931645 50225738028473424835849367)
              ·
                refine ⟨75338607042710137253774051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50225738028473424835849367 75338607042710137253774051)
                ·
                  refine ⟨113007910564065205880661077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75338607042710137253774051 113007910564065205880661077)
                  ·
                    refine ⟨1324311451922639131413997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113007910564065205880661077 1324311451922639131413997)
                    ·
                      rfl

theorem cell22_3868631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_3868631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868631 prefixEnd_3868631 := by exact prefixLift 3868631
  have htrace : WordTrace (prefixWord ++ tailWord_3868631) baseStart_3868631 baseEnd_3868631 := by
    simpa [prefixWord, tailWord_3868631, baseEnd_3868631] using wordTrace_append hprefix tailTrace_3868631
  have hstable : (prefixWord ++ tailWord_3868631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868631).length < 2 ^ (prefixWord ++ tailWord_3868631).sum := by decide
  have hdescent : baseEnd_3868631 < baseStart_3868631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868650 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_3868650 : Nat := 118140960795 + 3868650 * 2 ^ 59
def prefixEnd_3868650 : Nat := 4983230072969 + 3 ^ 40 * 3868650 * 2
def baseEnd_3868650 : Nat := 1324317956010929415188939

theorem tailTrace_3868650 : CollatzResearch.WordTrace tailWord_3868650 prefixEnd_3868650 1324317956010929415188939 := by
  unfold tailWord_3868650
  simp only [CollatzResearch.WordTrace]
  refine ⟨35275314358637309415768851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94067504956366158442050269 35275314358637309415768851)
  ·
    refine ⟨52912971537955964123653277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35275314358637309415768851 52912971537955964123653277)
    ·
      refine ⟨19842364326733486546369979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52912971537955964123653277 19842364326733486546369979)
      ·
        refine ⟨29763546490100229819554969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19842364326733486546369979 29763546490100229819554969)
        ·
          refine ⟨22322659867575172364666227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29763546490100229819554969 22322659867575172364666227)
          ·
            refine ⟨33483989801362758546999341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22322659867575172364666227 33483989801362758546999341)
            ·
              refine ⟨12556496175511034455124753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33483989801362758546999341 12556496175511034455124753)
              ·
                refine ⟨9417372131633275841343565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12556496175511034455124753 9417372131633275841343565)
                ·
                  refine ⟨3531514549362478440503837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9417372131633275841343565 3531514549362478440503837)
                  ·
                    refine ⟨1324317956010929415188939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531514549362478440503837 1324317956010929415188939)
                    ·
                      rfl

theorem cell22_3868650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_3868650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868650 prefixEnd_3868650 := by exact prefixLift 3868650
  have htrace : WordTrace (prefixWord ++ tailWord_3868650) baseStart_3868650 baseEnd_3868650 := by
    simpa [prefixWord, tailWord_3868650, baseEnd_3868650] using wordTrace_append hprefix tailTrace_3868650
  have hstable : (prefixWord ++ tailWord_3868650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868650).length < 2 ^ (prefixWord ++ tailWord_3868650).sum := by decide
  have hdescent : baseEnd_3868650 < baseStart_3868650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868723 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 1, 5]
def baseStart_3868723 : Nat := 118140960795 + 3868723 * 2 ^ 59
def prefixEnd_3868723 : Nat := 4983230072969 + 3 ^ 40 * 3868723 * 2
def baseEnd_3868723 : Nat := 1324342945402781558113715

theorem tailTrace_3868723 : CollatzResearch.WordTrace tailWord_3868723 prefixEnd_3868723 1324342945402781558113715 := by
  unfold tailWord_3868723
  simp only [CollatzResearch.WordTrace]
  refine ⟨141103919963284771130482823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94069279975523180753655215 141103919963284771130482823)
  ·
    refine ⟨211655879944927156695724235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141103919963284771130482823 211655879944927156695724235)
    ·
      refine ⟨317483819917390735043586353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211655879944927156695724235 317483819917390735043586353)
      ·
        refine ⟨238112864938043051282689765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317483819917390735043586353 238112864938043051282689765)
        ·
          refine ⟨44646162175883072115504331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238112864938043051282689765 44646162175883072115504331)
          ·
            refine ⟨66969243263824608173256497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44646162175883072115504331 66969243263824608173256497)
            ·
              refine ⟨50226932447868456129942373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66969243263824608173256497 50226932447868456129942373)
              ·
                refine ⟨9417549833975335524364195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50226932447868456129942373 9417549833975335524364195)
                ·
                  refine ⟨14126324750963003286546293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9417549833975335524364195 14126324750963003286546293)
                  ·
                    refine ⟨1324342945402781558113715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14126324750963003286546293 1324342945402781558113715)
                    ·
                      rfl

theorem cell22_3868723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 5].length) (baseStart_3868723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868723 prefixEnd_3868723 := by exact prefixLift 3868723
  have htrace : WordTrace (prefixWord ++ tailWord_3868723) baseStart_3868723 baseEnd_3868723 := by
    simpa [prefixWord, tailWord_3868723, baseEnd_3868723] using wordTrace_append hprefix tailTrace_3868723
  have hstable : (prefixWord ++ tailWord_3868723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868723).length < 2 ^ (prefixWord ++ tailWord_3868723).sum := by decide
  have hdescent : baseEnd_3868723 < baseStart_3868723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868757 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_3868757 : Nat := 118140960795 + 3868757 * 2 ^ 59
def prefixEnd_3868757 : Nat := 4983230072969 + 3 ^ 40 * 3868757 * 2
def baseEnd_3868757 : Nat := 1324354584297616802763611

theorem tailTrace_3868757 : CollatzResearch.WordTrace tailWord_3868757 prefixEnd_3868757 1324354584297616802763611 := by
  unfold tailWord_3868757
  simp only [CollatzResearch.WordTrace]
  refine ⟨141105160045161594937220525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94070106696774396624813683 141105160045161594937220525)
  ·
    refine ⟨52914435016935598101457697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141105160045161594937220525 52914435016935598101457697)
    ·
      refine ⟨39685826262701698576093273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52914435016935598101457697 39685826262701698576093273)
      ·
        refine ⟨29764369697026273932069955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39685826262701698576093273 29764369697026273932069955)
        ·
          refine ⟨44646554545539410898104933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29764369697026273932069955 44646554545539410898104933)
          ·
            refine ⟨8371228977288639543394675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44646554545539410898104933 8371228977288639543394675)
            ·
              refine ⟨12556843465932959315092013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8371228977288639543394675 12556843465932959315092013)
              ·
                refine ⟨4708816299724859743159505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12556843465932959315092013 4708816299724859743159505)
                ·
                  refine ⟨3531612224793644807369629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4708816299724859743159505 3531612224793644807369629)
                  ·
                    refine ⟨1324354584297616802763611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531612224793644807369629 1324354584297616802763611)
                    ·
                      rfl

theorem cell22_3868757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_3868757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868757 prefixEnd_3868757 := by exact prefixLift 3868757
  have htrace : WordTrace (prefixWord ++ tailWord_3868757) baseStart_3868757 baseEnd_3868757 := by
    simpa [prefixWord, tailWord_3868757, baseEnd_3868757] using wordTrace_append hprefix tailTrace_3868757
  have hstable : (prefixWord ++ tailWord_3868757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868757).length < 2 ^ (prefixWord ++ tailWord_3868757).sum := by decide
  have hdescent : baseEnd_3868757 < baseStart_3868757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868836 : List Nat := [2, 3, 1, 2, 4, 1, 2, 3, 1, 3]
def baseStart_3868836 : Nat := 118140960795 + 3868836 * 2 ^ 59
def prefixEnd_3868836 : Nat := 4983230072969 + 3 ^ 40 * 3868836 * 2
def baseEnd_3868836 : Nat := 1324381627612086930038369

theorem tailTrace_3868836 : CollatzResearch.WordTrace tailWord_3868836 prefixEnd_3868836 1324381627612086930038369 := by
  unfold tailWord_3868836
  simp only [CollatzResearch.WordTrace]
  refine ⟨70554020705937695714673181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94072027607916927619564241 70554020705937695714673181)
  ·
    refine ⟨26457757764726635893002443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70554020705937695714673181 26457757764726635893002443)
    ·
      refine ⟨39686636647089953839503665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26457757764726635893002443 39686636647089953839503665)
      ·
        refine ⟨29764977485317465379627749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39686636647089953839503665 29764977485317465379627749)
        ·
          refine ⟨5580933278497024758680203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29764977485317465379627749 5580933278497024758680203)
          ·
            refine ⟨8371399917745537138020305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580933278497024758680203 8371399917745537138020305)
            ·
              refine ⟨6278549938309152853515229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8371399917745537138020305 6278549938309152853515229)
              ·
                refine ⟨2354456226865932320068211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6278549938309152853515229 2354456226865932320068211)
                ·
                  refine ⟨3531684340298898480102317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354456226865932320068211 3531684340298898480102317)
                  ·
                    refine ⟨1324381627612086930038369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531684340298898480102317 1324381627612086930038369)
                    ·
                      rfl

theorem cell22_3868836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_3868836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868836 prefixEnd_3868836 := by exact prefixLift 3868836
  have htrace : WordTrace (prefixWord ++ tailWord_3868836) baseStart_3868836 baseEnd_3868836 := by
    simpa [prefixWord, tailWord_3868836, baseEnd_3868836] using wordTrace_append hprefix tailTrace_3868836
  have hstable : (prefixWord ++ tailWord_3868836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868836).length < 2 ^ (prefixWord ++ tailWord_3868836).sum := by decide
  have hdescent : baseEnd_3868836 < baseStart_3868836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868849 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 5]
def baseStart_3868849 : Nat := 118140960795 + 3868849 * 2 ^ 59
def prefixEnd_3868849 : Nat := 4983230072969 + 3 ^ 40 * 3868849 * 2
def baseEnd_3868849 : Nat := 441462025925919743154443

theorem tailTrace_3868849 : CollatzResearch.WordTrace tailWord_3868849 prefixEnd_3868849 441462025925919743154443 := by
  unfold tailWord_3868849
  simp only [CollatzResearch.WordTrace]
  refine ⟨141108515560828294649569601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94072343707218863099713067 141108515560828294649569601)
  ·
    refine ⟨105831386670621220987177201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141108515560828294649569601 105831386670621220987177201)
    ·
      refine ⟨79373540002965915740382901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105831386670621220987177201 79373540002965915740382901)
      ·
        refine ⟨7441269375278054600660897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79373540002965915740382901 7441269375278054600660897)
        ·
          refine ⟨5580952031458540950495673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7441269375278054600660897 5580952031458540950495673)
          ·
            refine ⟨4185714023593905712871755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580952031458540950495673 4185714023593905712871755)
            ·
              refine ⟨6278571035390858569307633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4185714023593905712871755 6278571035390858569307633)
              ·
                refine ⟨4708928276543143926980725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6278571035390858569307633 4708928276543143926980725)
                ·
                  refine ⟨441462025925919743154443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4708928276543143926980725 441462025925919743154443)
                  ·
                    rfl

theorem cell22_3868849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_3868849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868849 prefixEnd_3868849 := by exact prefixLift 3868849
  have htrace : WordTrace (prefixWord ++ tailWord_3868849) baseStart_3868849 baseEnd_3868849 := by
    simpa [prefixWord, tailWord_3868849, baseEnd_3868849] using wordTrace_append hprefix tailTrace_3868849
  have hstable : (prefixWord ++ tailWord_3868849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868849).length < 2 ^ (prefixWord ++ tailWord_3868849).sum := by decide
  have hdescent : baseEnd_3868849 < baseStart_3868849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868890 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_3868890 : Nat := 118140960795 + 3868890 * 2 ^ 59
def prefixEnd_3868890 : Nat := 4983230072969 + 3 ^ 40 * 3868890 * 2
def baseEnd_3868890 : Nat := 1324400112915648789188203

theorem tailTrace_3868890 : CollatzResearch.WordTrace tailWord_3868890 prefixEnd_3868890 1324400112915648789188203 := by
  unfold tailWord_3868890
  simp only [CollatzResearch.WordTrace]
  refine ⟨35277502738419939662953031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94073340635786505767874749 35277502738419939662953031)
  ·
    refine ⟨52916254107629909494429547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35277502738419939662953031 52916254107629909494429547)
    ·
      refine ⟨79374381161444864241644321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52916254107629909494429547 79374381161444864241644321)
      ·
        refine ⟨59530785871083648181233241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79374381161444864241644321 59530785871083648181233241)
        ·
          refine ⟨44648089403312736135924931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59530785871083648181233241 44648089403312736135924931)
          ·
            refine ⟨66972134104969104203887397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44648089403312736135924931 66972134104969104203887397)
            ·
              refine ⟨12557275144681707038228887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66972134104969104203887397 12557275144681707038228887)
              ·
                refine ⟨18835912717022560557343331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12557275144681707038228887 18835912717022560557343331)
                ·
                  refine ⟨28253869075533840836014997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18835912717022560557343331 28253869075533840836014997)
                  ·
                    refine ⟨1324400112915648789188203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28253869075533840836014997 1324400112915648789188203)
                    ·
                      rfl

theorem cell22_3868890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_3868890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868890 prefixEnd_3868890 := by exact prefixLift 3868890
  have htrace : WordTrace (prefixWord ++ tailWord_3868890) baseStart_3868890 baseEnd_3868890 := by
    simpa [prefixWord, tailWord_3868890, baseEnd_3868890] using wordTrace_append hprefix tailTrace_3868890
  have hstable : (prefixWord ++ tailWord_3868890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868890).length < 2 ^ (prefixWord ++ tailWord_3868890).sum := by decide
  have hdescent : baseEnd_3868890 < baseStart_3868890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3868995 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 8]
def baseStart_3868995 : Nat := 118140960795 + 3868995 * 2 ^ 59
def prefixEnd_3868995 : Nat := 4983230072969 + 3 ^ 40 * 3868995 * 2
def baseEnd_3868995 : Nat := 441478685520487838437627

theorem tailTrace_3868995 : CollatzResearch.WordTrace tailWord_3868995 prefixEnd_3868995 441478685520487838437627 := by
  unfold tailWord_3868995
  simp only [CollatzResearch.WordTrace]
  refine ⟨141113840618299361584384439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94075893745532907722922959 141113840618299361584384439)
  ·
    refine ⟨211670760927449042376576659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141113840618299361584384439 211670760927449042376576659)
    ·
      refine ⟨317506141391173563564864989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211670760927449042376576659 317506141391173563564864989)
      ·
        refine ⟨119064803021690086336824371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317506141391173563564864989 119064803021690086336824371)
        ·
          refine ⟨178597204532535129505236557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119064803021690086336824371 178597204532535129505236557)
          ·
            refine ⟨66973951699700673564463709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178597204532535129505236557 66973951699700673564463709)
            ·
              refine ⟨25115231887387752586673891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66973951699700673564463709 25115231887387752586673891)
              ·
                refine ⟨37672847831081628880010837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25115231887387752586673891 37672847831081628880010837)
                ·
                  refine ⟨441478685520487838437627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37672847831081628880010837 441478685520487838437627)
                  ·
                    rfl

theorem cell22_3868995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 8].length) (baseStart_3868995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3868995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3868995 prefixEnd_3868995 := by exact prefixLift 3868995
  have htrace : WordTrace (prefixWord ++ tailWord_3868995) baseStart_3868995 baseEnd_3868995 := by
    simpa [prefixWord, tailWord_3868995, baseEnd_3868995] using wordTrace_append hprefix tailTrace_3868995
  have hstable : (prefixWord ++ tailWord_3868995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3868995).length < 2 ^ (prefixWord ++ tailWord_3868995).sum := by decide
  have hdescent : baseEnd_3868995 < baseStart_3868995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3868995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869022 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3869022 : Nat := 118140960795 + 3869022 * 2 ^ 59
def prefixEnd_3869022 : Nat := 4983230072969 + 3 ^ 40 * 3869022 * 2
def baseEnd_3869022 : Nat := 1324445299213244444887799

theorem tailTrace_3869022 : CollatzResearch.WordTrace tailWord_3869022 prefixEnd_3869022 1324445299213244444887799 := by
  unfold tailWord_3869022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17639353173650193149452165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94076550259467696797078213 17639353173650193149452165)
  ·
    refine ⟨3307378720059411215522281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17639353173650193149452165 3307378720059411215522281)
    ·
      refine ⟨2480534040044558411641711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3307378720059411215522281 2480534040044558411641711)
      ·
        refine ⟨3720801060066837617462567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480534040044558411641711 3720801060066837617462567)
        ·
          refine ⟨5581201590100256426193851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720801060066837617462567 5581201590100256426193851)
          ·
            refine ⟨8371802385150384639290777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581201590100256426193851 8371802385150384639290777)
            ·
              refine ⟨6278851788862788479468083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8371802385150384639290777 6278851788862788479468083)
              ·
                refine ⟨9418277683294182719202125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278851788862788479468083 9418277683294182719202125)
                ·
                  refine ⟨3531854131235318519700797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9418277683294182719202125 3531854131235318519700797)
                  ·
                    refine ⟨1324445299213244444887799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531854131235318519700797 1324445299213244444887799)
                    ·
                      rfl

theorem cell22_3869022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3869022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869022 prefixEnd_3869022 := by exact prefixLift 3869022
  have htrace : WordTrace (prefixWord ++ tailWord_3869022) baseStart_3869022 baseEnd_3869022 := by
    simpa [prefixWord, tailWord_3869022, baseEnd_3869022] using wordTrace_append hprefix tailTrace_3869022
  have hstable : (prefixWord ++ tailWord_3869022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869022).length < 2 ^ (prefixWord ++ tailWord_3869022).sum := by decide
  have hdescent : baseEnd_3869022 < baseStart_3869022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869029 : List Nat := [1, 3, 1, 3, 1, 3, 2, 4, 4]
def baseStart_3869029 : Nat := 118140960795 + 3869029 * 2 ^ 59
def prefixEnd_3869029 : Nat := 4983230072969 + 3 ^ 40 * 3869029 * 2
def baseEnd_3869029 : Nat := 441482565152099586654259

theorem tailTrace_3869029 : CollatzResearch.WordTrace tailWord_3869029 prefixEnd_3869029 441482565152099586654259 := by
  unfold tailWord_3869029
  simp only [CollatzResearch.WordTrace]
  refine ⟨141115080700176185391122141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94076720466784123594081427 141115080700176185391122141)
  ·
    refine ⟨52918155262566069521670803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141115080700176185391122141 52918155262566069521670803)
    ·
      refine ⟨79377232893849104282506205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52918155262566069521670803 79377232893849104282506205)
      ·
        refine ⟨29766462335193414105939827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79377232893849104282506205 29766462335193414105939827)
        ·
          refine ⟨44649693502790121158909741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29766462335193414105939827 44649693502790121158909741)
          ·
            refine ⟨16743635063546295434591153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44649693502790121158909741 16743635063546295434591153)
            ·
              refine ⟨12557726297659721575943365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16743635063546295434591153 12557726297659721575943365)
              ·
                refine ⟨2354573680811197795489381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12557726297659721575943365 2354573680811197795489381)
                ·
                  refine ⟨441482565152099586654259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2354573680811197795489381 441482565152099586654259)
                  ·
                    rfl

theorem cell22_3869029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_3869029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869029 prefixEnd_3869029 := by exact prefixLift 3869029
  have htrace : WordTrace (prefixWord ++ tailWord_3869029) baseStart_3869029 baseEnd_3869029 := by
    simpa [prefixWord, tailWord_3869029, baseEnd_3869029] using wordTrace_append hprefix tailTrace_3869029
  have hstable : (prefixWord ++ tailWord_3869029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869029).length < 2 ^ (prefixWord ++ tailWord_3869029).sum := by decide
  have hdescent : baseEnd_3869029 < baseStart_3869029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869042 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_3869042 : Nat := 118140960795 + 3869042 * 2 ^ 59
def prefixEnd_3869042 : Nat := 4983230072969 + 3 ^ 40 * 3869042 * 2
def baseEnd_3869042 : Nat := 1324452145621971059387737

theorem tailTrace_3869042 : CollatzResearch.WordTrace tailWord_3869042 prefixEnd_3869042 1324452145621971059387737 := by
  unfold tailWord_3869042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35278888712282272152836345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94077036566086059074230253 35278888712282272152836345)
  ·
    refine ⟨26459166534211704114627259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35278888712282272152836345 26459166534211704114627259)
    ·
      refine ⟨39688749801317556171940889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26459166534211704114627259 39688749801317556171940889)
      ·
        refine ⟨29766562350988167128955667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39688749801317556171940889 29766562350988167128955667)
        ·
          refine ⟨44649843526482250693433501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29766562350988167128955667 44649843526482250693433501)
          ·
            refine ⟨16743691322430844010037563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44649843526482250693433501 16743691322430844010037563)
            ·
              refine ⟨25115536983646266015056345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16743691322430844010037563 25115536983646266015056345)
              ·
                refine ⟨18836652737734699511292259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25115536983646266015056345 18836652737734699511292259)
                ·
                  refine ⟨28254979106602049266938389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18836652737734699511292259 28254979106602049266938389)
                  ·
                    refine ⟨1324452145621971059387737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28254979106602049266938389 1324452145621971059387737)
                    ·
                      rfl

theorem cell22_3869042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_3869042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869042 prefixEnd_3869042 := by exact prefixLift 3869042
  have htrace : WordTrace (prefixWord ++ tailWord_3869042) baseStart_3869042 baseEnd_3869042 := by
    simpa [prefixWord, tailWord_3869042, baseEnd_3869042] using wordTrace_append hprefix tailTrace_3869042
  have hstable : (prefixWord ++ tailWord_3869042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869042).length < 2 ^ (prefixWord ++ tailWord_3869042).sum := by decide
  have hdescent : baseEnd_3869042 < baseStart_3869042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869076 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3869076 : Nat := 118140960795 + 3869076 * 2 ^ 59
def prefixEnd_3869076 : Nat := 4983230072969 + 3 ^ 40 * 3869076 * 2
def baseEnd_3869076 : Nat := 1324463784516806304037633

theorem tailTrace_3869076 : CollatzResearch.WordTrace tailWord_3869076 prefixEnd_3869076 1324463784516806304037633 := by
  unfold tailWord_3869076
  simp only [CollatzResearch.WordTrace]
  refine ⟨70558397465502956209041541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94077863287337274945388721 70558397465502956209041541)
  ·
    refine ⟨13229699524781804289195289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70558397465502956209041541 13229699524781804289195289)
    ·
      refine ⟨9922274643586353216896467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13229699524781804289195289 9922274643586353216896467)
      ·
        refine ⟨14883411965379529825344701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9922274643586353216896467 14883411965379529825344701)
        ·
          refine ⟨5581279487017323684504263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14883411965379529825344701 5581279487017323684504263)
          ·
            refine ⟨8371919230525985526756395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581279487017323684504263 8371919230525985526756395)
            ·
              refine ⟨12557878845788978290134593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8371919230525985526756395 12557878845788978290134593)
              ·
                refine ⟨9418409134341733717600945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12557878845788978290134593 9418409134341733717600945)
                ·
                  refine ⟨7063806850756300288200709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9418409134341733717600945 7063806850756300288200709)
                  ·
                    refine ⟨1324463784516806304037633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7063806850756300288200709 1324463784516806304037633)
                    ·
                      rfl

theorem cell22_3869076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3869076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869076 prefixEnd_3869076 := by exact prefixLift 3869076
  have htrace : WordTrace (prefixWord ++ tailWord_3869076) baseStart_3869076 baseEnd_3869076 := by
    simpa [prefixWord, tailWord_3869076, baseEnd_3869076] using wordTrace_append hprefix tailTrace_3869076
  have hstable : (prefixWord ++ tailWord_3869076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869076).length < 2 ^ (prefixWord ++ tailWord_3869076).sum := by decide
  have hdescent : baseEnd_3869076 < baseStart_3869076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869087 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 2, 6]
def baseStart_3869087 : Nat := 118140960795 + 3869087 * 2 ^ 59
def prefixEnd_3869087 : Nat := 4983230072969 + 3 ^ 40 * 3869087 * 2
def baseEnd_3869087 : Nat := 1324467550041605942012599

theorem tailTrace_3869087 : CollatzResearch.WordTrace tailWord_3869087 prefixEnd_3869087 1324467550041605942012599 := by
  unfold tailWord_3869087
  simp only [CollatzResearch.WordTrace]
  refine ⟨141117196133966061296733515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94078130755977374197822343 141117196133966061296733515)
  ·
    refine ⟨211675794200949091945100273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141117196133966061296733515 211675794200949091945100273)
    ·
      refine ⟨158756845650711818958825205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211675794200949091945100273 158756845650711818958825205)
      ·
        refine ⟨14883454279754233027389863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158756845650711818958825205 14883454279754233027389863)
        ·
          refine ⟨22325181419631349541084795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14883454279754233027389863 22325181419631349541084795)
          ·
            refine ⟨33487772129447024311627193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22325181419631349541084795 33487772129447024311627193)
            ·
              refine ⟨25115829097085268233720395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33487772129447024311627193 25115829097085268233720395)
              ·
                refine ⟨37673743645627902350580593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25115829097085268233720395 37673743645627902350580593)
                ·
                  refine ⟨28255307734220926762935445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37673743645627902350580593 28255307734220926762935445)
                  ·
                    refine ⟨1324467550041605942012599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28255307734220926762935445 1324467550041605942012599)
                    ·
                      rfl

theorem cell22_3869087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_3869087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869087 prefixEnd_3869087 := by exact prefixLift 3869087
  have htrace : WordTrace (prefixWord ++ tailWord_3869087) baseStart_3869087 baseEnd_3869087 := by
    simpa [prefixWord, tailWord_3869087, baseEnd_3869087] using wordTrace_append hprefix tailTrace_3869087
  have hstable : (prefixWord ++ tailWord_3869087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869087).length < 2 ^ (prefixWord ++ tailWord_3869087).sum := by decide
  have hdescent : baseEnd_3869087 < baseStart_3869087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869140 : List Nat := [2, 4, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_3869140 : Nat := 118140960795 + 3869140 * 2 ^ 59
def prefixEnd_3869140 : Nat := 4983230072969 + 3 ^ 40 * 3869140 * 2
def baseEnd_3869140 : Nat := 1324485693024731470437437

theorem tailTrace_3869140 : CollatzResearch.WordTrace tailWord_3869140 prefixEnd_3869140 1324485693024731470437437 := by
  unfold tailWord_3869140
  simp only [CollatzResearch.WordTrace]
  refine ⟨70559564601387025674206437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94079419468516034232275249 70559564601387025674206437)
  ·
    refine ⟨13229918362760067313913707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70559564601387025674206437 13229918362760067313913707)
    ·
      refine ⟨19844877544140100970870561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13229918362760067313913707 19844877544140100970870561)
      ·
        refine ⟨14883658158105075728152921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19844877544140100970870561 14883658158105075728152921)
        ·
          refine ⟨11162743618578806796114691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14883658158105075728152921 11162743618578806796114691)
          ·
            refine ⟨16744115427868210194172037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11162743618578806796114691 16744115427868210194172037)
            ·
              refine ⟨3139521642725289411407257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16744115427868210194172037 3139521642725289411407257)
              ·
                refine ⟨2354641232043967058555443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139521642725289411407257 2354641232043967058555443)
                ·
                  refine ⟨3531961848065950587833165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354641232043967058555443 3531961848065950587833165)
                  ·
                    refine ⟨1324485693024731470437437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531961848065950587833165 1324485693024731470437437)
                    ·
                      rfl

theorem cell22_3869140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_3869140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869140 prefixEnd_3869140 := by exact prefixLift 3869140
  have htrace : WordTrace (prefixWord ++ tailWord_3869140) baseStart_3869140 baseEnd_3869140 := by
    simpa [prefixWord, tailWord_3869140, baseEnd_3869140] using wordTrace_append hprefix tailTrace_3869140
  have hstable : (prefixWord ++ tailWord_3869140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869140).length < 2 ^ (prefixWord ++ tailWord_3869140).sum := by decide
  have hdescent : baseEnd_3869140 < baseStart_3869140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869149 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3869149 : Nat := 118140960795 + 3869149 * 2 ^ 59
def prefixEnd_3869149 : Nat := 4983230072969 + 3 ^ 40 * 3869149 * 2
def baseEnd_3869149 : Nat := 1324488773908658446962409

theorem tailTrace_3869149 : CollatzResearch.WordTrace tailWord_3869149 prefixEnd_3869149 1324488773908658446962409 := by
  unfold tailWord_3869149
  simp only [CollatzResearch.WordTrace]
  refine ⟨141119457459741445885490501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94079638306494297256993667 141119457459741445885490501)
  ·
    refine ⟨26459898273701521103529469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141119457459741445885490501 26459898273701521103529469)
    ·
      refine ⟨9922461852638070413823551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26459898273701521103529469 9922461852638070413823551)
      ·
        refine ⟨14883692778957105620735327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9922461852638070413823551 14883692778957105620735327)
        ·
          refine ⟨22325539168435658431102991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14883692778957105620735327 22325539168435658431102991)
          ·
            refine ⟨33488308752653487646654487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22325539168435658431102991 33488308752653487646654487)
            ·
              refine ⟨50232463128980231469981731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33488308752653487646654487 50232463128980231469981731)
              ·
                refine ⟨75348694693470347204972597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50232463128980231469981731 75348694693470347204972597)
                ·
                  refine ⟨7063940127512845050466181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75348694693470347204972597 7063940127512845050466181)
                  ·
                    refine ⟨1324488773908658446962409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7063940127512845050466181 1324488773908658446962409)
                    ·
                      rfl

theorem cell22_3869149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3869149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869149 prefixEnd_3869149 := by exact prefixLift 3869149
  have htrace : WordTrace (prefixWord ++ tailWord_3869149) baseStart_3869149 baseEnd_3869149 := by
    simpa [prefixWord, tailWord_3869149, baseEnd_3869149] using wordTrace_append hprefix tailTrace_3869149
  have hstable : (prefixWord ++ tailWord_3869149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869149).length < 2 ^ (prefixWord ++ tailWord_3869149).sum := by decide
  have hdescent : baseEnd_3869149 < baseStart_3869149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869181 : List Nat := [1, 4, 1, 1, 1, 3, 4, 3, 4]
def baseStart_3869181 : Nat := 118140960795 + 3869181 * 2 ^ 59
def prefixEnd_3869181 : Nat := 4983230072969 + 3 ^ 40 * 3869181 * 2
def baseEnd_3869181 : Nat := 441499909387540343387437

theorem tailTrace_3869181 : CollatzResearch.WordTrace tailWord_3869181 prefixEnd_3869181 441499909387540343387437 := by
  unfold tailWord_3869181
  simp only [CollatzResearch.WordTrace]
  refine ⟨141120624595625515350655397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94080416397083676900436931 141120624595625515350655397)
  ·
    refine ⟨26460117111679784128247887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141120624595625515350655397 26460117111679784128247887)
    ·
      refine ⟨39690175667519676192371831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26460117111679784128247887 39690175667519676192371831)
      ·
        refine ⟨59535263501279514288557747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39690175667519676192371831 59535263501279514288557747)
        ·
          refine ⟨89302895251919271432836621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59535263501279514288557747 89302895251919271432836621)
          ·
            refine ⟨33488585719469726787313733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89302895251919271432836621 33488585719469726787313733)
            ·
              refine ⟨6279109822400573772621325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33488585719469726787313733 6279109822400573772621325)
              ·
                refine ⟨2354666183400215164732997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6279109822400573772621325 2354666183400215164732997)
                ·
                  refine ⟨441499909387540343387437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2354666183400215164732997 441499909387540343387437)
                  ·
                    rfl

theorem cell22_3869181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_3869181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869181 prefixEnd_3869181 := by exact prefixLift 3869181
  have htrace : WordTrace (prefixWord ++ tailWord_3869181) baseStart_3869181 baseEnd_3869181 := by
    simpa [prefixWord, tailWord_3869181, baseEnd_3869181] using wordTrace_append hprefix tailTrace_3869181
  have hstable : (prefixWord ++ tailWord_3869181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869181).length < 2 ^ (prefixWord ++ tailWord_3869181).sum := by decide
  have hdescent : baseEnd_3869181 < baseStart_3869181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869194 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_3869194 : Nat := 118140960795 + 3869194 * 2 ^ 59
def prefixEnd_3869194 : Nat := 4983230072969 + 3 ^ 40 * 3869194 * 2
def baseEnd_3869194 : Nat := 1324504178328293329587271

theorem tailTrace_3869194 : CollatzResearch.WordTrace tailWord_3869194 prefixEnd_3869194 1324504178328293329587271 := by
  unfold tailWord_3869194
  simp only [CollatzResearch.WordTrace]
  refine ⟨35280274686144604642719659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94080732496385612380585757 35280274686144604642719659)
  ·
    refine ⟨52920412029216906964079489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35280274686144604642719659 52920412029216906964079489)
    ·
      refine ⟨39690309021912680223059617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52920412029216906964079489 39690309021912680223059617)
      ·
        refine ⟨29767731766434510167294713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39690309021912680223059617 29767731766434510167294713)
        ·
          refine ⟨22325798824825882625471035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29767731766434510167294713 22325798824825882625471035)
          ·
            refine ⟨33488698237238823938206553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22325798824825882625471035 33488698237238823938206553)
            ·
              refine ⟨25116523677929117953654915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33488698237238823938206553 25116523677929117953654915)
              ·
                refine ⟨37674785516893676930482373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25116523677929117953654915 37674785516893676930482373)
                ·
                  refine ⟨7064022284417564424465445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37674785516893676930482373 7064022284417564424465445)
                  ·
                    refine ⟨1324504178328293329587271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7064022284417564424465445 1324504178328293329587271)
                    ·
                      rfl

theorem cell22_3869194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_3869194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869194 prefixEnd_3869194 := by exact prefixLift 3869194
  have htrace : WordTrace (prefixWord ++ tailWord_3869194) baseStart_3869194 baseEnd_3869194 := by
    simpa [prefixWord, tailWord_3869194, baseEnd_3869194] using wordTrace_append hprefix tailTrace_3869194
  have hstable : (prefixWord ++ tailWord_3869194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869194).length < 2 ^ (prefixWord ++ tailWord_3869194).sum := by decide
  have hdescent : baseEnd_3869194 < baseStart_3869194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869196 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 4, 3]
def baseStart_3869196 : Nat := 118140960795 + 3869196 * 2 ^ 59
def prefixEnd_3869196 : Nat := 4983230072969 + 3 ^ 40 * 3869196 * 2
def baseEnd_3869196 : Nat := 1324504862969165991037265

theorem tailTrace_3869196 : CollatzResearch.WordTrace tailWord_3869196 prefixEnd_3869196 1324504862969165991037265 := by
  unfold tailWord_3869196
  simp only [CollatzResearch.WordTrace]
  refine ⟨70560585845285586456225721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94080781127047448608300961 70560585845285586456225721)
  ·
    refine ⟨52920439383964189842169291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70560585845285586456225721 52920439383964189842169291)
    ·
      refine ⟨79380659075946284763253937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52920439383964189842169291 79380659075946284763253937)
      ·
        refine ⟨59535494306959713572440453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79380659075946284763253937 59535494306959713572440453)
        ·
          refine ⟨11162905182554946294832585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59535494306959713572440453 11162905182554946294832585)
          ·
            refine ⟨8372178886916209721124439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11162905182554946294832585 8372178886916209721124439)
            ·
              refine ⟨12558268330374314581686659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8372178886916209721124439 12558268330374314581686659)
              ·
                refine ⟨18837402495561471872529989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12558268330374314581686659 18837402495561471872529989)
                ·
                  refine ⟨3532012967917775976099373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18837402495561471872529989 3532012967917775976099373)
                  ·
                    refine ⟨1324504862969165991037265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532012967917775976099373 1324504862969165991037265)
                    ·
                      rfl

theorem cell22_3869196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_3869196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869196 prefixEnd_3869196 := by exact prefixLift 3869196
  have htrace : WordTrace (prefixWord ++ tailWord_3869196) baseStart_3869196 baseEnd_3869196 := by
    simpa [prefixWord, tailWord_3869196, baseEnd_3869196] using wordTrace_append hprefix tailTrace_3869196
  have hstable : (prefixWord ++ tailWord_3869196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869196).length < 2 ^ (prefixWord ++ tailWord_3869196).sum := by decide
  have hdescent : baseEnd_3869196 < baseStart_3869196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869226 : List Nat := [3, 1, 4, 1, 1, 2, 4, 6]
def baseStart_3869226 : Nat := 118140960795 + 3869226 * 2 ^ 59
def prefixEnd_3869226 : Nat := 4983230072969 + 3 ^ 40 * 3869226 * 2
def baseEnd_3869226 : Nat := 147168348064695101420797

theorem tailTrace_3869226 : CollatzResearch.WordTrace tailWord_3869226 prefixEnd_3869226 147168348064695101420797 := by
  unfold tailWord_3869226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35280566470115622009010883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94081510586974992024029021 35280566470115622009010883)
  ·
    refine ⟨52920849705173433013516325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35280566470115622009010883 52920849705173433013516325)
    ·
      refine ⟨9922659319720018690034311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52920849705173433013516325 9922659319720018690034311)
      ·
        refine ⟨14883988979580028035051467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9922659319720018690034311 14883988979580028035051467)
        ·
          refine ⟨22325983469370042052577201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14883988979580028035051467 22325983469370042052577201)
          ·
            refine ⟨16744487602027531539432901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22325983469370042052577201 16744487602027531539432901)
            ·
              refine ⟨3139591425380162163643669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16744487602027531539432901 3139591425380162163643669)
              ·
                refine ⟨147168348064695101420797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3139591425380162163643669 147168348064695101420797)
                ·
                  rfl

theorem cell22_3869226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_3869226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869226 prefixEnd_3869226 := by exact prefixLift 3869226
  have htrace : WordTrace (prefixWord ++ tailWord_3869226) baseStart_3869226 baseEnd_3869226 := by
    simpa [prefixWord, tailWord_3869226, baseEnd_3869226] using wordTrace_append hprefix tailTrace_3869226
  have hstable : (prefixWord ++ tailWord_3869226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869226).length < 2 ^ (prefixWord ++ tailWord_3869226).sum := by decide
  have hdescent : baseEnd_3869226 < baseStart_3869226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869258 : List Nat := [3, 1, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_3869258 : Nat := 118140960795 + 3869258 * 2 ^ 59
def prefixEnd_3869258 : Nat := 4983230072969 + 3 ^ 40 * 3869258 * 2
def baseEnd_3869258 : Nat := 1324526086836218495987075

theorem tailTrace_3869258 : CollatzResearch.WordTrace tailWord_3869258 prefixEnd_3869258 1324526086836218495987075 := by
  unfold tailWord_3869258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35280858254086639375302107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94082288677564371667472285 35280858254086639375302107)
  ·
    refine ⟨52921287381129959062953161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35280858254086639375302107 52921287381129959062953161)
    ·
      refine ⟨39690965535847469297214871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52921287381129959062953161 39690965535847469297214871)
      ·
        refine ⟨59536448303771203945822307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39690965535847469297214871 59536448303771203945822307)
        ·
          refine ⟨89304672455656805918733461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59536448303771203945822307 89304672455656805918733461)
          ·
            refine ⟨4186156521358912777440631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89304672455656805918733461 4186156521358912777440631)
            ·
              refine ⟨6279234782038369166160947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186156521358912777440631 6279234782038369166160947)
              ·
                refine ⟨9418852173057553749241421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279234782038369166160947 9418852173057553749241421)
                ·
                  refine ⟨3532069564896582655965533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9418852173057553749241421 3532069564896582655965533)
                  ·
                    refine ⟨1324526086836218495987075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532069564896582655965533 1324526086836218495987075)
                    ·
                      rfl

theorem cell22_3869258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_3869258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869258 prefixEnd_3869258 := by exact prefixLift 3869258
  have htrace : WordTrace (prefixWord ++ tailWord_3869258) baseStart_3869258 baseEnd_3869258 := by
    simpa [prefixWord, tailWord_3869258, baseEnd_3869258] using wordTrace_append hprefix tailTrace_3869258
  have hstable : (prefixWord ++ tailWord_3869258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869258).length < 2 ^ (prefixWord ++ tailWord_3869258).sum := by decide
  have hdescent : baseEnd_3869258 < baseStart_3869258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869269 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3869269 : Nat := 118140960795 + 3869269 * 2 ^ 59
def prefixEnd_3869269 : Nat := 4983230072969 + 3 ^ 40 * 3869269 * 2
def baseEnd_3869269 : Nat := 1324529852361018133962041

theorem tailTrace_3869269 : CollatzResearch.WordTrace tailWord_3869269 prefixEnd_3869269 1324529852361018133962041 := by
  unfold tailWord_3869269
  simp only [CollatzResearch.WordTrace]
  refine ⟨141123834219306706379858861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94082556146204470919905907 141123834219306706379858861)
  ·
    refine ⟨52921437832240014892447073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141123834219306706379858861 52921437832240014892447073)
    ·
      refine ⟨39691078374180011169335305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52921437832240014892447073 39691078374180011169335305)
      ·
        refine ⟨29768308780635008377001479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39691078374180011169335305 29768308780635008377001479)
        ·
          refine ⟨44652463170952512565502219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29768308780635008377001479 44652463170952512565502219)
          ·
            refine ⟨66978694756428768848253329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44652463170952512565502219 66978694756428768848253329)
            ·
              refine ⟨50234021067321576636189997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66978694756428768848253329 50234021067321576636189997)
              ·
                refine ⟨18837757900245591238571249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50234021067321576636189997 18837757900245591238571249)
                ·
                  refine ⟨14128318425184193428928437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18837757900245591238571249 14128318425184193428928437)
                  ·
                    refine ⟨1324529852361018133962041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14128318425184193428928437 1324529852361018133962041)
                    ·
                      rfl

theorem cell22_3869269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3869269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869269 prefixEnd_3869269 := by exact prefixLift 3869269
  have htrace : WordTrace (prefixWord ++ tailWord_3869269) baseStart_3869269 baseEnd_3869269 := by
    simpa [prefixWord, tailWord_3869269, baseEnd_3869269] using wordTrace_append hprefix tailTrace_3869269
  have hstable : (prefixWord ++ tailWord_3869269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869269).length < 2 ^ (prefixWord ++ tailWord_3869269).sum := by decide
  have hdescent : baseEnd_3869269 < baseStart_3869269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869309 : List Nat := [1, 4, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_3869309 : Nat := 118140960795 + 3869309 * 2 ^ 59
def prefixEnd_3869309 : Nat := 4983230072969 + 3 ^ 40 * 3869309 * 2
def baseEnd_3869309 : Nat := 1324543545178471362961919

theorem tailTrace_3869309 : CollatzResearch.WordTrace tailWord_3869309 prefixEnd_3869309 1324543545178471362961919 := by
  unfold tailWord_3869309
  simp only [CollatzResearch.WordTrace]
  refine ⟨141125293139161793211314981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94083528759441195474209987 141125293139161793211314981)
  ·
    refine ⟨26460992463592836227121559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141125293139161793211314981 26460992463592836227121559)
    ·
      refine ⟨39691488695389254340682339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26460992463592836227121559 39691488695389254340682339)
      ·
        refine ⟨59537233043083881511023509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39691488695389254340682339 59537233043083881511023509)
        ·
          refine ⟨2790807798894556945829227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59537233043083881511023509 2790807798894556945829227)
          ·
            refine ⟨4186211698341835418743841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790807798894556945829227 4186211698341835418743841)
            ·
              refine ⟨3139658773756376564057881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4186211698341835418743841 3139658773756376564057881)
              ·
                refine ⟨2354744080317282423043411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139658773756376564057881 2354744080317282423043411)
                ·
                  refine ⟨3532116120475923634565117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354744080317282423043411 3532116120475923634565117)
                  ·
                    refine ⟨1324543545178471362961919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532116120475923634565117 1324543545178471362961919)
                    ·
                      rfl

theorem cell22_3869309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_3869309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869309 prefixEnd_3869309 := by exact prefixLift 3869309
  have htrace : WordTrace (prefixWord ++ tailWord_3869309) baseStart_3869309 baseEnd_3869309 := by
    simpa [prefixWord, tailWord_3869309, baseEnd_3869309] using wordTrace_append hprefix tailTrace_3869309
  have hstable : (prefixWord ++ tailWord_3869309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869309).length < 2 ^ (prefixWord ++ tailWord_3869309).sum := by decide
  have hdescent : baseEnd_3869309 < baseStart_3869309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869365 : List Nat := [1, 3, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3869365 : Nat := 118140960795 + 3869365 * 2 ^ 59
def prefixEnd_3869365 : Nat := 4983230072969 + 3 ^ 40 * 3869365 * 2
def baseEnd_3869365 : Nat := 1324562715122905883561747

theorem tailTrace_3869365 : CollatzResearch.WordTrace tailWord_3869365 prefixEnd_3869365 1324562715122905883561747 := by
  unfold tailWord_3869365
  simp only [CollatzResearch.WordTrace]
  refine ⟨141127335626958914775353549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94084890417972609850235699 141127335626958914775353549)
  ·
    refine ⟨52922750860109593040757581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141127335626958914775353549 52922750860109593040757581)
    ·
      refine ⟨19846031572541097390284093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52922750860109593040757581 19846031572541097390284093)
      ·
        refine ⟨7442261839702911521356535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19846031572541097390284093 7442261839702911521356535)
        ·
          refine ⟨11163392759554367282034803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7442261839702911521356535 11163392759554367282034803)
          ·
            refine ⟨16745089139331550923052205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11163392759554367282034803 16745089139331550923052205)
            ·
              refine ⟨6279408427249331596144577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16745089139331550923052205 6279408427249331596144577)
              ·
                refine ⟨4709556320436998697108433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6279408427249331596144577 4709556320436998697108433)
                ·
                  refine ⟨3532167240327749022831325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4709556320436998697108433 3532167240327749022831325)
                  ·
                    refine ⟨1324562715122905883561747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532167240327749022831325 1324562715122905883561747)
                    ·
                      rfl

theorem cell22_3869365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3869365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869365 prefixEnd_3869365 := by exact prefixLift 3869365
  have htrace : WordTrace (prefixWord ++ tailWord_3869365) baseStart_3869365 baseEnd_3869365 := by
    simpa [prefixWord, tailWord_3869365, baseEnd_3869365] using wordTrace_append hprefix tailTrace_3869365
  have hstable : (prefixWord ++ tailWord_3869365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869365).length < 2 ^ (prefixWord ++ tailWord_3869365).sum := by decide
  have hdescent : baseEnd_3869365 < baseStart_3869365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869483 : List Nat := [1, 1, 1, 1, 2, 1, 2, 8, 2, 3]
def baseStart_3869483 : Nat := 118140960795 + 3869483 * 2 ^ 59
def prefixEnd_3869483 : Nat := 4983230072969 + 3 ^ 40 * 3869483 * 2
def baseEnd_3869483 : Nat := 1324603108934392909111385

theorem tailTrace_3869483 : CollatzResearch.WordTrace tailWord_3869483 prefixEnd_3869483 1324603108934392909111385 := by
  unfold tailWord_3869483
  simp only [CollatzResearch.WordTrace]
  refine ⟨141131639440531420928149103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94087759627020947285432735 141131639440531420928149103)
  ·
    refine ⟨211697459160797131392223655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141131639440531420928149103 211697459160797131392223655)
    ·
      refine ⟨317546188741195697088335483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211697459160797131392223655 317546188741195697088335483)
      ·
        refine ⟨476319283111793545632503225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317546188741195697088335483 476319283111793545632503225)
        ·
          refine ⟨357239462333845159224377419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476319283111793545632503225 357239462333845159224377419)
          ·
            refine ⟨535859193500767738836566129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357239462333845159224377419 535859193500767738836566129)
            ·
              refine ⟨401894395125575804127424597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535859193500767738836566129 401894395125575804127424597)
              ·
                refine ⟨4709699942877841454618257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 401894395125575804127424597 4709699942877841454618257)
                ·
                  refine ⟨3532274957158381090963693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4709699942877841454618257 3532274957158381090963693)
                  ·
                    refine ⟨1324603108934392909111385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532274957158381090963693 1324603108934392909111385)
                    ·
                      rfl

theorem cell22_3869483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2, 3].length) (baseStart_3869483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869483 prefixEnd_3869483 := by exact prefixLift 3869483
  have htrace : WordTrace (prefixWord ++ tailWord_3869483) baseStart_3869483 baseEnd_3869483 := by
    simpa [prefixWord, tailWord_3869483, baseEnd_3869483] using wordTrace_append hprefix tailTrace_3869483
  have hstable : (prefixWord ++ tailWord_3869483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869483).length < 2 ^ (prefixWord ++ tailWord_3869483).sum := by decide
  have hdescent : baseEnd_3869483 < baseStart_3869483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869513 : List Nat := [1, 2, 1, 1, 2, 6, 3, 6]
def baseStart_3869513 : Nat := 118140960795 + 3869513 * 2 ^ 59
def prefixEnd_3869513 : Nat := 4983230072969 + 3 ^ 40 * 3869513 * 2
def baseEnd_3869513 : Nat := 147179264283053647873477

theorem tailTrace_3869513 : CollatzResearch.WordTrace tailWord_3869513 prefixEnd_3869513 147179264283053647873477 := by
  unfold tailWord_3869513
  simp only [CollatzResearch.WordTrace]
  refine ⟨141132733630422736051741193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94088489086948490701160795 141132733630422736051741193)
  ·
    refine ⟨105849550222817052038805895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141132733630422736051741193 105849550222817052038805895)
    ·
      refine ⟨158774325334225578058208843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105849550222817052038805895 158774325334225578058208843)
      ·
        refine ⟨238161488001338367087313265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158774325334225578058208843 238161488001338367087313265)
        ·
          refine ⟨178621116001003775315484949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238161488001338367087313265 178621116001003775315484949)
          ·
            refine ⟨8372864812547051967913357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 178621116001003775315484949 8372864812547051967913357)
            ·
              refine ⟨3139824304705144487967509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8372864812547051967913357 3139824304705144487967509)
              ·
                refine ⟨147179264283053647873477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3139824304705144487967509 147179264283053647873477)
                ·
                  rfl

theorem cell22_3869513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 6].length) (baseStart_3869513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869513 prefixEnd_3869513 := by exact prefixLift 3869513
  have htrace : WordTrace (prefixWord ++ tailWord_3869513) baseStart_3869513 baseEnd_3869513 := by
    simpa [prefixWord, tailWord_3869513, baseEnd_3869513] using wordTrace_append hprefix tailTrace_3869513
  have hstable : (prefixWord ++ tailWord_3869513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869513).length < 2 ^ (prefixWord ++ tailWord_3869513).sum := by decide
  have hdescent : baseEnd_3869513 < baseStart_3869513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869596 : List Nat := [2, 2, 3, 3, 2, 1, 3, 2, 1, 3]
def baseStart_3869596 : Nat := 118140960795 + 3869596 * 2 ^ 59
def prefixEnd_3869596 : Nat := 4983230072969 + 3 ^ 40 * 3869596 * 2
def baseEnd_3869596 : Nat := 1324641791143698281036039

theorem tailTrace_3869596 : CollatzResearch.WordTrace tailWord_3869596 prefixEnd_3869596 1324641791143698281036039 := by
  unfold tailWord_3869596
  simp only [CollatzResearch.WordTrace]
  refine ⟨70567880444561020613506321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94090507259414694151341761 70567880444561020613506321)
  ·
    refine ⟨52925910333420765460129741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70567880444561020613506321 52925910333420765460129741)
    ·
      refine ⟨19847216375032787047548653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52925910333420765460129741 19847216375032787047548653)
      ·
        refine ⟨7442706140637295142830745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19847216375032787047548653 7442706140637295142830745)
        ·
          refine ⟨5582029605477971357123059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7442706140637295142830745 5582029605477971357123059)
          ·
            refine ⟨8373044408216957035684589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582029605477971357123059 8373044408216957035684589)
            ·
              refine ⟨3139891653081358888381721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8373044408216957035684589 3139891653081358888381721)
              ·
                refine ⟨2354918739811019166286291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139891653081358888381721 2354918739811019166286291)
                ·
                  refine ⟨3532378109716528749429437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354918739811019166286291 3532378109716528749429437)
                  ·
                    refine ⟨1324641791143698281036039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532378109716528749429437 1324641791143698281036039)
                    ·
                      rfl

theorem cell22_3869596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_3869596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869596 prefixEnd_3869596 := by exact prefixLift 3869596
  have htrace : WordTrace (prefixWord ++ tailWord_3869596) baseStart_3869596 baseEnd_3869596 := by
    simpa [prefixWord, tailWord_3869596, baseEnd_3869596] using wordTrace_append hprefix tailTrace_3869596
  have hstable : (prefixWord ++ tailWord_3869596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869596).length < 2 ^ (prefixWord ++ tailWord_3869596).sum := by decide
  have hdescent : baseEnd_3869596 < baseStart_3869596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869603 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 6]
def baseStart_3869603 : Nat := 118140960795 + 3869603 * 2 ^ 59
def prefixEnd_3869603 : Nat := 4983230072969 + 3 ^ 40 * 3869603 * 2
def baseEnd_3869603 : Nat := 441548062462250865370339

theorem tailTrace_3869603 : CollatzResearch.WordTrace tailWord_3869603 prefixEnd_3869603 441548062462250865370339 := by
  unfold tailWord_3869603
  simp only [CollatzResearch.WordTrace]
  refine ⟨141136016200096681422517463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94090677466731120948344975 141136016200096681422517463)
  ·
    refine ⟨211704024300145022133776195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141136016200096681422517463 211704024300145022133776195)
    ·
      refine ⟨317556036450217533200664293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211704024300145022133776195 317556036450217533200664293)
      ·
        refine ⟨59541756834415787475124555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317556036450217533200664293 59541756834415787475124555)
        ·
          refine ⟨89312635251623681212686833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59541756834415787475124555 89312635251623681212686833)
          ·
            refine ⟨66984476438717760909515125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89312635251623681212686833 66984476438717760909515125)
            ·
              refine ⟨6279794666129790085267043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66984476438717760909515125 6279794666129790085267043)
              ·
                refine ⟨9419691999194685127900565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279794666129790085267043 9419691999194685127900565)
                ·
                  refine ⟨441548062462250865370339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9419691999194685127900565 441548062462250865370339)
                  ·
                    rfl

theorem cell22_3869603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 6].length) (baseStart_3869603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869603 prefixEnd_3869603 := by exact prefixLift 3869603
  have htrace : WordTrace (prefixWord ++ tailWord_3869603) baseStart_3869603 baseEnd_3869603 := by
    simpa [prefixWord, tailWord_3869603, baseEnd_3869603] using wordTrace_append hprefix tailTrace_3869603
  have hstable : (prefixWord ++ tailWord_3869603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869603).length < 2 ^ (prefixWord ++ tailWord_3869603).sum := by decide
  have hdescent : baseEnd_3869603 < baseStart_3869603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869652 : List Nat := [2, 4, 1, 2, 1, 2, 1, 4, 2, 3]
def baseStart_3869652 : Nat := 118140960795 + 3869652 * 2 ^ 59
def prefixEnd_3869652 : Nat := 4983230072969 + 3 ^ 40 * 3869652 * 2
def baseEnd_3869652 : Nat := 1324660961088132801635867

theorem tailTrace_3869652 : CollatzResearch.WordTrace tailWord_3869652 prefixEnd_3869652 1324660961088132801635867 := by
  unfold tailWord_3869652
  simp only [CollatzResearch.WordTrace]
  refine ⟨70568901688459581395525605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94091868917946108527367473 70568901688459581395525605)
  ·
    refine ⟨13231669066586171511661051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70568901688459581395525605 13231669066586171511661051)
    ·
      refine ⟨19847503599879257267491577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13231669066586171511661051 19847503599879257267491577)
      ·
        refine ⟨14885627699909442950618683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19847503599879257267491577 14885627699909442950618683)
        ·
          refine ⟨22328441549864164425928025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14885627699909442950618683 22328441549864164425928025)
          ·
            refine ⟨16746331162398123319446019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22328441549864164425928025 16746331162398123319446019)
            ·
              refine ⟨25119496743597184979169029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16746331162398123319446019 25119496743597184979169029)
              ·
                refine ⟨4709905639424472183594193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25119496743597184979169029 4709905639424472183594193)
                ·
                  refine ⟨3532429229568354137695645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4709905639424472183594193 3532429229568354137695645)
                  ·
                    refine ⟨1324660961088132801635867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532429229568354137695645 1324660961088132801635867)
                    ·
                      rfl

theorem cell22_3869652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_3869652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869652 prefixEnd_3869652 := by exact prefixLift 3869652
  have htrace : WordTrace (prefixWord ++ tailWord_3869652) baseStart_3869652 baseEnd_3869652 := by
    simpa [prefixWord, tailWord_3869652, baseEnd_3869652] using wordTrace_append hprefix tailTrace_3869652
  have hstable : (prefixWord ++ tailWord_3869652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869652).length < 2 ^ (prefixWord ++ tailWord_3869652).sum := by decide
  have hdescent : baseEnd_3869652 < baseStart_3869652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869654 : List Nat := [5, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3869654 : Nat := 118140960795 + 3869654 * 2 ^ 59
def prefixEnd_3869654 : Nat := 4983230072969 + 3 ^ 40 * 3869654 * 2
def baseEnd_3869654 : Nat := 441553881909668487695287

theorem tailTrace_3869654 : CollatzResearch.WordTrace tailWord_3869654 prefixEnd_3869654 441553881909668487695287 := by
  unfold tailWord_3869654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8821117270181994820789001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94091917548607944755082677 8821117270181994820789001)
  ·
    refine ⟨6615837952636496115591751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8821117270181994820789001 6615837952636496115591751)
    ·
      refine ⟨9923756928954744173387627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6615837952636496115591751 9923756928954744173387627)
      ·
        refine ⟨14885635393432116260081441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9923756928954744173387627 14885635393432116260081441)
        ·
          refine ⟨11164226545074087195061081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14885635393432116260081441 11164226545074087195061081)
          ·
            refine ⟨8373169908805565396295811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11164226545074087195061081 8373169908805565396295811)
            ·
              refine ⟨12559754863208348094443717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373169908805565396295811 12559754863208348094443717)
              ·
                refine ⟨2354954036851565267708197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12559754863208348094443717 2354954036851565267708197)
                ·
                  refine ⟨441553881909668487695287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2354954036851565267708197 441553881909668487695287)
                  ·
                    rfl

theorem cell22_3869654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3869654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869654 prefixEnd_3869654 := by exact prefixLift 3869654
  have htrace : WordTrace (prefixWord ++ tailWord_3869654) baseStart_3869654 baseEnd_3869654 := by
    simpa [prefixWord, tailWord_3869654, baseEnd_3869654] using wordTrace_append hprefix tailTrace_3869654
  have hstable : (prefixWord ++ tailWord_3869654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869654).length < 2 ^ (prefixWord ++ tailWord_3869654).sum := by decide
  have hdescent : baseEnd_3869654 < baseStart_3869654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869693 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 7]
def baseStart_3869693 : Nat := 118140960795 + 3869693 * 2 ^ 59
def prefixEnd_3869693 : Nat := 4983230072969 + 3 ^ 40 * 3869693 * 2
def baseEnd_3869693 : Nat := 441558332075340787120247

theorem tailTrace_3869693 : CollatzResearch.WordTrace tailWord_3869693 prefixEnd_3869693 441558332075340787120247 := by
  unfold tailWord_3869693
  simp only [CollatzResearch.WordTrace]
  refine ⟨141139298769770626793293733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94092865846513751195529155 141139298769770626793293733)
  ·
    refine ⟨26463618519331992523742575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141139298769770626793293733 26463618519331992523742575)
    ·
      refine ⟨39695427778997988785613863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26463618519331992523742575 39695427778997988785613863)
      ·
        refine ⟨59543141668496983178420795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39695427778997988785613863 59543141668496983178420795)
        ·
          refine ⟨89314712502745474767631193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59543141668496983178420795 89314712502745474767631193)
          ·
            refine ⟨66986034377059106075723395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89314712502745474767631193 66986034377059106075723395)
            ·
              refine ⟨100479051565588659113585093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66986034377059106075723395 100479051565588659113585093)
              ·
                refine ⟨18839822168547873583797205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100479051565588659113585093 18839822168547873583797205)
                ·
                  refine ⟨441558332075340787120247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18839822168547873583797205 441558332075340787120247)
                  ·
                    rfl

theorem cell22_3869693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_3869693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869693 prefixEnd_3869693 := by exact prefixLift 3869693
  have htrace : WordTrace (prefixWord ++ tailWord_3869693) baseStart_3869693 baseEnd_3869693 := by
    simpa [prefixWord, tailWord_3869693, baseEnd_3869693] using wordTrace_append hprefix tailTrace_3869693
  have hstable : (prefixWord ++ tailWord_3869693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869693).length < 2 ^ (prefixWord ++ tailWord_3869693).sum := by decide
  have hdescent : baseEnd_3869693 < baseStart_3869693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869710 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_3869710 : Nat := 118140960795 + 3869710 * 2 ^ 59
def prefixEnd_3869710 : Nat := 4983230072969 + 3 ^ 40 * 3869710 * 2
def baseEnd_3869710 : Nat := 441560271891146661228563

theorem tailTrace_3869710 : CollatzResearch.WordTrace tailWord_3869710 prefixEnd_3869710 441560271891146661228563 := by
  unfold tailWord_3869710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17642489851338629837082823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94093279207139359131108389 17642489851338629837082823)
  ·
    refine ⟨26463734777007944755624235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17642489851338629837082823 26463734777007944755624235)
    ·
      refine ⟨39695602165511917133436353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26463734777007944755624235 39695602165511917133436353)
      ·
        refine ⟨29771701624133937850077265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39695602165511917133436353 29771701624133937850077265)
        ·
          refine ⟨22328776218100453387557949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29771701624133937850077265 22328776218100453387557949)
          ·
            refine ⟨8373291081787670020334231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22328776218100453387557949 8373291081787670020334231)
            ·
              refine ⟨12559936622681505030501347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373291081787670020334231 12559936622681505030501347)
              ·
                refine ⟨18839904934022257545752021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12559936622681505030501347 18839904934022257545752021)
                ·
                  refine ⟨441560271891146661228563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18839904934022257545752021 441560271891146661228563)
                  ·
                    rfl

theorem cell22_3869710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_3869710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869710 prefixEnd_3869710 := by exact prefixLift 3869710
  have htrace : WordTrace (prefixWord ++ tailWord_3869710) baseStart_3869710 baseEnd_3869710 := by
    simpa [prefixWord, tailWord_3869710, baseEnd_3869710] using wordTrace_append hprefix tailTrace_3869710
  have hstable : (prefixWord ++ tailWord_3869710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869710).length < 2 ^ (prefixWord ++ tailWord_3869710).sum := by decide
  have hdescent : baseEnd_3869710 < baseStart_3869710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869727 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 5]
def baseStart_3869727 : Nat := 118140960795 + 3869727 * 2 ^ 59
def prefixEnd_3869727 : Nat := 4983230072969 + 3 ^ 40 * 3869727 * 2
def baseEnd_3869727 : Nat := 441562211706952535336879

theorem tailTrace_3869727 : CollatzResearch.WordTrace tailWord_3869727 prefixEnd_3869727 441562211706952535336879 := by
  unfold tailWord_3869727
  simp only [CollatzResearch.WordTrace]
  refine ⟨141140538851647450600031435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94093692567764967066687623 141140538851647450600031435)
  ·
    refine ⟨211710808277471175900047153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141140538851647450600031435 211710808277471175900047153)
    ·
      refine ⟨158783106208103381925035365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211710808277471175900047153 158783106208103381925035365)
      ·
        refine ⟨29771832414019384110944131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158783106208103381925035365 29771832414019384110944131)
        ·
          refine ⟨44657748621029076166416197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29771832414019384110944131 44657748621029076166416197)
          ·
            refine ⟨8373327866442951781203037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44657748621029076166416197 8373327866442951781203037)
            ·
              refine ⟨3139997949916106917951139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8373327866442951781203037 3139997949916106917951139)
              ·
                refine ⟨4709996924874160376926709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139997949916106917951139 4709996924874160376926709)
                ·
                  refine ⟨441562211706952535336879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4709996924874160376926709 441562211706952535336879)
                  ·
                    rfl

theorem cell22_3869727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 5].length) (baseStart_3869727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869727 prefixEnd_3869727 := by exact prefixLift 3869727
  have htrace : WordTrace (prefixWord ++ tailWord_3869727) baseStart_3869727 baseEnd_3869727 := by
    simpa [prefixWord, tailWord_3869727, baseEnd_3869727] using wordTrace_append hprefix tailTrace_3869727
  have hstable : (prefixWord ++ tailWord_3869727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869727).length < 2 ^ (prefixWord ++ tailWord_3869727).sum := by decide
  have hdescent : baseEnd_3869727 < baseStart_3869727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869748 : List Nat := [2, 5, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_3869748 : Nat := 118140960795 + 3869748 * 2 ^ 59
def prefixEnd_3869748 : Nat := 4983230072969 + 3 ^ 40 * 3869748 * 2
def baseEnd_3869748 : Nat := 1324693823850020551235573

theorem tailTrace_3869748 : CollatzResearch.WordTrace tailWord_3869748 prefixEnd_3869748 1324693823850020551235573 := by
  unfold tailWord_3869748
  simp only [CollatzResearch.WordTrace]
  refine ⟨70570652392285685593272949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94094203189714247457697265 70570652392285685593272949)
  ·
    refine ⟨6615998661776783024369339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70570652392285685593272949 6615998661776783024369339)
    ·
      refine ⟨9923997992665174536554009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6615998661776783024369339 9923997992665174536554009)
      ·
        refine ⟨7442998494498880902415507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9923997992665174536554009 7442998494498880902415507)
        ·
          refine ⟨11164497741748321353623261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7442998494498880902415507 11164497741748321353623261)
          ·
            refine ⟨4186686653155620507608723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11164497741748321353623261 4186686653155620507608723)
            ·
              refine ⟨6280029979733430761413085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186686653155620507608723 6280029979733430761413085)
              ·
                refine ⟨2355011242400036535529907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6280029979733430761413085 2355011242400036535529907)
                ·
                  refine ⟨3532516863600054803294861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355011242400036535529907 3532516863600054803294861)
                  ·
                    refine ⟨1324693823850020551235573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532516863600054803294861 1324693823850020551235573)
                    ·
                      rfl

theorem cell22_3869748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_3869748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869748 prefixEnd_3869748 := by exact prefixLift 3869748
  have htrace : WordTrace (prefixWord ++ tailWord_3869748) baseStart_3869748 baseEnd_3869748 := by
    simpa [prefixWord, tailWord_3869748, baseEnd_3869748] using wordTrace_append hprefix tailTrace_3869748
  have hstable : (prefixWord ++ tailWord_3869748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869748).length < 2 ^ (prefixWord ++ tailWord_3869748).sum := by decide
  have hdescent : baseEnd_3869748 < baseStart_3869748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869757 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3869757 : Nat := 118140960795 + 3869757 * 2 ^ 59
def prefixEnd_3869757 : Nat := 4983230072969 + 3 ^ 40 * 3869757 * 2
def baseEnd_3869757 : Nat := 1324696904733947527760545

theorem tailTrace_3869757 : CollatzResearch.WordTrace tailWord_3869757 prefixEnd_3869757 1324696904733947527760545 := by
  unfold tailWord_3869757
  simp only [CollatzResearch.WordTrace]
  refine ⟨141141633041538765723623525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94094422027692510482415683 141141633041538765723623525)
  ·
    refine ⟨26464056195288518573179411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141141633041538765723623525 26464056195288518573179411)
    ·
      refine ⟨39696084292932777859769117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26464056195288518573179411 39696084292932777859769117)
      ·
        refine ⟨14886031609849791697413419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39696084292932777859769117 14886031609849791697413419)
        ·
          refine ⟨22329047414774687546120129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14886031609849791697413419 22329047414774687546120129)
          ·
            refine ⟨16746785561081015659590097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22329047414774687546120129 16746785561081015659590097)
            ·
              refine ⟨12560089170810761744692573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16746785561081015659590097 12560089170810761744692573)
              ·
                refine ⟨4710033439054035654259715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12560089170810761744692573 4710033439054035654259715)
                ·
                  refine ⟨7065050158581053481389573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710033439054035654259715 7065050158581053481389573)
                  ·
                    refine ⟨1324696904733947527760545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7065050158581053481389573 1324696904733947527760545)
                    ·
                      rfl

theorem cell22_3869757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3869757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869757 prefixEnd_3869757 := by exact prefixLift 3869757
  have htrace : WordTrace (prefixWord ++ tailWord_3869757) baseStart_3869757 baseEnd_3869757 := by
    simpa [prefixWord, tailWord_3869757, baseEnd_3869757] using wordTrace_append hprefix tailTrace_3869757
  have hstable : (prefixWord ++ tailWord_3869757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869757).length < 2 ^ (prefixWord ++ tailWord_3869757).sum := by decide
  have hdescent : baseEnd_3869757 < baseStart_3869757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869802 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_3869802 : Nat := 118140960795 + 3869802 * 2 ^ 59
def prefixEnd_3869802 : Nat := 4983230072969 + 3 ^ 40 * 3869802 * 2
def baseEnd_3869802 : Nat := 1324712309153582410385407

theorem tailTrace_3869802 : CollatzResearch.WordTrace tailWord_3869802 prefixEnd_3869802 1324712309153582410385407 := by
  unfold tailWord_3869802
  simp only [CollatzResearch.WordTrace]
  refine ⟨35285818581593934602252915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94095516217583825606007773 35285818581593934602252915)
  ·
    refine ⟨52928727872390901903379373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35285818581593934602252915 52928727872390901903379373)
    ·
      refine ⟨19848272952146588213767265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52928727872390901903379373 19848272952146588213767265)
      ·
        refine ⟨14886204714109941160325449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19848272952146588213767265 14886204714109941160325449)
        ·
          refine ⟨11164653535582455870244087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14886204714109941160325449 11164653535582455870244087)
          ·
            refine ⟨16746980303373683805366131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11164653535582455870244087 16746980303373683805366131)
            ·
              refine ⟨25120470455060525708049197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16746980303373683805366131 25120470455060525708049197)
              ·
                refine ⟨9420176420647697140518449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25120470455060525708049197 9420176420647697140518449)
                ·
                  refine ⟨7065132315485772855388837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420176420647697140518449 7065132315485772855388837)
                  ·
                    refine ⟨1324712309153582410385407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7065132315485772855388837 1324712309153582410385407)
                    ·
                      rfl

theorem cell22_3869802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_3869802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869802 prefixEnd_3869802 := by exact prefixLift 3869802
  have htrace : WordTrace (prefixWord ++ tailWord_3869802) baseStart_3869802 baseEnd_3869802 := by
    simpa [prefixWord, tailWord_3869802, baseEnd_3869802] using wordTrace_append hprefix tailTrace_3869802
  have hstable : (prefixWord ++ tailWord_3869802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869802).length < 2 ^ (prefixWord ++ tailWord_3869802).sum := by decide
  have hdescent : baseEnd_3869802 < baseStart_3869802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869909 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_3869909 : Nat := 118140960795 + 3869909 * 2 ^ 59
def prefixEnd_3869909 : Nat := 4983230072969 + 3 ^ 40 * 3869909 * 2
def baseEnd_3869909 : Nat := 1324748937440269797960079

theorem tailTrace_3869909 : CollatzResearch.WordTrace tailWord_3869909 prefixEnd_3869909 1324748937440269797960079 := by
  unfold tailWord_3869909
  simp only [CollatzResearch.WordTrace]
  refine ⟨141147176936988095683156781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94098117957992063788771187 141147176936988095683156781)
  ·
    refine ⟨52930191351370535881183793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141147176936988095683156781 52930191351370535881183793)
    ·
      refine ⟨39697643513527901910887845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52930191351370535881183793 39697643513527901910887845)
      ·
        refine ⟨7443308158786481608291471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39697643513527901910887845 7443308158786481608291471)
        ·
          refine ⟨11164962238179722412437207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443308158786481608291471 11164962238179722412437207)
          ·
            refine ⟨16747443357269583618655811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11164962238179722412437207 16747443357269583618655811)
            ·
              refine ⟨25121165035904375427983717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16747443357269583618655811 25121165035904375427983717)
              ·
                refine ⟨4710218444232070392746947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25121165035904375427983717 4710218444232070392746947)
                ·
                  refine ⟨7065327666348105589120421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710218444232070392746947 7065327666348105589120421)
                  ·
                    refine ⟨1324748937440269797960079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7065327666348105589120421 1324748937440269797960079)
                    ·
                      rfl

theorem cell22_3869909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_3869909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869909 prefixEnd_3869909 := by exact prefixLift 3869909
  have htrace : WordTrace (prefixWord ++ tailWord_3869909) baseStart_3869909 baseEnd_3869909 := by
    simpa [prefixWord, tailWord_3869909, baseEnd_3869909] using wordTrace_append hprefix tailTrace_3869909
  have hstable : (prefixWord ++ tailWord_3869909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869909).length < 2 ^ (prefixWord ++ tailWord_3869909).sum := by decide
  have hdescent : baseEnd_3869909 < baseStart_3869909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869924 : List Nat := [2, 3, 1, 1, 1, 2, 5, 3, 4]
def baseStart_3869924 : Nat := 118140960795 + 3869924 * 2 ^ 59
def prefixEnd_3869924 : Nat := 4983230072969 + 3 ^ 40 * 3869924 * 2
def baseEnd_3869924 : Nat := 441584690748938252945011

theorem tailTrace_3869924 : CollatzResearch.WordTrace tailWord_3869924 prefixEnd_3869924 441584690748938252945011 := by
  unfold tailWord_3869924
  simp only [CollatzResearch.WordTrace]
  refine ⟨70573862015966876622476413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94098482687955835496635217 70573862015966876622476413)
  ·
    refine ⟨26465198255987578733428655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70573862015966876622476413 26465198255987578733428655)
    ·
      refine ⟨39697797383981368100142983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26465198255987578733428655 39697797383981368100142983)
      ·
        refine ⟨59546696075972052150214475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39697797383981368100142983 59546696075972052150214475)
        ·
          refine ⟨89320044113958078225321713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59546696075972052150214475 89320044113958078225321713)
          ·
            refine ⟨66990033085468558668991285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89320044113958078225321713 66990033085468558668991285)
            ·
              refine ⟨6280315601762677375217933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66990033085468558668991285 6280315601762677375217933)
              ·
                refine ⟨2355118350661004015706725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6280315601762677375217933 2355118350661004015706725)
                ·
                  refine ⟨441584690748938252945011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2355118350661004015706725 441584690748938252945011)
                  ·
                    rfl

theorem cell22_3869924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_3869924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869924 prefixEnd_3869924 := by exact prefixLift 3869924
  have htrace : WordTrace (prefixWord ++ tailWord_3869924) baseStart_3869924 baseEnd_3869924 := by
    simpa [prefixWord, tailWord_3869924, baseEnd_3869924] using wordTrace_append hprefix tailTrace_3869924
  have hstable : (prefixWord ++ tailWord_3869924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869924).length < 2 ^ (prefixWord ++ tailWord_3869924).sum := by decide
  have hdescent : baseEnd_3869924 < baseStart_3869924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3869956 : List Nat := [2, 3, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_3869956 : Nat := 118140960795 + 3869956 * 2 ^ 59
def prefixEnd_3869956 : Nat := 4983230072969 + 3 ^ 40 * 3869956 * 2
def baseEnd_3869956 : Nat := 1324765026500777342034935

theorem tailTrace_3869956 : CollatzResearch.WordTrace tailWord_3869956 prefixEnd_3869956 1324765026500777342034935 := by
  unfold tailWord_3869956
  simp only [CollatzResearch.WordTrace]
  refine ⟨70574445583908911355058861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94099260778545215140078481 70574445583908911355058861)
  ·
    refine ⟨26465417093965841758147073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70574445583908911355058861 26465417093965841758147073)
    ·
      refine ⟨19849062820474381318610305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26465417093965841758147073 19849062820474381318610305)
      ·
        refine ⟨14886797115355785988957729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19849062820474381318610305 14886797115355785988957729)
        ·
          refine ⟨11165097836516839491718297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14886797115355785988957729 11165097836516839491718297)
          ·
            refine ⟨8373823377387629618788723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11165097836516839491718297 8373823377387629618788723)
            ·
              refine ⟨12560735066081444428183085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373823377387629618788723 12560735066081444428183085)
              ·
                refine ⟨4710275649780541660568657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12560735066081444428183085 4710275649780541660568657)
                ·
                  refine ⟨3532706737335406245426493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710275649780541660568657 3532706737335406245426493)
                  ·
                    refine ⟨1324765026500777342034935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532706737335406245426493 1324765026500777342034935)
                    ·
                      rfl

theorem cell22_3869956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_3869956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3869956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3869956 prefixEnd_3869956 := by exact prefixLift 3869956
  have htrace : WordTrace (prefixWord ++ tailWord_3869956) baseStart_3869956 baseEnd_3869956 := by
    simpa [prefixWord, tailWord_3869956, baseEnd_3869956] using wordTrace_append hprefix tailTrace_3869956
  have hstable : (prefixWord ++ tailWord_3869956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3869956).length < 2 ^ (prefixWord ++ tailWord_3869956).sum := by decide
  have hdescent : baseEnd_3869956 < baseStart_3869956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3869956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870012 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_3870012 : Nat := 118140960795 + 3870012 * 2 ^ 59
def prefixEnd_3870012 : Nat := 4983230072969 + 3 ^ 40 * 3870012 * 2
def baseEnd_3870012 : Nat := 1324784196445211862634763

theorem tailTrace_3870012 : CollatzResearch.WordTrace tailWord_3870012 prefixEnd_3870012 1324784196445211862634763 := by
  unfold tailWord_3870012
  simp only [CollatzResearch.WordTrace]
  refine ⟨70575466827807472137078145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94100622437076629516104193 70575466827807472137078145)
  ·
    refine ⟨52931600120855604102808609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70575466827807472137078145 52931600120855604102808609)
    ·
      refine ⟨39698700090641703077106457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52931600120855604102808609 39698700090641703077106457)
      ·
        refine ⟨29774025067981277307829843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39698700090641703077106457 29774025067981277307829843)
        ·
          refine ⟨44661037601971915961744765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29774025067981277307829843 44661037601971915961744765)
          ·
            refine ⟨16747889100739468485654287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44661037601971915961744765 16747889100739468485654287)
            ·
              refine ⟨25121833651109202728481431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16747889100739468485654287 25121833651109202728481431)
              ·
                refine ⟨37682750476663804092722147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25121833651109202728481431 37682750476663804092722147)
                ·
                  refine ⟨56524125714995706139083221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37682750476663804092722147 56524125714995706139083221)
                  ·
                    refine ⟨1324784196445211862634763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56524125714995706139083221 1324784196445211862634763)
                    ·
                      rfl

theorem cell22_3870012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_3870012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870012 prefixEnd_3870012 := by exact prefixLift 3870012
  have htrace : WordTrace (prefixWord ++ tailWord_3870012) baseStart_3870012 baseEnd_3870012 := by
    simpa [prefixWord, tailWord_3870012, baseEnd_3870012] using wordTrace_append hprefix tailTrace_3870012
  have hstable : (prefixWord ++ tailWord_3870012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870012).length < 2 ^ (prefixWord ++ tailWord_3870012).sum := by decide
  have hdescent : baseEnd_3870012 < baseStart_3870012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870014 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_3870014 : Nat := 118140960795 + 3870014 * 2 ^ 59
def prefixEnd_3870014 : Nat := 4983230072969 + 3 ^ 40 * 3870014 * 2
def baseEnd_3870014 : Nat := 441594960362028174694919

theorem tailTrace_3870014 : CollatzResearch.WordTrace tailWord_3870014 prefixEnd_3870014 441594960362028174694919 := by
  unfold tailWord_3870014
  simp only [CollatzResearch.WordTrace]
  refine ⟨17643875825200962326966137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94100671067738465743819397 17643875825200962326966137)
  ·
    refine ⟨13232906868900721745224603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17643875825200962326966137 13232906868900721745224603)
    ·
      refine ⟨19849360303351082617836905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13232906868900721745224603 19849360303351082617836905)
      ·
        refine ⟨14887020227513311963377679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19849360303351082617836905 14887020227513311963377679)
        ·
          refine ⟨22330530341269967945066519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14887020227513311963377679 22330530341269967945066519)
          ·
            refine ⟨33495795511904951917599779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22330530341269967945066519 33495795511904951917599779)
            ·
              refine ⟨50243693267857427876399669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33495795511904951917599779 50243693267857427876399669)
              ·
                refine ⟨4710346243861633863412469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50243693267857427876399669 4710346243861633863412469)
                ·
                  refine ⟨441594960362028174694919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4710346243861633863412469 441594960362028174694919)
                  ·
                    rfl

theorem cell22_3870014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_3870014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870014 prefixEnd_3870014 := by exact prefixLift 3870014
  have htrace : WordTrace (prefixWord ++ tailWord_3870014) baseStart_3870014 baseEnd_3870014 := by
    simpa [prefixWord, tailWord_3870014, baseEnd_3870014] using wordTrace_append hprefix tailTrace_3870014
  have hstable : (prefixWord ++ tailWord_3870014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870014).length < 2 ^ (prefixWord ++ tailWord_3870014).sum := by decide
  have hdescent : baseEnd_3870014 < baseStart_3870014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870022 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3870022 : Nat := 118140960795 + 3870022 * 2 ^ 59
def prefixEnd_3870022 : Nat := 4983230072969 + 3 ^ 40 * 3870022 * 2
def baseEnd_3870022 : Nat := 1324787619649575169884733

theorem tailTrace_3870022 : CollatzResearch.WordTrace tailWord_3870022 prefixEnd_3870022 1324787619649575169884733 := by
  unfold tailWord_3870022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410978074549334874438135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94100865590385810654680213 4410978074549334874438135)
  ·
    refine ⟨6616467111824002311657203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4410978074549334874438135 6616467111824002311657203)
    ·
      refine ⟨9924700667736003467485805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6616467111824002311657203 9924700667736003467485805)
      ·
        refine ⟨3721762750401001300307177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9924700667736003467485805 3721762750401001300307177)
        ·
          refine ⟨2791322062800750975230383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721762750401001300307177 2791322062800750975230383)
          ·
            refine ⟨4186983094201126462845575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791322062800750975230383 4186983094201126462845575)
            ·
              refine ⟨6280474641301689694268363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186983094201126462845575 6280474641301689694268363)
              ·
                refine ⟨9420711961952534541402545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280474641301689694268363 9420711961952534541402545)
                ·
                  refine ⟨7065533971464400906051909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420711961952534541402545 7065533971464400906051909)
                  ·
                    refine ⟨1324787619649575169884733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7065533971464400906051909 1324787619649575169884733)
                    ·
                      rfl

theorem cell22_3870022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3870022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870022 prefixEnd_3870022 := by exact prefixLift 3870022
  have htrace : WordTrace (prefixWord ++ tailWord_3870022) baseStart_3870022 baseEnd_3870022 := by
    simpa [prefixWord, tailWord_3870022, baseEnd_3870022] using wordTrace_append hprefix tailTrace_3870022
  have hstable : (prefixWord ++ tailWord_3870022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870022).length < 2 ^ (prefixWord ++ tailWord_3870022).sum := by decide
  have hdescent : baseEnd_3870022 < baseStart_3870022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870110 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3870110 : Nat := 118140960795 + 3870110 * 2 ^ 59
def prefixEnd_3870110 : Nat := 4983230072969 + 3 ^ 40 * 3870110 * 2
def baseEnd_3870110 : Nat := 441605914615990757894821

theorem tailTrace_3870110 : CollatzResearch.WordTrace tailWord_3870110 prefixEnd_3870110 441605914615990757894821 := by
  unfold tailWord_3870110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17644313501157488376402973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94103005339506604674149189 17644313501157488376402973)
  ·
    refine ⟨6616617562934058141151115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17644313501157488376402973 6616617562934058141151115)
    ·
      refine ⟨9924926344401087211726673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6616617562934058141151115 9924926344401087211726673)
      ·
        refine ⟨7443694758300815408795005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9924926344401087211726673 7443694758300815408795005)
        ·
          refine ⟨2791385534362805778298127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7443694758300815408795005 2791385534362805778298127)
          ·
            refine ⟨4187078301544208667447191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791385534362805778298127 4187078301544208667447191)
            ·
              refine ⟨6280617452316313001170787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187078301544208667447191 6280617452316313001170787)
              ·
                refine ⟨9420926178474469501756181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280617452316313001170787 9420926178474469501756181)
                ·
                  refine ⟨441605914615990757894821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9420926178474469501756181 441605914615990757894821)
                  ·
                    rfl

theorem cell22_3870110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3870110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870110 prefixEnd_3870110 := by exact prefixLift 3870110
  have htrace : WordTrace (prefixWord ++ tailWord_3870110) baseStart_3870110 baseEnd_3870110 := by
    simpa [prefixWord, tailWord_3870110, baseEnd_3870110] using wordTrace_append hprefix tailTrace_3870110
  have hstable : (prefixWord ++ tailWord_3870110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870110).length < 2 ^ (prefixWord ++ tailWord_3870110).sum := by decide
  have hdescent : baseEnd_3870110 < baseStart_3870110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870125 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_3870125 : Nat := 118140960795 + 3870125 * 2 ^ 59
def prefixEnd_3870125 : Nat := 4983230072969 + 3 ^ 40 * 3870125 * 2
def baseEnd_3870125 : Nat := 1324822878654517234559417

theorem tailTrace_3870125 : CollatzResearch.WordTrace tailWord_3870125 prefixEnd_3870125 1324822878654517234559417 := by
  unfold tailWord_3870125
  simp only [CollatzResearch.WordTrace]
  refine ⟨141155055104205564573019829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94103370069470376382013219 141155055104205564573019829)
  ·
    refine ⟨13233286416019271678720609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141155055104205564573019829 13233286416019271678720609)
    ·
      refine ⟨9924964812014453759040457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13233286416019271678720609 9924964812014453759040457)
      ·
        refine ⟨7443723609010840319280343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9924964812014453759040457 7443723609010840319280343)
        ·
          refine ⟨11165585413516260478920515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443723609010840319280343 11165585413516260478920515)
          ·
            refine ⟨16748378120274390718380773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11165585413516260478920515 16748378120274390718380773)
            ·
              refine ⟨3140320897551448259696395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16748378120274390718380773 3140320897551448259696395)
              ·
                refine ⟨4710481346327172389544593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3140320897551448259696395 4710481346327172389544593)
                ·
                  refine ⟨3532861009745379292158445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710481346327172389544593 3532861009745379292158445)
                  ·
                    refine ⟨1324822878654517234559417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532861009745379292158445 1324822878654517234559417)
                    ·
                      rfl

theorem cell22_3870125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_3870125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870125 prefixEnd_3870125 := by exact prefixLift 3870125
  have htrace : WordTrace (prefixWord ++ tailWord_3870125) baseStart_3870125 baseEnd_3870125 := by
    simpa [prefixWord, tailWord_3870125, baseEnd_3870125] using wordTrace_append hprefix tailTrace_3870125
  have hstable : (prefixWord ++ tailWord_3870125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870125).length < 2 ^ (prefixWord ++ tailWord_3870125).sum := by decide
  have hdescent : baseEnd_3870125 < baseStart_3870125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870170 : List Nat := [3, 1, 1, 2, 3, 2, 4, 2, 1, 3]
def baseStart_3870170 : Nat := 118140960795 + 3870170 * 2 ^ 59
def prefixEnd_3870170 : Nat := 4983230072969 + 3 ^ 40 * 3870170 * 2
def baseEnd_3870170 : Nat := 1324838283074152117184279

theorem tailTrace_3870170 : CollatzResearch.WordTrace tailWord_3870170 prefixEnd_3870170 1324838283074152117184279 := by
  unfold tailWord_3870170
  simp only [CollatzResearch.WordTrace]
  refine ⟨35289174097260634314601991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94104464259361691505605309 35289174097260634314601991)
  ·
    refine ⟨52933761145890951471902987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35289174097260634314601991 52933761145890951471902987)
    ·
      refine ⟨79400641718836427207854481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52933761145890951471902987 79400641718836427207854481)
      ·
        refine ⟨59550481289127320405890861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79400641718836427207854481 59550481289127320405890861)
        ·
          refine ⟨22331430483422745152209073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59550481289127320405890861 22331430483422745152209073)
          ·
            refine ⟨16748572862567058864156805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22331430483422745152209073 16748572862567058864156805)
            ·
              refine ⟨3140357411731323537029401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16748572862567058864156805 3140357411731323537029401)
              ·
                refine ⟨2355268058798492652772051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3140357411731323537029401 2355268058798492652772051)
                ·
                  refine ⟨3532902088197738979158077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355268058798492652772051 3532902088197738979158077)
                  ·
                    refine ⟨1324838283074152117184279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532902088197738979158077 1324838283074152117184279)
                    ·
                      rfl

theorem cell22_3870170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_3870170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870170 prefixEnd_3870170 := by exact prefixLift 3870170
  have htrace : WordTrace (prefixWord ++ tailWord_3870170) baseStart_3870170 baseEnd_3870170 := by
    simpa [prefixWord, tailWord_3870170, baseEnd_3870170] using wordTrace_append hprefix tailTrace_3870170
  have hstable : (prefixWord ++ tailWord_3870170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870170).length < 2 ^ (prefixWord ++ tailWord_3870170).sum := by decide
  have hdescent : baseEnd_3870170 < baseStart_3870170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870181 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_3870181 : Nat := 118140960795 + 3870181 * 2 ^ 59
def prefixEnd_3870181 : Nat := 4983230072969 + 3 ^ 40 * 3870181 * 2
def baseEnd_3870181 : Nat := 1324842048598951755159245

theorem tailTrace_3870181 : CollatzResearch.WordTrace tailWord_3870181 prefixEnd_3870181 1324842048598951755159245 := by
  unfold tailWord_3870181
  simp only [CollatzResearch.WordTrace]
  refine ⟨141157097592002686137058397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94104731728001790758038931 141157097592002686137058397)
  ·
    refine ⟨52933911597001007301396899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141157097592002686137058397 52933911597001007301396899)
    ·
      refine ⟨79400867395501510952095349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52933911597001007301396899 79400867395501510952095349)
      ·
        refine ⟨7443831318328266651758939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79400867395501510952095349 7443831318328266651758939)
        ·
          refine ⟨11165746977492399977638409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443831318328266651758939 11165746977492399977638409)
          ·
            refine ⟨8374310233119299983228807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11165746977492399977638409 8374310233119299983228807)
            ·
              refine ⟨12561465349678949974843211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374310233119299983228807 12561465349678949974843211)
              ·
                refine ⟨18842198024518424962264817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12561465349678949974843211 18842198024518424962264817)
                ·
                  refine ⟨14131648518388818721698613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18842198024518424962264817 14131648518388818721698613)
                  ·
                    refine ⟨1324842048598951755159245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14131648518388818721698613 1324842048598951755159245)
                    ·
                      rfl

theorem cell22_3870181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_3870181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870181 prefixEnd_3870181 := by exact prefixLift 3870181
  have htrace : WordTrace (prefixWord ++ tailWord_3870181) baseStart_3870181 baseEnd_3870181 := by
    simpa [prefixWord, tailWord_3870181, baseEnd_3870181] using wordTrace_append hprefix tailTrace_3870181
  have hstable : (prefixWord ++ tailWord_3870181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870181).length < 2 ^ (prefixWord ++ tailWord_3870181).sum := by decide
  have hdescent : baseEnd_3870181 < baseStart_3870181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870243 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 1, 5]
def baseStart_3870243 : Nat := 118140960795 + 3870243 * 2 ^ 59
def prefixEnd_3870243 : Nat := 4983230072969 + 3 ^ 40 * 3870243 * 2
def baseEnd_3870243 : Nat := 1324863272466004260109055

theorem tailTrace_3870243 : CollatzResearch.WordTrace tailWord_3870243 prefixEnd_3870243 1324863272466004260109055 := by
  unfold tailWord_3870243
  simp only [CollatzResearch.WordTrace]
  refine ⟨141159358917778070725815383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94106239278518713817210255 141159358917778070725815383)
  ·
    refine ⟨211739038376667106088723075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141159358917778070725815383 211739038376667106088723075)
    ·
      refine ⟨317608557565000659133084613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211739038376667106088723075 317608557565000659133084613)
      ·
        refine ⟨59551604543437623587453365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317608557565000659133084613 59551604543437623587453365)
        ·
          refine ⟨5582962925947277211323753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59551604543437623587453365 5582962925947277211323753)
          ·
            refine ⟨4187222194460457908492815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5582962925947277211323753 4187222194460457908492815)
            ·
              refine ⟨6280833291690686862739223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187222194460457908492815 6280833291690686862739223)
              ·
                refine ⟨9421249937536030294108835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280833291690686862739223 9421249937536030294108835)
                ·
                  refine ⟨14131874906304045441163253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421249937536030294108835 14131874906304045441163253)
                  ·
                    refine ⟨1324863272466004260109055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14131874906304045441163253 1324863272466004260109055)
                    ·
                      rfl

theorem cell22_3870243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 5].length) (baseStart_3870243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870243 prefixEnd_3870243 := by exact prefixLift 3870243
  have htrace : WordTrace (prefixWord ++ tailWord_3870243) baseStart_3870243 baseEnd_3870243 := by
    simpa [prefixWord, tailWord_3870243, baseEnd_3870243] using wordTrace_append hprefix tailTrace_3870243
  have hstable : (prefixWord ++ tailWord_3870243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870243).length < 2 ^ (prefixWord ++ tailWord_3870243).sum := by decide
  have hdescent : baseEnd_3870243 < baseStart_3870243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870262 : List Nat := [5, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3870262 : Nat := 118140960795 + 3870262 * 2 ^ 59
def prefixEnd_3870262 : Nat := 4983230072969 + 3 ^ 40 * 3870262 * 2
def baseEnd_3870262 : Nat := 441623258851431514627999

theorem tailTrace_3870262 : CollatzResearch.WordTrace tailWord_3870262 prefixEnd_3870262 441623258851431514627999 := by
  unfold tailWord_3870262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8822503244044327310672315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94106701269806157980504693 8822503244044327310672315)
  ·
    refine ⟨13233754866066490966008473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8822503244044327310672315 13233754866066490966008473)
    ·
      refine ⟨9925316149549868224506355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13233754866066490966008473 9925316149549868224506355)
      ·
        refine ⟨14887974224324802336759533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9925316149549868224506355 14887974224324802336759533)
        ·
          refine ⟨5582990334121800876284825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14887974224324802336759533 5582990334121800876284825)
          ·
            refine ⟨4187242750591350657213619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5582990334121800876284825 4187242750591350657213619)
            ·
              refine ⟨6280864125887025985820429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187242750591350657213619 6280864125887025985820429)
              ·
                refine ⟨2355324047207634744682661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6280864125887025985820429 2355324047207634744682661)
                ·
                  refine ⟨441623258851431514627999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2355324047207634744682661 441623258851431514627999)
                  ·
                    rfl

theorem cell22_3870262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3870262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870262 prefixEnd_3870262 := by exact prefixLift 3870262
  have htrace : WordTrace (prefixWord ++ tailWord_3870262) baseStart_3870262 baseEnd_3870262 := by
    simpa [prefixWord, tailWord_3870262, baseEnd_3870262] using wordTrace_append hprefix tailTrace_3870262
  have hstable : (prefixWord ++ tailWord_3870262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870262).length < 2 ^ (prefixWord ++ tailWord_3870262).sum := by decide
  have hdescent : baseEnd_3870262 < baseStart_3870262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870294 : List Nat := [5, 2, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3870294 : Nat := 118140960795 + 3870294 * 2 ^ 59
def prefixEnd_3870294 : Nat := 4983230072969 + 3 ^ 40 * 3870294 * 2
def baseEnd_3870294 : Nat := 1324880730808257127083899

theorem tailTrace_3870294 : CollatzResearch.WordTrace tailWord_3870294 prefixEnd_3870294 1324880730808257127083899 := by
  unfold tailWord_3870294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8822576190037081652245121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94107479360395537623947957 8822576190037081652245121)
  ·
    refine ⟨6616932142527811239183841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8822576190037081652245121 6616932142527811239183841)
    ·
      refine ⟨4962699106895858429387881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6616932142527811239183841 4962699106895858429387881)
      ·
        refine ⟨3722024330171893822040911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4962699106895858429387881 3722024330171893822040911)
        ·
          refine ⟨5583036495257840733061367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722024330171893822040911 5583036495257840733061367)
          ·
            refine ⟨8374554742886761099592051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583036495257840733061367 8374554742886761099592051)
            ·
              refine ⟨12561832114330141649388077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374554742886761099592051 12561832114330141649388077)
              ·
                refine ⟨4710687042873803118520529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12561832114330141649388077 4710687042873803118520529)
                ·
                  refine ⟨3533015282155352338890397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710687042873803118520529 3533015282155352338890397)
                  ·
                    refine ⟨1324880730808257127083899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533015282155352338890397 1324880730808257127083899)
                    ·
                      rfl

theorem cell22_3870294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3870294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870294 prefixEnd_3870294 := by exact prefixLift 3870294
  have htrace : WordTrace (prefixWord ++ tailWord_3870294) baseStart_3870294 baseEnd_3870294 := by
    simpa [prefixWord, tailWord_3870294, baseEnd_3870294] using wordTrace_append hprefix tailTrace_3870294
  have hstable : (prefixWord ++ tailWord_3870294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870294).length < 2 ^ (prefixWord ++ tailWord_3870294).sum := by decide
  have hdescent : baseEnd_3870294 < baseStart_3870294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870382 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3870382 : Nat := 118140960795 + 3870382 * 2 ^ 59
def prefixEnd_3870382 : Nat := 4983230072969 + 3 ^ 40 * 3870382 * 2
def baseEnd_3870382 : Nat := 1324910855006654230883629

theorem tailTrace_3870382 : CollatzResearch.WordTrace tailWord_3870382 prefixEnd_3870382 1324910855006654230883629 := by
  unfold tailWord_3870382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17645553583034312183140675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94109619109516331643416933 17645553583034312183140675)
  ·
    refine ⟨26468330374551468274711013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17645553583034312183140675 26468330374551468274711013)
    ·
      refine ⟨4962811945228400301508315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26468330374551468274711013 4962811945228400301508315)
      ·
        refine ⟨7444217917842600452262473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962811945228400301508315 7444217917842600452262473)
        ·
          refine ⟨5583163438381950339196855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7444217917842600452262473 5583163438381950339196855)
          ·
            refine ⟨8374745157572925508795283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583163438381950339196855 8374745157572925508795283)
            ·
              refine ⟨12562117736359388263192925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374745157572925508795283 12562117736359388263192925)
              ·
                refine ⟨4710794151134770598697347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12562117736359388263192925 4710794151134770598697347)
                ·
                  refine ⟨7066191226702155898046021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710794151134770598697347 7066191226702155898046021)
                  ·
                    refine ⟨1324910855006654230883629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066191226702155898046021 1324910855006654230883629)
                    ·
                      rfl

theorem cell22_3870382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3870382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870382 prefixEnd_3870382 := by exact prefixLift 3870382
  have htrace : WordTrace (prefixWord ++ tailWord_3870382) baseStart_3870382 baseEnd_3870382 := by
    simpa [prefixWord, tailWord_3870382, baseEnd_3870382] using wordTrace_append hprefix tailTrace_3870382
  have hstable : (prefixWord ++ tailWord_3870382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870382).length < 2 ^ (prefixWord ++ tailWord_3870382).sum := by decide
  have hdescent : baseEnd_3870382 < baseStart_3870382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870391 : List Nat := [1, 1, 3, 1, 5, 2, 9]
def baseStart_3870391 : Nat := 118140960795 + 3870391 * 2 ^ 59
def prefixEnd_3870391 : Nat := 4983230072969 + 3 ^ 40 * 3870391 * 2
def baseEnd_3870391 : Nat := 49070886514465970644763

theorem tailTrace_3870391 : CollatzResearch.WordTrace tailWord_3870391 prefixEnd_3870391 49070886514465970644763 := by
  unfold tailWord_3870391
  simp only [CollatzResearch.WordTrace]
  refine ⟨141164756921241892002203027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94109837947494594668135351 141164756921241892002203027)
  ·
    refine ⟨211747135381862838003304541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141164756921241892002203027 211747135381862838003304541)
    ·
      refine ⟨79405175768198564251239203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211747135381862838003304541 79405175768198564251239203)
      ·
        refine ⟨119107763652297846376858805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79405175768198564251239203 119107763652297846376858805)
        ·
          refine ⟨11166352842402923097830513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119107763652297846376858805 11166352842402923097830513)
          ·
            refine ⟨8374764631802192323372885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11166352842402923097830513 8374764631802192323372885)
            ·
              refine ⟨49070886514465970644763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8374764631802192323372885 49070886514465970644763)
              ·
                rfl

theorem cell22_3870391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 9].length) (baseStart_3870391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870391 prefixEnd_3870391 := by exact prefixLift 3870391
  have htrace : WordTrace (prefixWord ++ tailWord_3870391) baseStart_3870391 baseEnd_3870391 := by
    simpa [prefixWord, tailWord_3870391, baseEnd_3870391] using wordTrace_append hprefix tailTrace_3870391
  have hstable : (prefixWord ++ tailWord_3870391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870391).length < 2 ^ (prefixWord ++ tailWord_3870391).sum := by decide
  have hdescent : baseEnd_3870391 < baseStart_3870391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870412 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 1, 5]
def baseStart_3870412 : Nat := 118140960795 + 3870412 * 2 ^ 59
def prefixEnd_3870412 : Nat := 4983230072969 + 3 ^ 40 * 3870412 * 2
def baseEnd_3870412 : Nat := 1324921124619744152633537

theorem tailTrace_3870412 : CollatzResearch.WordTrace tailWord_3870412 prefixEnd_3870412 1324921124619744152633537 := by
  unfold tailWord_3870412
  simp only [CollatzResearch.WordTrace]
  refine ⟨70582761427082906294358745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94110348569443875059144993 70582761427082906294358745)
  ·
    refine ⟨52937071070312179720769059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70582761427082906294358745 52937071070312179720769059)
    ·
      refine ⟨79405606605468269581153589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52937071070312179720769059 79405606605468269581153589)
      ·
        refine ⟨7444275619262650273233149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79405606605468269581153589 7444275619262650273233149)
        ·
          refine ⟨2791603357223493852462431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7444275619262650273233149 2791603357223493852462431)
          ·
            refine ⟨4187405035835240778693647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791603357223493852462431 4187405035835240778693647)
            ·
              refine ⟨6281107553752861168040471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187405035835240778693647 6281107553752861168040471)
              ·
                refine ⟨9421661330629291752060707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281107553752861168040471 9421661330629291752060707)
                ·
                  refine ⟨14132491995943937628091061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421661330629291752060707 14132491995943937628091061)
                  ·
                    refine ⟨1324921124619744152633537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14132491995943937628091061 1324921124619744152633537)
                    ·
                      rfl

theorem cell22_3870412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_3870412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870412 prefixEnd_3870412 := by exact prefixLift 3870412
  have htrace : WordTrace (prefixWord ++ tailWord_3870412) baseStart_3870412 baseEnd_3870412 := by
    simpa [prefixWord, tailWord_3870412, baseEnd_3870412] using wordTrace_append hprefix tailTrace_3870412
  have hstable : (prefixWord ++ tailWord_3870412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870412).length < 2 ^ (prefixWord ++ tailWord_3870412).sum := by decide
  have hdescent : baseEnd_3870412 < baseStart_3870412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870423 : List Nat := [1, 1, 3, 2, 1, 3, 1, 4, 3, 3]
def baseStart_3870423 : Nat := 118140960795 + 3870423 * 2 ^ 59
def prefixEnd_3870423 : Nat := 4983230072969 + 3 ^ 40 * 3870423 * 2
def baseEnd_3870423 : Nat := 1324924890144543790608503

theorem tailTrace_3870423 : CollatzResearch.WordTrace tailWord_3870423 prefixEnd_3870423 1324924890144543790608503 := by
  unfold tailWord_3870423
  simp only [CollatzResearch.WordTrace]
  refine ⟨141165924057125961467367923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94110616038083974311578615 141165924057125961467367923)
  ·
    refine ⟨211748886085688942201051885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141165924057125961467367923 211748886085688942201051885)
    ·
      refine ⟨79405832282133353325394457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211748886085688942201051885 79405832282133353325394457)
      ·
        refine ⟨59554374211600014994045843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79405832282133353325394457 59554374211600014994045843)
        ·
          refine ⟨89331561317400022491068765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59554374211600014994045843 89331561317400022491068765)
          ·
            refine ⟨33499335494025008434150787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89331561317400022491068765 33499335494025008434150787)
            ·
              refine ⟨50249003241037512651226181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33499335494025008434150787 50249003241037512651226181)
              ·
                refine ⟨9421688107694533622104909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50249003241037512651226181 9421688107694533622104909)
                ·
                  refine ⟨3533133040385450108289341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9421688107694533622104909 3533133040385450108289341)
                  ·
                    refine ⟨1324924890144543790608503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533133040385450108289341 1324924890144543790608503)
                    ·
                      rfl

theorem cell22_3870423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_3870423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870423 prefixEnd_3870423 := by exact prefixLift 3870423
  have htrace : WordTrace (prefixWord ++ tailWord_3870423) baseStart_3870423 baseEnd_3870423 := by
    simpa [prefixWord, tailWord_3870423, baseEnd_3870423] using wordTrace_append hprefix tailTrace_3870423
  have hstable : (prefixWord ++ tailWord_3870423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870423).length < 2 ^ (prefixWord ++ tailWord_3870423).sum := by decide
  have hdescent : baseEnd_3870423 < baseStart_3870423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870436 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 9]
def baseStart_3870436 : Nat := 118140960795 + 3870436 * 2 ^ 59
def prefixEnd_3870436 : Nat := 4983230072969 + 3 ^ 40 * 3870436 * 2
def baseEnd_3870436 : Nat := 441643113436738696677821

theorem tailTrace_3870436 : CollatzResearch.WordTrace tailWord_3870436 prefixEnd_3870436 441643113436738696677821 := by
  unfold tailWord_3870436
  simp only [CollatzResearch.WordTrace]
  refine ⟨70583199103039432343795581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94110932137385909791727441 70583199103039432343795581)
  ·
    refine ⟨26468699663639787128923343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70583199103039432343795581 26468699663639787128923343)
    ·
      refine ⟨39703049495459680693385015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26468699663639787128923343 39703049495459680693385015)
      ·
        refine ⟨59554574243189521040077523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39703049495459680693385015 59554574243189521040077523)
        ·
          refine ⟨89331861364784281560116285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59554574243189521040077523 89331861364784281560116285)
          ·
            refine ⟨33499448011794105585043607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89331861364784281560116285 33499448011794105585043607)
            ·
              refine ⟨50249172017691158377565411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33499448011794105585043607 50249172017691158377565411)
              ·
                refine ⟨75373758026536737566348117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50249172017691158377565411 75373758026536737566348117)
                ·
                  refine ⟨441643113436738696677821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75373758026536737566348117 441643113436738696677821)
                  ·
                    rfl

theorem cell22_3870436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_3870436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870436 prefixEnd_3870436 := by exact prefixLift 3870436
  have htrace : WordTrace (prefixWord ++ tailWord_3870436) baseStart_3870436 baseEnd_3870436 := by
    simpa [prefixWord, tailWord_3870436, baseEnd_3870436] using wordTrace_append hprefix tailTrace_3870436
  have hstable : (prefixWord ++ tailWord_3870436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870436).length < 2 ^ (prefixWord ++ tailWord_3870436).sum := by decide
  have hdescent : baseEnd_3870436 < baseStart_3870436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870451 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 4, 5]
def baseStart_3870451 : Nat := 118140960795 + 3870451 * 2 ^ 59
def prefixEnd_3870451 : Nat := 4983230072969 + 3 ^ 40 * 3870451 * 2
def baseEnd_3870451 : Nat := 1324934475116761050908417

theorem tailTrace_3870451 : CollatzResearch.WordTrace tailWord_3870451 prefixEnd_3870451 1324934475116761050908417 := by
  unfold tailWord_3870451
  simp only [CollatzResearch.WordTrace]
  refine ⟨141166945301024522249387207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94111296867349681499591471 141166945301024522249387207)
  ·
    refine ⟨211750417951536783374080811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141166945301024522249387207 211750417951536783374080811)
    ·
      refine ⟨317625626927305175061121217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211750417951536783374080811 317625626927305175061121217)
      ·
        refine ⟨238219220195478881295840913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317625626927305175061121217 238219220195478881295840913)
        ·
          refine ⟨178664415146609160971880685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238219220195478881295840913 178664415146609160971880685)
          ·
            refine ⟨66999155679978435364455257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178664415146609160971880685 66999155679978435364455257)
            ·
              refine ⟨50249366759983826523341443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66999155679978435364455257 50249366759983826523341443)
              ·
                refine ⟨75374050139975739785012165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50249366759983826523341443 75374050139975739785012165)
                ·
                  refine ⟨14132634401245451209689781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75374050139975739785012165 14132634401245451209689781)
                  ·
                    refine ⟨1324934475116761050908417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14132634401245451209689781 1324934475116761050908417)
                    ·
                      rfl

theorem cell22_3870451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_3870451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870451 prefixEnd_3870451 := by exact prefixLift 3870451
  have htrace : WordTrace (prefixWord ++ tailWord_3870451) baseStart_3870451 baseEnd_3870451 := by
    simpa [prefixWord, tailWord_3870451, baseEnd_3870451] using wordTrace_append hprefix tailTrace_3870451
  have hstable : (prefixWord ++ tailWord_3870451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870451).length < 2 ^ (prefixWord ++ tailWord_3870451).sum := by decide
  have hdescent : baseEnd_3870451 < baseStart_3870451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870481 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 8]
def baseStart_3870481 : Nat := 118140960795 + 3870481 * 2 ^ 59
def prefixEnd_3870481 : Nat := 4983230072969 + 3 ^ 40 * 3870481 * 2
def baseEnd_3870481 : Nat := 441648248243283657552775

theorem tailTrace_3870481 : CollatzResearch.WordTrace tailWord_3870481 prefixEnd_3870481 441648248243283657552775 := by
  unfold tailWord_3870481
  simp only [CollatzResearch.WordTrace]
  refine ⟨141168039490915837372979297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94112026327277224915319531 141168039490915837372979297)
  ·
    refine ⟨105876029618186878029734473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141168039490915837372979297 105876029618186878029734473)
    ·
      refine ⟨79407022213640158522300855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105876029618186878029734473 79407022213640158522300855)
      ·
        refine ⟨119110533320460237783451283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79407022213640158522300855 119110533320460237783451283)
        ·
          refine ⟨178665799980690356675176925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119110533320460237783451283 178665799980690356675176925)
          ·
            refine ⟨66999674992758883753191347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178665799980690356675176925 66999674992758883753191347)
            ·
              refine ⟨100499512489138325629787021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66999674992758883753191347 100499512489138325629787021)
              ·
                refine ⟨37687317183426872111170133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100499512489138325629787021 37687317183426872111170133)
                ·
                  refine ⟨441648248243283657552775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37687317183426872111170133 441648248243283657552775)
                  ·
                    rfl

theorem cell22_3870481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_3870481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870481 prefixEnd_3870481 := by exact prefixLift 3870481
  have htrace : WordTrace (prefixWord ++ tailWord_3870481) baseStart_3870481 baseEnd_3870481 := by
    simpa [prefixWord, tailWord_3870481, baseEnd_3870481] using wordTrace_append hprefix tailTrace_3870481
  have hstable : (prefixWord ++ tailWord_3870481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870481).length < 2 ^ (prefixWord ++ tailWord_3870481).sum := by decide
  have hdescent : baseEnd_3870481 < baseStart_3870481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870483 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 1, 4]
def baseStart_3870483 : Nat := 118140960795 + 3870483 * 2 ^ 59
def prefixEnd_3870483 : Nat := 4983230072969 + 3 ^ 40 * 3870483 * 2
def baseEnd_3870483 : Nat := 1324945429370723634108319

theorem tailTrace_3870483 : CollatzResearch.WordTrace tailWord_3870483 prefixEnd_3870483 1324945429370723634108319 := by
  unfold tailWord_3870483
  simp only [CollatzResearch.WordTrace]
  refine ⟨141168112436908591714552103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94112074957939061143034735 141168112436908591714552103)
  ·
    refine ⟨211752168655362887571828155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141168112436908591714552103 211752168655362887571828155)
    ·
      refine ⟨317628252983044331357742233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211752168655362887571828155 317628252983044331357742233)
      ·
        refine ⟨238221189737283248518306675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317628252983044331357742233 238221189737283248518306675)
        ·
          refine ⟨357331784605924872777460013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238221189737283248518306675 357331784605924872777460013)
          ·
            refine ⟨133999419227221827291547505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357331784605924872777460013 133999419227221827291547505)
            ·
              refine ⟨100499564420416370468660629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133999419227221827291547505 100499564420416370468660629)
              ·
                refine ⟨4710917082207017365718467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100499564420416370468660629 4710917082207017365718467)
                ·
                  refine ⟨7066375623310526048577701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710917082207017365718467 7066375623310526048577701)
                  ·
                    refine ⟨1324945429370723634108319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066375623310526048577701 1324945429370723634108319)
                    ·
                      rfl

theorem cell22_3870483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 4].length) (baseStart_3870483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870483 prefixEnd_3870483 := by exact prefixLift 3870483
  have htrace : WordTrace (prefixWord ++ tailWord_3870483) baseStart_3870483 baseEnd_3870483 := by
    simpa [prefixWord, tailWord_3870483, baseEnd_3870483] using wordTrace_append hprefix tailTrace_3870483
  have hstable : (prefixWord ++ tailWord_3870483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870483).length < 2 ^ (prefixWord ++ tailWord_3870483).sum := by decide
  have hdescent : baseEnd_3870483 < baseStart_3870483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870545 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_3870545 : Nat := 118140960795 + 3870545 * 2 ^ 59
def prefixEnd_3870545 : Nat := 4983230072969 + 3 ^ 40 * 3870545 * 2
def baseEnd_3870545 : Nat := 1324966653237776139058129

theorem tailTrace_3870545 : CollatzResearch.WordTrace tailWord_3870545 prefixEnd_3870545 1324966653237776139058129 := by
  unfold tailWord_3870545
  simp only [CollatzResearch.WordTrace]
  refine ⟨141170373762683976303309089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94113582508455984202206059 141170373762683976303309089)
  ·
    refine ⟨105877780322012982227481817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141170373762683976303309089 105877780322012982227481817)
    ·
      refine ⟨79408335241509736670611363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105877780322012982227481817 79408335241509736670611363)
      ·
        refine ⟨119112502862264605005917045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79408335241509736670611363 119112502862264605005917045)
        ·
          refine ⟨11166797143337306719304723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119112502862264605005917045 11166797143337306719304723)
          ·
            refine ⟨16750195715005960078957085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11166797143337306719304723 16750195715005960078957085)
            ·
              refine ⟨6281323393127235029608907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16750195715005960078957085 6281323393127235029608907)
              ·
                refine ⟨9421985089690852544413361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281323393127235029608907 9421985089690852544413361)
                ·
                  refine ⟨7066488817268139408310021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9421985089690852544413361 7066488817268139408310021)
                  ·
                    refine ⟨1324966653237776139058129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066488817268139408310021 1324966653237776139058129)
                    ·
                      rfl

theorem cell22_3870545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_3870545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870545 prefixEnd_3870545 := by exact prefixLift 3870545
  have htrace : WordTrace (prefixWord ++ tailWord_3870545) baseStart_3870545 baseEnd_3870545 := by
    simpa [prefixWord, tailWord_3870545, baseEnd_3870545] using wordTrace_append hprefix tailTrace_3870545
  have hstable : (prefixWord ++ tailWord_3870545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870545).length < 2 ^ (prefixWord ++ tailWord_3870545).sum := by decide
  have hdescent : baseEnd_3870545 < baseStart_3870545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870564 : List Nat := [2, 3, 1, 1, 5, 2, 1, 2, 2, 3]
def baseStart_3870564 : Nat := 118140960795 + 3870564 * 2 ^ 59
def prefixEnd_3870564 : Nat := 4983230072969 + 3 ^ 40 * 3870564 * 2
def baseEnd_3870564 : Nat := 1324973157326066422833071

theorem tailTrace_3870564 : CollatzResearch.WordTrace tailWord_3870564 prefixEnd_3870564 1324973157326066422833071 := by
  unfold tailWord_3870564
  simp only [CollatzResearch.WordTrace]
  refine ⟨70585533374807571274125373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94114044499743428365500497 70585533374807571274125373)
  ·
    refine ⟨26469575015552839227797015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70585533374807571274125373 26469575015552839227797015)
    ·
      refine ⟨39704362523329258841695523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26469575015552839227797015 39704362523329258841695523)
      ·
        refine ⟨59556543784993888262543285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39704362523329258841695523 59556543784993888262543285)
        ·
          refine ⟨5583425979843177024613433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59556543784993888262543285 5583425979843177024613433)
          ·
            refine ⟨4187569484882382768460075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5583425979843177024613433 4187569484882382768460075)
            ·
              refine ⟨6281354227323574152690113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187569484882382768460075 6281354227323574152690113)
              ·
                refine ⟨4711015670492680614517585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6281354227323574152690113 4711015670492680614517585)
                ·
                  refine ⟨3533261752869510460888189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4711015670492680614517585 3533261752869510460888189)
                  ·
                    refine ⟨1324973157326066422833071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533261752869510460888189 1324973157326066422833071)
                    ·
                      rfl

theorem cell22_3870564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_3870564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870564 prefixEnd_3870564 := by exact prefixLift 3870564
  have htrace : WordTrace (prefixWord ++ tailWord_3870564) baseStart_3870564 baseEnd_3870564 := by
    simpa [prefixWord, tailWord_3870564, baseEnd_3870564] using wordTrace_append hprefix tailTrace_3870564
  have hstable : (prefixWord ++ tailWord_3870564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870564).length < 2 ^ (prefixWord ++ tailWord_3870564).sum := by decide
  have hdescent : baseEnd_3870564 < baseStart_3870564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870573 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3870573 : Nat := 118140960795 + 3870573 * 2 ^ 59
def prefixEnd_3870573 : Nat := 4983230072969 + 3 ^ 40 * 3870573 * 2
def baseEnd_3870573 : Nat := 1324976238209993399358043

theorem tailTrace_3870573 : CollatzResearch.WordTrace tailWord_3870573 prefixEnd_3870573 1324976238209993399358043 := by
  unfold tailWord_3870573
  simp only [CollatzResearch.WordTrace]
  refine ⟨141171395006582537085328373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94114263337721691390218915 141171395006582537085328373)
  ·
    refine ⟨13234818281867112851749535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141171395006582537085328373 13234818281867112851749535)
    ·
      refine ⟨19852227422800669277624303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13234818281867112851749535 19852227422800669277624303)
      ·
        refine ⟨29778341134201003916436455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19852227422800669277624303 29778341134201003916436455)
        ·
          refine ⟨44667511701301505874654683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29778341134201003916436455 44667511701301505874654683)
          ·
            refine ⟨67001267551952258811982025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44667511701301505874654683 67001267551952258811982025)
            ·
              refine ⟨50250950663964194108986519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67001267551952258811982025 50250950663964194108986519)
              ·
                refine ⟨75376425995946291163479779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50250950663964194108986519 75376425995946291163479779)
                ·
                  refine ⟨113064638993919436745219669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75376425995946291163479779 113064638993919436745219669)
                  ·
                    refine ⟨1324976238209993399358043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113064638993919436745219669 1324976238209993399358043)
                    ·
                      rfl

theorem cell22_3870573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3870573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870573 prefixEnd_3870573 := by exact prefixLift 3870573
  have htrace : WordTrace (prefixWord ++ tailWord_3870573) baseStart_3870573 baseEnd_3870573 := by
    simpa [prefixWord, tailWord_3870573, baseEnd_3870573] using wordTrace_append hprefix tailTrace_3870573
  have hstable : (prefixWord ++ tailWord_3870573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870573).length < 2 ^ (prefixWord ++ tailWord_3870573).sum := by decide
  have hdescent : baseEnd_3870573 < baseStart_3870573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870626 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3870626 : Nat := 118140960795 + 3870626 * 2 ^ 59
def prefixEnd_3870626 : Nat := 4983230072969 + 3 ^ 40 * 3870626 * 2
def baseEnd_3870626 : Nat := 1324994381193118927782881

theorem tailTrace_3870626 : CollatzResearch.WordTrace tailWord_3870626 prefixEnd_3870626 1324994381193118927782881 := by
  unfold tailWord_3870626
  simp only [CollatzResearch.WordTrace]
  refine ⟨35293332018847631784251933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94115552050260351424671821 35293332018847631784251933)
  ·
    refine ⟨13234999507067861919094475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35293332018847631784251933 13234999507067861919094475)
    ·
      refine ⟨19852499260601792878641713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13234999507067861919094475 19852499260601792878641713)
      ·
        refine ⟨14889374445451344658981285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19852499260601792878641713 14889374445451344658981285)
        ·
          refine ⟨2791757708522127123558991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14889374445451344658981285 2791757708522127123558991)
          ·
            refine ⟨4187636562783190685338487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791757708522127123558991 4187636562783190685338487)
            ·
              refine ⟨6281454844174786028007731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187636562783190685338487 6281454844174786028007731)
              ·
                refine ⟨9422182266262179042011597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281454844174786028007731 9422182266262179042011597)
                ·
                  refine ⟨3533318349848317140754349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9422182266262179042011597 3533318349848317140754349)
                  ·
                    refine ⟨1324994381193118927782881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533318349848317140754349 1324994381193118927782881)
                    ·
                      rfl

theorem cell22_3870626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3870626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870626 prefixEnd_3870626 := by exact prefixLift 3870626
  have htrace : WordTrace (prefixWord ++ tailWord_3870626) baseStart_3870626 baseEnd_3870626 := by
    simpa [prefixWord, tailWord_3870626, baseEnd_3870626] using wordTrace_append hprefix tailTrace_3870626
  have hstable : (prefixWord ++ tailWord_3870626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870626).length < 2 ^ (prefixWord ++ tailWord_3870626).sum := by decide
  have hdescent : baseEnd_3870626 < baseStart_3870626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870633 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 6]
def baseStart_3870633 : Nat := 118140960795 + 3870633 * 2 ^ 59
def prefixEnd_3870633 : Nat := 4983230072969 + 3 ^ 40 * 3870633 * 2
def baseEnd_3870633 : Nat := 441665592478724414285953

theorem tailTrace_3870633 : CollatzResearch.WordTrace tailWord_3870633 prefixEnd_3870633 441665592478724414285953 := by
  unfold tailWord_3870633
  simp only [CollatzResearch.WordTrace]
  refine ⟨141173583386365167332512553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94115722257576778221675035 141173583386365167332512553)
  ·
    refine ⟨105880187539773875499384415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141173583386365167332512553 105880187539773875499384415)
    ·
      refine ⟨158820281309660813249076623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105880187539773875499384415 158820281309660813249076623)
      ·
        refine ⟨238230421964491219873614935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158820281309660813249076623 238230421964491219873614935)
        ·
          refine ⟨357345632946736829810422403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238230421964491219873614935 357345632946736829810422403)
          ·
            refine ⟨536018449420105244715633605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357345632946736829810422403 536018449420105244715633605)
            ·
              refine ⟨100503459266269733384181301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 536018449420105244715633605 100503459266269733384181301)
              ·
                refine ⟨9422199306212787504766997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100503459266269733384181301 9422199306212787504766997)
                ·
                  refine ⟨441665592478724414285953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9422199306212787504766997 441665592478724414285953)
                  ·
                    rfl

theorem cell22_3870633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_3870633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870633 prefixEnd_3870633 := by exact prefixLift 3870633
  have htrace : WordTrace (prefixWord ++ tailWord_3870633) baseStart_3870633 baseEnd_3870633 := by
    simpa [prefixWord, tailWord_3870633, baseEnd_3870633] using wordTrace_append hprefix tailTrace_3870633
  have hstable : (prefixWord ++ tailWord_3870633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870633).length < 2 ^ (prefixWord ++ tailWord_3870633).sum := by decide
  have hdescent : baseEnd_3870633 < baseStart_3870633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870680 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_3870680 : Nat := 118140960795 + 3870680 * 2 ^ 59
def prefixEnd_3870680 : Nat := 4983230072969 + 3 ^ 40 * 3870680 * 2
def baseEnd_3870680 : Nat := 1325012866496680786932715

theorem tailTrace_3870680 : CollatzResearch.WordTrace tailWord_3870680 prefixEnd_3870680 1325012866496680786932715 := by
  unfold tailWord_3870680
  simp only [CollatzResearch.WordTrace]
  refine ⟨70587648808597447179736747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94116865078129929572982329 70587648808597447179736747)
  ·
    refine ⟨105881473212896170769605121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70587648808597447179736747 105881473212896170769605121)
    ·
      refine ⟨79411104909672128077203841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105881473212896170769605121 79411104909672128077203841)
      ·
        refine ⟨59558328682254096057902881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79411104909672128077203841 59558328682254096057902881)
        ·
          refine ⟨44668746511690572043427161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59558328682254096057902881 44668746511690572043427161)
          ·
            refine ⟨33501559883767929032570371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44668746511690572043427161 33501559883767929032570371)
            ·
              refine ⟨50252339825651893548855557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33501559883767929032570371 50252339825651893548855557)
              ·
                refine ⟨9422313717309730040410417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50252339825651893548855557 9422313717309730040410417)
                ·
                  refine ⟨7066735287982297530307813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9422313717309730040410417 7066735287982297530307813)
                  ·
                    refine ⟨1325012866496680786932715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066735287982297530307813 1325012866496680786932715)
                    ·
                      rfl

theorem cell22_3870680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_3870680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870680 prefixEnd_3870680 := by exact prefixLift 3870680
  have htrace : WordTrace (prefixWord ++ tailWord_3870680) baseStart_3870680 baseEnd_3870680 := by
    simpa [prefixWord, tailWord_3870680, baseEnd_3870680] using wordTrace_append hprefix tailTrace_3870680
  have hstable : (prefixWord ++ tailWord_3870680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870680).length < 2 ^ (prefixWord ++ tailWord_3870680).sum := by decide
  have hdescent : baseEnd_3870680 < baseStart_3870680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870733 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3870733 : Nat := 118140960795 + 3870733 * 2 ^ 59
def prefixEnd_3870733 : Nat := 4983230072969 + 3 ^ 40 * 3870733 * 2
def baseEnd_3870733 : Nat := 1325031009479806315357553

theorem tailTrace_3870733 : CollatzResearch.WordTrace tailWord_3870733 prefixEnd_3870733 1325031009479806315357553 := by
  unfold tailWord_3870733
  simp only [CollatzResearch.WordTrace]
  refine ⟨141177230686002884411152853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94118153790668589607435235 141177230686002884411152853)
  ·
    refine ⟨3308841344203192603386395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 141177230686002884411152853 3308841344203192603386395)
    ·
      refine ⟨4963262016304788905079593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3308841344203192603386395 4963262016304788905079593)
      ·
        refine ⟨3722446512228591678809695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4963262016304788905079593 3722446512228591678809695)
        ·
          refine ⟨5583669768342887518214543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722446512228591678809695 5583669768342887518214543)
          ·
            refine ⟨8375504652514331277321815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583669768342887518214543 8375504652514331277321815)
            ·
              refine ⟨12563256978771496915982723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375504652514331277321815 12563256978771496915982723)
              ·
                refine ⟨18844885468157245373974085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12563256978771496915982723 18844885468157245373974085)
                ·
                  refine ⟨3533416025279483507620141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18844885468157245373974085 3533416025279483507620141)
                  ·
                    refine ⟨1325031009479806315357553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533416025279483507620141 1325031009479806315357553)
                    ·
                      rfl

theorem cell22_3870733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3870733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870733 prefixEnd_3870733 := by exact prefixLift 3870733
  have htrace : WordTrace (prefixWord ++ tailWord_3870733) baseStart_3870733 baseEnd_3870733 := by
    simpa [prefixWord, tailWord_3870733, baseEnd_3870733] using wordTrace_append hprefix tailTrace_3870733
  have hstable : (prefixWord ++ tailWord_3870733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870733).length < 2 ^ (prefixWord ++ tailWord_3870733).sum := by decide
  have hdescent : baseEnd_3870733 < baseStart_3870733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870744 : List Nat := [2, 1, 2, 3, 2, 1, 1, 6, 1, 3]
def baseStart_3870744 : Nat := 118140960795 + 3870744 * 2 ^ 59
def prefixEnd_3870744 : Nat := 4983230072969 + 3 ^ 40 * 3870744 * 2
def baseEnd_3870744 : Nat := 1325034775004605953332519

theorem tailTrace_3870744 : CollatzResearch.WordTrace tailWord_3870744 prefixEnd_3870744 1325034775004605953332519 := by
  unfold tailWord_3870744
  simp only [CollatzResearch.WordTrace]
  refine ⟨70588815944481516644901643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94118421259308688859868857 70588815944481516644901643)
  ·
    refine ⟨105883223916722274967352465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70588815944481516644901643 105883223916722274967352465)
    ·
      refine ⟨79412417937541706225514349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105883223916722274967352465 79412417937541706225514349)
      ·
        refine ⟨29779656726578139834567881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79412417937541706225514349 29779656726578139834567881)
        ·
          refine ⟨22334742544933604875925911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29779656726578139834567881 22334742544933604875925911)
          ·
            refine ⟨33502113817400407313888867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22334742544933604875925911 33502113817400407313888867)
            ·
              refine ⟨50253170726100610970833301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33502113817400407313888867 50253170726100610970833301)
              ·
                refine ⟨2355617377785966139257811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50253170726100610970833301 2355617377785966139257811)
                ·
                  refine ⟨3533426066678949208886717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355617377785966139257811 3533426066678949208886717)
                  ·
                    refine ⟨1325034775004605953332519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533426066678949208886717 1325034775004605953332519)
                    ·
                      rfl

theorem cell22_3870744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_3870744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870744 prefixEnd_3870744 := by exact prefixLift 3870744
  have htrace : WordTrace (prefixWord ++ tailWord_3870744) baseStart_3870744 baseEnd_3870744 := by
    simpa [prefixWord, tailWord_3870744, baseEnd_3870744] using wordTrace_append hprefix tailTrace_3870744
  have hstable : (prefixWord ++ tailWord_3870744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870744).length < 2 ^ (prefixWord ++ tailWord_3870744).sum := by decide
  have hdescent : baseEnd_3870744 < baseStart_3870744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870755 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 2, 5]
def baseStart_3870755 : Nat := 118140960795 + 3870755 * 2 ^ 59
def prefixEnd_3870755 : Nat := 4983230072969 + 3 ^ 40 * 3870755 * 2
def baseEnd_3870755 : Nat := 1325038540529405591307485

theorem tailTrace_3870755 : CollatzResearch.WordTrace tailWord_3870755 prefixEnd_3870755 1325038540529405591307485 := by
  unfold tailWord_3870755
  simp only [CollatzResearch.WordTrace]
  refine ⟨141178033091923182168453719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94118688727948788112302479 141178033091923182168453719)
  ·
    refine ⟨211767049637884773252680579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141178033091923182168453719 211767049637884773252680579)
    ·
      refine ⟨317650574456827159879020869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211767049637884773252680579 317650574456827159879020869)
      ·
        refine ⟨59559482710655092477316413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317650574456827159879020869 59559482710655092477316413)
        ·
          refine ⟨22334806016495659678993655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59559482710655092477316413 22334806016495659678993655)
          ·
            refine ⟨33502209024743489518490483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22334806016495659678993655 33502209024743489518490483)
            ·
              refine ⟨50253313537115234277735725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33502209024743489518490483 50253313537115234277735725)
              ·
                refine ⟨18844992576418212854150897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50253313537115234277735725 18844992576418212854150897)
                ·
                  refine ⟨14133744432313659640613173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18844992576418212854150897 14133744432313659640613173)
                  ·
                    refine ⟨1325038540529405591307485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14133744432313659640613173 1325038540529405591307485)
                    ·
                      rfl

theorem cell22_3870755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_3870755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870755 prefixEnd_3870755 := by exact prefixLift 3870755
  have htrace : WordTrace (prefixWord ++ tailWord_3870755) baseStart_3870755 baseEnd_3870755 := by
    simpa [prefixWord, tailWord_3870755, baseEnd_3870755] using wordTrace_append hprefix tailTrace_3870755
  have hstable : (prefixWord ++ tailWord_3870755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870755).length < 2 ^ (prefixWord ++ tailWord_3870755).sum := by decide
  have hdescent : baseEnd_3870755 < baseStart_3870755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870815 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 1, 6]
def baseStart_3870815 : Nat := 118140960795 + 3870815 * 2 ^ 59
def prefixEnd_3870815 : Nat := 4983230072969 + 3 ^ 40 * 3870815 * 2
def baseEnd_3870815 : Nat := 1325059079755585434807301

theorem tailTrace_3870815 : CollatzResearch.WordTrace tailWord_3870815 prefixEnd_3870815 1325059079755585434807301 := by
  unfold tailWord_3870815
  simp only [CollatzResearch.WordTrace]
  refine ⟨141180221471705812415637899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94120147647803874943758599 141180221471705812415637899)
  ·
    refine ⟨211770332207558718623456849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141180221471705812415637899 211770332207558718623456849)
    ·
      refine ⟨158827749155669038967592637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211770332207558718623456849 158827749155669038967592637)
      ·
        refine ⟨59560405933375889612847239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158827749155669038967592637 59560405933375889612847239)
        ·
          refine ⟨89340608900063834419270859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59560405933375889612847239 89340608900063834419270859)
          ·
            refine ⟨134010913350095751628906289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89340608900063834419270859 134010913350095751628906289)
            ·
              refine ⟨100508185012571813721679717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134010913350095751628906289 100508185012571813721679717)
              ·
                refine ⟨18845284689857215072814947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100508185012571813721679717 18845284689857215072814947)
                ·
                  refine ⟨28267927034785822609222421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18845284689857215072814947 28267927034785822609222421)
                  ·
                    refine ⟨1325059079755585434807301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28267927034785822609222421 1325059079755585434807301)
                    ·
                      rfl

theorem cell22_3870815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_3870815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870815 prefixEnd_3870815 := by exact prefixLift 3870815
  have htrace : WordTrace (prefixWord ++ tailWord_3870815) baseStart_3870815 baseEnd_3870815 := by
    simpa [prefixWord, tailWord_3870815, baseEnd_3870815] using wordTrace_append hprefix tailTrace_3870815
  have hstable : (prefixWord ++ tailWord_3870815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870815).length < 2 ^ (prefixWord ++ tailWord_3870815).sum := by decide
  have hdescent : baseEnd_3870815 < baseStart_3870815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870832 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_3870832 : Nat := 118140960795 + 3870832 * 2 ^ 59
def prefixEnd_3870832 : Nat := 4983230072969 + 3 ^ 40 * 3870832 * 2
def baseEnd_3870832 : Nat := 1325064899203003057132249

theorem tailTrace_3870832 : CollatzResearch.WordTrace tailWord_3870832 prefixEnd_3870832 1325064899203003057132249 := by
  unfold tailWord_3870832
  simp only [CollatzResearch.WordTrace]
  refine ⟨70590420756322112159503375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94120561008429482879337833 70590420756322112159503375)
  ·
    refine ⟨105885631134483168239255063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70590420756322112159503375 105885631134483168239255063)
    ·
      refine ⟨158828446701724752358882595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105885631134483168239255063 158828446701724752358882595)
      ·
        refine ⟨238242670052587128538323893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158828446701724752358882595 238242670052587128538323893)
        ·
          refine ⟨22335250317430043300467865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238242670052587128538323893 22335250317430043300467865)
          ·
            refine ⟨16751437738072532475350899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22335250317430043300467865 16751437738072532475350899)
            ·
              refine ⟨25127156607108798713026349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16751437738072532475350899 25127156607108798713026349)
              ·
                refine ⟨9422683727665799517384881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25127156607108798713026349 9422683727665799517384881)
                ·
                  refine ⟨7067012795749349638038661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9422683727665799517384881 7067012795749349638038661)
                  ·
                    refine ⟨1325064899203003057132249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7067012795749349638038661 1325064899203003057132249)
                    ·
                      rfl

theorem cell22_3870832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_3870832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870832 prefixEnd_3870832 := by exact prefixLift 3870832
  have htrace : WordTrace (prefixWord ++ tailWord_3870832) baseStart_3870832 baseEnd_3870832 := by
    simpa [prefixWord, tailWord_3870832, baseEnd_3870832] using wordTrace_append hprefix tailTrace_3870832
  have hstable : (prefixWord ++ tailWord_3870832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870832).length < 2 ^ (prefixWord ++ tailWord_3870832).sum := by decide
  have hdescent : baseEnd_3870832 < baseStart_3870832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870870 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3870870 : Nat := 118140960795 + 3870870 * 2 ^ 59
def prefixEnd_3870870 : Nat := 4983230072969 + 3 ^ 40 * 3870870 * 2
def baseEnd_3870870 : Nat := 441692635793194541560711

theorem tailTrace_3870870 : CollatzResearch.WordTrace tailWord_3870870 prefixEnd_3870870 441692635793194541560711 := by
  unfold tailWord_3870870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823889217906659800555629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94121484991004371205926709 8823889217906659800555629)
  ·
    refine ⟨3308958456714997425208361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8823889217906659800555629 3308958456714997425208361)
    ·
      refine ⟨2481718842536248068906271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3308958456714997425208361 2481718842536248068906271)
      ·
        refine ⟨3722578263804372103359407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481718842536248068906271 3722578263804372103359407)
        ·
          refine ⟨5583867395706558155039111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722578263804372103359407 5583867395706558155039111)
          ·
            refine ⟨8375801093559837232558667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583867395706558155039111 8375801093559837232558667)
            ·
              refine ⟨12563701640339755848838001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375801093559837232558667 12563701640339755848838001)
              ·
                refine ⟨9422776230254816886628501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12563701640339755848838001 9422776230254816886628501)
                ·
                  refine ⟨441692635793194541560711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9422776230254816886628501 441692635793194541560711)
                  ·
                    rfl

theorem cell22_3870870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3870870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870870 prefixEnd_3870870 := by exact prefixLift 3870870
  have htrace : WordTrace (prefixWord ++ tailWord_3870870) baseStart_3870870 baseEnd_3870870 := by
    simpa [prefixWord, tailWord_3870870, baseEnd_3870870] using wordTrace_append hprefix tailTrace_3870870
  have hstable : (prefixWord ++ tailWord_3870870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870870).length < 2 ^ (prefixWord ++ tailWord_3870870).sum := by decide
  have hdescent : baseEnd_3870870 < baseStart_3870870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870879 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 5, 3]
def baseStart_3870879 : Nat := 118140960795 + 3870879 * 2 ^ 59
def prefixEnd_3870879 : Nat := 4983230072969 + 3 ^ 40 * 3870879 * 2
def baseEnd_3870879 : Nat := 1325080988263510601207105

theorem tailTrace_3870879 : CollatzResearch.WordTrace tailWord_3870879 prefixEnd_3870879 1325080988263510601207105 := by
  unfold tailWord_3870879
  simp only [CollatzResearch.WordTrace]
  refine ⟨141182555743473951345967691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94121703828982634230645127 141182555743473951345967691)
  ·
    refine ⟨211773833615210927018951537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141182555743473951345967691 211773833615210927018951537)
    ·
      refine ⟨158830375211408195264213653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211773833615210927018951537 158830375211408195264213653)
      ·
        refine ⟨7445173838034759153010015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158830375211408195264213653 7445173838034759153010015)
        ·
          refine ⟨11167760757052138729515023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445173838034759153010015 11167760757052138729515023)
          ·
            refine ⟨16751641135578208094272535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11167760757052138729515023 16751641135578208094272535)
            ·
              refine ⟨25127461703367312141408803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16751641135578208094272535 25127461703367312141408803)
              ·
                refine ⟨37691192555050968212113205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25127461703367312141408803 37691192555050968212113205)
                ·
                  refine ⟨3533549302036028269885613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37691192555050968212113205 3533549302036028269885613)
                  ·
                    refine ⟨1325080988263510601207105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533549302036028269885613 1325080988263510601207105)
                    ·
                      rfl

theorem cell22_3870879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_3870879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870879 prefixEnd_3870879 := by exact prefixLift 3870879
  have htrace : WordTrace (prefixWord ++ tailWord_3870879) baseStart_3870879 baseEnd_3870879 := by
    simpa [prefixWord, tailWord_3870879, baseEnd_3870879] using wordTrace_append hprefix tailTrace_3870879
  have hstable : (prefixWord ++ tailWord_3870879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870879).length < 2 ^ (prefixWord ++ tailWord_3870879).sum := by decide
  have hdescent : baseEnd_3870879 < baseStart_3870879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870913 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3870913 : Nat := 118140960795 + 3870913 * 2 ^ 59
def prefixEnd_3870913 : Nat := 4983230072969 + 3 ^ 40 * 3870913 * 2
def baseEnd_3870913 : Nat := 1325092627158345845857001

theorem tailTrace_3870913 : CollatzResearch.WordTrace tailWord_3870913 prefixEnd_3870913 1325092627158345845857001 := by
  unfold tailWord_3870913
  simp only [CollatzResearch.WordTrace]
  refine ⟨141183795825350775152705393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94122530550233850101803595 141183795825350775152705393)
  ·
    refine ⟨105887846869013081364529045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141183795825350775152705393 105887846869013081364529045)
    ·
      refine ⟨4963492821984988188962299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105887846869013081364529045 4963492821984988188962299)
      ·
        refine ⟨7445239232977482283443449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4963492821984988188962299 7445239232977482283443449)
        ·
          refine ⟨5583929424733111712582587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7445239232977482283443449 5583929424733111712582587)
          ·
            refine ⟨8375894137099667568873881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583929424733111712582587 8375894137099667568873881)
            ·
              refine ⟨6281920602824750676655411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8375894137099667568873881 6281920602824750676655411)
              ·
                refine ⟨9422880904237126014983117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281920602824750676655411 9422880904237126014983117)
                ·
                  refine ⟨3533580339088922255618669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9422880904237126014983117 3533580339088922255618669)
                  ·
                    refine ⟨1325092627158345845857001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533580339088922255618669 1325092627158345845857001)
                    ·
                      rfl

theorem cell22_3870913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3870913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870913 prefixEnd_3870913 := by exact prefixLift 3870913
  have htrace : WordTrace (prefixWord ++ tailWord_3870913) baseStart_3870913 baseEnd_3870913 := by
    simpa [prefixWord, tailWord_3870913, baseEnd_3870913] using wordTrace_append hprefix tailTrace_3870913
  have hstable : (prefixWord ++ tailWord_3870913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870913).length < 2 ^ (prefixWord ++ tailWord_3870913).sum := by decide
  have hdescent : baseEnd_3870913 < baseStart_3870913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870926 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_3870926 : Nat := 118140960795 + 3870926 * 2 ^ 59
def prefixEnd_3870926 : Nat := 4983230072969 + 3 ^ 40 * 3870926 * 2
def baseEnd_3870926 : Nat := 441699025774672715093987

theorem tailTrace_3870926 : CollatzResearch.WordTrace tailWord_3870926 prefixEnd_3870926 441699025774672715093987 := by
  unfold tailWord_3870926
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648033746787959796616079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94122846649535785581952421 17648033746787959796616079)
  ·
    refine ⟨26472050620181939694924119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17648033746787959796616079 26472050620181939694924119)
    ·
      refine ⟨39708075930272909542386179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26472050620181939694924119 39708075930272909542386179)
      ·
        refine ⟨59562113895409364313579269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39708075930272909542386179 59562113895409364313579269)
        ·
          refine ⟨11167896355389255808796113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59562113895409364313579269 11167896355389255808796113)
          ·
            refine ⟨8375922266541941856597085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11167896355389255808796113 8375922266541941856597085)
            ·
              refine ⟨3140970849953228196223907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8375922266541941856597085 3140970849953228196223907)
              ·
                refine ⟨4711456274929842294335861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3140970849953228196223907 4711456274929842294335861)
                ·
                  refine ⟨441699025774672715093987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4711456274929842294335861 441699025774672715093987)
                  ·
                    rfl

theorem cell22_3870926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_3870926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870926 prefixEnd_3870926 := by exact prefixLift 3870926
  have htrace : WordTrace (prefixWord ++ tailWord_3870926) baseStart_3870926 baseEnd_3870926 := by
    simpa [prefixWord, tailWord_3870926, baseEnd_3870926] using wordTrace_append hprefix tailTrace_3870926
  have hstable : (prefixWord ++ tailWord_3870926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870926).length < 2 ^ (prefixWord ++ tailWord_3870926).sum := by decide
  have hdescent : baseEnd_3870926 < baseStart_3870926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870937 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 6]
def baseStart_3870937 : Nat := 118140960795 + 3870937 * 2 ^ 59
def prefixEnd_3870937 : Nat := 4983230072969 + 3 ^ 40 * 3870937 * 2
def baseEnd_3870937 : Nat := 441700280949605927752309

theorem tailTrace_3870937 : CollatzResearch.WordTrace tailWord_3870937 prefixEnd_3870937 441700280949605927752309 := by
  unfold tailWord_3870937
  simp only [CollatzResearch.WordTrace]
  refine ⟨141184671177263827251579065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94123114118175884834386043 141184671177263827251579065)
  ·
    refine ⟨105888503382947870438684299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141184671177263827251579065 105888503382947870438684299)
    ·
      refine ⟨158832755074421805658026449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105888503382947870438684299 158832755074421805658026449)
      ·
        refine ⟨119124566305816354243519837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158832755074421805658026449 119124566305816354243519837)
        ·
          refine ⟨44671712364681132841319939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119124566305816354243519837 44671712364681132841319939)
          ·
            refine ⟨67007568547021699261979909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44671712364681132841319939 67007568547021699261979909)
            ·
              refine ⟨12563919102566568611621233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67007568547021699261979909 12563919102566568611621233)
              ·
                refine ⟨9422939326924926458715925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12563919102566568611621233 9422939326924926458715925)
                ·
                  refine ⟨441700280949605927752309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9422939326924926458715925 441700280949605927752309)
                  ·
                    rfl

theorem cell22_3870937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_3870937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870937 prefixEnd_3870937 := by exact prefixLift 3870937
  have htrace : WordTrace (prefixWord ++ tailWord_3870937) baseStart_3870937 baseEnd_3870937 := by
    simpa [prefixWord, tailWord_3870937, baseEnd_3870937] using wordTrace_append hprefix tailTrace_3870937
  have hstable : (prefixWord ++ tailWord_3870937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870937).length < 2 ^ (prefixWord ++ tailWord_3870937).sum := by decide
  have hdescent : baseEnd_3870937 < baseStart_3870937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870947 : List Nat := [1, 1, 1, 8, 2, 1, 1, 3, 1, 3]
def baseStart_3870947 : Nat := 118140960795 + 3870947 * 2 ^ 59
def prefixEnd_3870947 : Nat := 4983230072969 + 3 ^ 40 * 3870947 * 2
def baseEnd_3870947 : Nat := 1325104266053181090506897

theorem tailTrace_3870947 : CollatzResearch.WordTrace tailWord_3870947 prefixEnd_3870947 1325104266053181090506897 := by
  unfold tailWord_3870947
  simp only [CollatzResearch.WordTrace]
  refine ⟨141185035907227598959443095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94123357271485065972962063 141185035907227598959443095)
  ·
    refine ⟨211777553860841398439164643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141185035907227598959443095 211777553860841398439164643)
    ·
      refine ⟨317666330791262097658746965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211777553860841398439164643 317666330791262097658746965)
      ·
        refine ⟨3722652313960102706938441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 317666330791262097658746965 3722652313960102706938441)
        ·
          refine ⟨2791989235470077030203831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3722652313960102706938441 2791989235470077030203831)
          ·
            refine ⟨4187983853205115545305747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791989235470077030203831 4187983853205115545305747)
            ·
              refine ⟨6281975779807673317958621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187983853205115545305747 6281975779807673317958621)
              ·
                refine ⟨2355740917427877494234483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6281975779807673317958621 2355740917427877494234483)
                ·
                  refine ⟨3533611376141816241351725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355740917427877494234483 3533611376141816241351725)
                  ·
                    refine ⟨1325104266053181090506897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533611376141816241351725 1325104266053181090506897)
                    ·
                      rfl

theorem cell22_3870947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 3].length) (baseStart_3870947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870947 prefixEnd_3870947 := by exact prefixLift 3870947
  have htrace : WordTrace (prefixWord ++ tailWord_3870947) baseStart_3870947 baseEnd_3870947 := by
    simpa [prefixWord, tailWord_3870947, baseEnd_3870947] using wordTrace_append hprefix tailTrace_3870947
  have hstable : (prefixWord ++ tailWord_3870947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870947).length < 2 ^ (prefixWord ++ tailWord_3870947).sum := by decide
  have hdescent : baseEnd_3870947 < baseStart_3870947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3870997 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3870997 : Nat := 118140960795 + 3870997 * 2 ^ 59
def prefixEnd_3870997 : Nat := 4983230072969 + 3 ^ 40 * 3870997 * 2
def baseEnd_3870997 : Nat := 1325121382074997626756743

theorem tailTrace_3870997 : CollatzResearch.WordTrace tailWord_3870997 prefixEnd_3870997 1325121382074997626756743 := by
  unfold tailWord_3870997
  simp only [CollatzResearch.WordTrace]
  refine ⟨141186859557046457498763245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94124573038030971665842163 141186859557046457498763245)
  ·
    refine ⟨52945072333892421562036217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141186859557046457498763245 52945072333892421562036217)
    ·
      refine ⟨39708804250419316171527163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52945072333892421562036217 39708804250419316171527163)
      ·
        refine ⟨59563206375628974257290745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39708804250419316171527163 59563206375628974257290745)
        ·
          refine ⟨44672404781721730692968059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59563206375628974257290745 44672404781721730692968059)
          ·
            refine ⟨67008607172582596039452089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44672404781721730692968059 67008607172582596039452089)
            ·
              refine ⟨50256455379436947029589067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67008607172582596039452089 50256455379436947029589067)
              ·
                refine ⟨75384683069155420544383601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50256455379436947029589067 75384683069155420544383601)
                ·
                  refine ⟨56538512301866565408287701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75384683069155420544383601 56538512301866565408287701)
                  ·
                    refine ⟨1325121382074997626756743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56538512301866565408287701 1325121382074997626756743)
                    ·
                      rfl

theorem cell22_3870997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3870997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3870997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3870997 prefixEnd_3870997 := by exact prefixLift 3870997
  have htrace : WordTrace (prefixWord ++ tailWord_3870997) baseStart_3870997 baseEnd_3870997 := by
    simpa [prefixWord, tailWord_3870997, baseEnd_3870997] using wordTrace_append hprefix tailTrace_3870997
  have hstable : (prefixWord ++ tailWord_3870997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3870997).length < 2 ^ (prefixWord ++ tailWord_3870997).sum := by decide
  have hdescent : baseEnd_3870997 < baseStart_3870997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3870997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871022 : List Nat := [4, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_3871022 : Nat := 118140960795 + 3871022 * 2 ^ 59
def prefixEnd_3871022 : Nat := 4983230072969 + 3 ^ 40 * 3871022 * 2
def baseEnd_3871022 : Nat := 441709980028635298293889

theorem tailTrace_3871022 : CollatzResearch.WordTrace tailWord_3871022 prefixEnd_3871022 441709980028635298293889 := by
  unfold tailWord_3871022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648471422744485846052915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94125180921303924512282213 17648471422744485846052915)
  ·
    refine ⟨26472707134116728769079373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17648471422744485846052915 26472707134116728769079373)
    ·
      refine ⟨9927265175293773288404765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26472707134116728769079373 9927265175293773288404765)
      ·
        refine ⟨3722724440735164983151787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9927265175293773288404765 3722724440735164983151787)
        ·
          refine ⟨5584086661102747474727681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3722724440735164983151787 5584086661102747474727681)
          ·
            refine ⟨4188064995827060606045761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5584086661102747474727681 4188064995827060606045761)
            ·
              refine ⟨3141048746870295454534321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188064995827060606045761 3141048746870295454534321)
              ·
                refine ⟨2355786560152721590900741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141048746870295454534321 2355786560152721590900741)
                ·
                  refine ⟨441709980028635298293889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2355786560152721590900741 441709980028635298293889)
                  ·
                    rfl

theorem cell22_3871022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_3871022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871022 prefixEnd_3871022 := by exact prefixLift 3871022
  have htrace : WordTrace (prefixWord ++ tailWord_3871022) baseStart_3871022 baseEnd_3871022 := by
    simpa [prefixWord, tailWord_3871022, baseEnd_3871022] using wordTrace_append hprefix tailTrace_3871022
  have hstable : (prefixWord ++ tailWord_3871022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871022).length < 2 ^ (prefixWord ++ tailWord_3871022).sum := by decide
  have hdescent : baseEnd_3871022 < baseStart_3871022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871136 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_3871136 : Nat := 118140960795 + 3871136 * 2 ^ 59
def prefixEnd_3871136 : Nat := 4983230072969 + 3 ^ 40 * 3871136 * 2
def baseEnd_3871136 : Nat := 1325168964615647597531317

theorem tailTrace_3871136 : CollatzResearch.WordTrace tailWord_3871136 prefixEnd_3871136 1325168964615647597531317 := by
  unfold tailWord_3871136
  simp only [CollatzResearch.WordTrace]
  refine ⟨70595964651771442119036631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94127952869028589492048841 70595964651771442119036631)
  ·
    refine ⟨105893946977657163178554947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70595964651771442119036631 105893946977657163178554947)
    ·
      refine ⟨158840920466485744767832421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105893946977657163178554947 158840920466485744767832421)
      ·
        refine ⟨29782672587466077143968579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158840920466485744767832421 29782672587466077143968579)
        ·
          refine ⟨44674008881199115715952869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29782672587466077143968579 44674008881199115715952869)
          ·
            refine ⟨8376376665224834196741163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44674008881199115715952869 8376376665224834196741163)
            ·
              refine ⟨12564564997837251295111745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8376376665224834196741163 12564564997837251295111745)
              ·
                refine ⟨9423423748377938471333809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12564564997837251295111745 9423423748377938471333809)
                ·
                  refine ⟨7067567811283453853500357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9423423748377938471333809 7067567811283453853500357)
                  ·
                    refine ⟨1325168964615647597531317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7067567811283453853500357 1325168964615647597531317)
                    ·
                      rfl

theorem cell22_3871136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_3871136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871136 prefixEnd_3871136 := by exact prefixLift 3871136
  have htrace : WordTrace (prefixWord ++ tailWord_3871136) baseStart_3871136 baseEnd_3871136 := by
    simpa [prefixWord, tailWord_3871136, baseEnd_3871136] using wordTrace_append hprefix tailTrace_3871136
  have hstable : (prefixWord ++ tailWord_3871136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871136).length < 2 ^ (prefixWord ++ tailWord_3871136).sum := by decide
  have hdescent : baseEnd_3871136 < baseStart_3871136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871138 : List Nat := [3, 3, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_3871138 : Nat := 118140960795 + 3871138 * 2 ^ 59
def prefixEnd_3871138 : Nat := 4983230072969 + 3 ^ 40 * 3871138 * 2
def baseEnd_3871138 : Nat := 1325169649256520258981311

theorem tailTrace_3871138 : CollatzResearch.WordTrace tailWord_3871138 prefixEnd_3871138 1325169649256520258981311 := by
  unfold tailWord_3871138
  simp only [CollatzResearch.WordTrace]
  refine ⟨35298000562383909644911517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94128001499690425719764045 35298000562383909644911517)
  ·
    refine ⟨13236750210893966116841819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35298000562383909644911517 13236750210893966116841819)
    ·
      refine ⟨19855125316340949175262729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13236750210893966116841819 19855125316340949175262729)
      ·
        refine ⟨14891343987255711881447047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19855125316340949175262729 14891343987255711881447047)
        ·
          refine ⟨22337015980883567822170571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14891343987255711881447047 22337015980883567822170571)
          ·
            refine ⟨33505523971325351733255857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22337015980883567822170571 33505523971325351733255857)
            ·
              refine ⟨25129142978494013799941893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33505523971325351733255857 25129142978494013799941893)
              ·
                refine ⟨4711714308467627587489105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25129142978494013799941893 4711714308467627587489105)
                ·
                  refine ⟨3533785731350720690616829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4711714308467627587489105 3533785731350720690616829)
                  ·
                    refine ⟨1325169649256520258981311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533785731350720690616829 1325169649256520258981311)
                    ·
                      rfl

theorem cell22_3871138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_3871138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871138 prefixEnd_3871138 := by exact prefixLift 3871138
  have htrace : WordTrace (prefixWord ++ tailWord_3871138) baseStart_3871138 baseEnd_3871138 := by
    simpa [prefixWord, tailWord_3871138, baseEnd_3871138] using wordTrace_append hprefix tailTrace_3871138
  have hstable : (prefixWord ++ tailWord_3871138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871138).length < 2 ^ (prefixWord ++ tailWord_3871138).sum := by decide
  have hdescent : baseEnd_3871138 < baseStart_3871138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871183 : List Nat := [1, 1, 2, 1, 1, 4, 1, 7, 1, 3]
def baseStart_3871183 : Nat := 118140960795 + 3871183 * 2 ^ 59
def prefixEnd_3871183 : Nat := 4983230072969 + 3 ^ 40 * 3871183 * 2
def baseEnd_3871183 : Nat := 1325185053676155141606173

theorem tailTrace_3871183 : CollatzResearch.WordTrace tailWord_3871183 prefixEnd_3871183 1325185053676155141606173 := by
  unfold tailWord_3871183
  simp only [CollatzResearch.WordTrace]
  refine ⟨141193643534372611265034203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94129095689581740843356135 141193643534372611265034203)
  ·
    refine ⟨211790465301558916897551305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141193643534372611265034203 211790465301558916897551305)
    ·
      refine ⟨158842848976169187673163479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211790465301558916897551305 158842848976169187673163479)
      ·
        refine ⟨238264273464253781509745219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158842848976169187673163479 238264273464253781509745219)
        ·
          refine ⟨357396410196380672264617829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238264273464253781509745219 357396410196380672264617829)
          ·
            refine ⟨67011826911821376049615843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 357396410196380672264617829 67011826911821376049615843)
            ·
              refine ⟨100517740367732064074423765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67011826911821376049615843 100517740367732064074423765)
              ·
                refine ⟨2355884539868720251744307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100517740367732064074423765 2355884539868720251744307)
                ·
                  refine ⟨3533826809803080377616461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355884539868720251744307 3533826809803080377616461)
                  ·
                    refine ⟨1325185053676155141606173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533826809803080377616461 1325185053676155141606173)
                    ·
                      rfl

theorem cell22_3871183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 3].length) (baseStart_3871183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871183 prefixEnd_3871183 := by exact prefixLift 3871183
  have htrace : WordTrace (prefixWord ++ tailWord_3871183) baseStart_3871183 baseEnd_3871183 := by
    simpa [prefixWord, tailWord_3871183, baseEnd_3871183] using wordTrace_append hprefix tailTrace_3871183
  have hstable : (prefixWord ++ tailWord_3871183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871183).length < 2 ^ (prefixWord ++ tailWord_3871183).sum := by decide
  have hdescent : baseEnd_3871183 < baseStart_3871183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871202 : List Nat := [3, 3, 3, 2, 2, 1, 1, 7]
def baseStart_3871202 : Nat := 118140960795 + 3871202 * 2 ^ 59
def prefixEnd_3871202 : Nat := 4983230072969 + 3 ^ 40 * 3871202 * 2
def baseEnd_3871202 : Nat := 147243506418271713931235

theorem tailTrace_3871202 : CollatzResearch.WordTrace tailWord_3871202 prefixEnd_3871202 147243506418271713931235 := by
  unfold tailWord_3871202
  simp only [CollatzResearch.WordTrace]
  refine ⟨35298584130325944377493965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94129557680869185006650573 35298584130325944377493965)
  ·
    refine ⟨13236969048872229141560237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35298584130325944377493965 13236969048872229141560237)
    ·
      refine ⟨4963863393327085928085089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13236969048872229141560237 4963863393327085928085089)
      ·
        refine ⟨3722897544995314446063817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4963863393327085928085089 3722897544995314446063817)
        ·
          refine ⟨2792173158746485834547863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3722897544995314446063817 2792173158746485834547863)
          ·
            refine ⟨4188259738119728751821795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792173158746485834547863 4188259738119728751821795)
            ·
              refine ⟨6282389607179593127732693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188259738119728751821795 6282389607179593127732693)
              ·
                refine ⟨147243506418271713931235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6282389607179593127732693 147243506418271713931235)
                ·
                  rfl

theorem cell22_3871202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_3871202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871202 prefixEnd_3871202 := by exact prefixLift 3871202
  have htrace : WordTrace (prefixWord ++ tailWord_3871202) baseStart_3871202 baseEnd_3871202 := by
    simpa [prefixWord, tailWord_3871202, baseEnd_3871202] using wordTrace_append hprefix tailTrace_3871202
  have hstable : (prefixWord ++ tailWord_3871202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871202).length < 2 ^ (prefixWord ++ tailWord_3871202).sum := by decide
  have hdescent : baseEnd_3871202 < baseStart_3871202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871213 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 5]
def baseStart_3871213 : Nat := 118140960795 + 3871213 * 2 ^ 59
def prefixEnd_3871213 : Nat := 4983230072969 + 3 ^ 40 * 3871213 * 2
def baseEnd_3871213 : Nat := 441731774429748354452027

theorem tailTrace_3871213 : CollatzResearch.WordTrace tailWord_3871213 prefixEnd_3871213 441731774429748354452027 := by
  unfold tailWord_3871213
  simp only [CollatzResearch.WordTrace]
  refine ⟨141194737724263926388626293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94129825149509284259084195 141194737724263926388626293)
  ·
    refine ⟨13237006661649743098933715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141194737724263926388626293 13237006661649743098933715)
    ·
      refine ⟨19855509992474614648400573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13237006661649743098933715 19855509992474614648400573)
      ·
        refine ⟨7445816247177980493150215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19855509992474614648400573 7445816247177980493150215)
        ·
          refine ⟨11168724370766970739725323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445816247177980493150215 11168724370766970739725323)
          ·
            refine ⟨16753086556150456109587985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11168724370766970739725323 16753086556150456109587985)
            ·
              refine ⟨12564814917112842082190989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16753086556150456109587985 12564814917112842082190989)
              ·
                refine ⟨4711805593917315780821621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12564814917112842082190989 4711805593917315780821621)
                ·
                  refine ⟨441731774429748354452027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4711805593917315780821621 441731774429748354452027)
                  ·
                    rfl

theorem cell22_3871213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_3871213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871213 prefixEnd_3871213 := by exact prefixLift 3871213
  have htrace : WordTrace (prefixWord ++ tailWord_3871213) baseStart_3871213 baseEnd_3871213 := by
    simpa [prefixWord, tailWord_3871213, baseEnd_3871213] using wordTrace_append hprefix tailTrace_3871213
  have hstable : (prefixWord ++ tailWord_3871213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871213).length < 2 ^ (prefixWord ++ tailWord_3871213).sum := by decide
  have hdescent : baseEnd_3871213 < baseStart_3871213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871234 : List Nat := [3, 4, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3871234 : Nat := 118140960795 + 3871234 * 2 ^ 59
def prefixEnd_3871234 : Nat := 4983230072969 + 3 ^ 40 * 3871234 * 2
def baseEnd_3871234 : Nat := 1325202512018408008581017

theorem tailTrace_3871234 : CollatzResearch.WordTrace tailWord_3871234 prefixEnd_3871234 1325202512018408008581017 := by
  unfold tailWord_3871234
  simp only [CollatzResearch.WordTrace]
  refine ⟨35298875914296961743785189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94130335771458564650093837 35298875914296961743785189)
  ·
    refine ⟨6618539233930680326959723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35298875914296961743785189 6618539233930680326959723)
    ·
      refine ⟨9927808850896020490439585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6618539233930680326959723 9927808850896020490439585)
      ·
        refine ⟨7445856638172015367829689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9927808850896020490439585 7445856638172015367829689)
        ·
          refine ⟨5584392478629011525872267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7445856638172015367829689 5584392478629011525872267)
          ·
            refine ⟨8376588717943517288808401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584392478629011525872267 8376588717943517288808401)
            ·
              refine ⟨6282441538457637966606301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8376588717943517288808401 6282441538457637966606301)
              ·
                refine ⟨2355915576921614237477363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6282441538457637966606301 2355915576921614237477363)
                ·
                  refine ⟨3533873365382421356216045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355915576921614237477363 3533873365382421356216045)
                  ·
                    refine ⟨1325202512018408008581017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533873365382421356216045 1325202512018408008581017)
                    ·
                      rfl

theorem cell22_3871234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3871234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871234 prefixEnd_3871234 := by exact prefixLift 3871234
  have htrace : WordTrace (prefixWord ++ tailWord_3871234) baseStart_3871234 baseEnd_3871234 := by
    simpa [prefixWord, tailWord_3871234, baseEnd_3871234] using wordTrace_append hprefix tailTrace_3871234
  have hstable : (prefixWord ++ tailWord_3871234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871234).length < 2 ^ (prefixWord ++ tailWord_3871234).sum := by decide
  have hdescent : baseEnd_3871234 < baseStart_3871234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871243 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 1, 4]
def baseStart_3871243 : Nat := 118140960795 + 3871243 * 2 ^ 59
def prefixEnd_3871243 : Nat := 4983230072969 + 3 ^ 40 * 3871243 * 2
def baseEnd_3871243 : Nat := 1325205592902334985105989

theorem tailTrace_3871243 : CollatzResearch.WordTrace tailWord_3871243 prefixEnd_3871243 1325205592902334985105989 := by
  unfold tailWord_3871243
  simp only [CollatzResearch.WordTrace]
  refine ⟨141195831914155241512218383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94130554609436827674812255 141195831914155241512218383)
  ·
    refine ⟨211793747871232862268327575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141195831914155241512218383 211793747871232862268327575)
    ·
      refine ⟨317690621806849293402491363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211793747871232862268327575 317690621806849293402491363)
      ·
        refine ⟨476535932710273940103737045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317690621806849293402491363 476535932710273940103737045)
        ·
          refine ⟨11168810922897045471181337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 476535932710273940103737045 11168810922897045471181337)
          ·
            refine ⟨8376608192172784103386003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11168810922897045471181337 8376608192172784103386003)
            ·
              refine ⟨12564912288259176155079005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8376608192172784103386003 12564912288259176155079005)
              ·
                refine ⟨4711842108097191058154627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12564912288259176155079005 4711842108097191058154627)
                ·
                  refine ⟨7067763162145786587231941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711842108097191058154627 7067763162145786587231941)
                  ·
                    refine ⟨1325205592902334985105989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7067763162145786587231941 1325205592902334985105989)
                    ·
                      rfl

theorem cell22_3871243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 4].length) (baseStart_3871243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871243 prefixEnd_3871243 := by exact prefixLift 3871243
  have htrace : WordTrace (prefixWord ++ tailWord_3871243) baseStart_3871243 baseEnd_3871243 := by
    simpa [prefixWord, tailWord_3871243, baseEnd_3871243] using wordTrace_append hprefix tailTrace_3871243
  have hstable : (prefixWord ++ tailWord_3871243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871243).length < 2 ^ (prefixWord ++ tailWord_3871243).sum := by decide
  have hdescent : baseEnd_3871243 < baseStart_3871243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871245 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3871245 : Nat := 118140960795 + 3871245 * 2 ^ 59
def prefixEnd_3871245 : Nat := 4983230072969 + 3 ^ 40 * 3871245 * 2
def baseEnd_3871245 : Nat := 1325206277543207646555983

theorem tailTrace_3871245 : CollatzResearch.WordTrace tailWord_3871245 prefixEnd_3871245 1325206277543207646555983 := by
  unfold tailWord_3871245
  simp only [CollatzResearch.WordTrace]
  refine ⟨141195904860147995853791189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94130603240098663902527459 141195904860147995853791189)
  ·
    refine ⟨3309279020159718652823231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 141195904860147995853791189 3309279020159718652823231)
    ·
      refine ⟨4963918530239577979234847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3309279020159718652823231 4963918530239577979234847)
      ·
        refine ⟨7445877795359366968852271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4963918530239577979234847 7445877795359366968852271)
        ·
          refine ⟨11168816693039050453278407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445877795359366968852271 11168816693039050453278407)
          ·
            refine ⟨16753225039558575679917611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11168816693039050453278407 16753225039558575679917611)
            ·
              refine ⟨25129837559337863519876417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16753225039558575679917611 25129837559337863519876417)
              ·
                refine ⟨18847378169503397639907313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25129837559337863519876417 18847378169503397639907313)
                ·
                  refine ⟨14135533627127548229930485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18847378169503397639907313 14135533627127548229930485)
                  ·
                    refine ⟨1325206277543207646555983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14135533627127548229930485 1325206277543207646555983)
                    ·
                      rfl

theorem cell22_3871245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3871245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871245 prefixEnd_3871245 := by exact prefixLift 3871245
  have htrace : WordTrace (prefixWord ++ tailWord_3871245) baseStart_3871245 baseEnd_3871245 := by
    simpa [prefixWord, tailWord_3871245, baseEnd_3871245] using wordTrace_append hprefix tailTrace_3871245
  have hstable : (prefixWord ++ tailWord_3871245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871245).length < 2 ^ (prefixWord ++ tailWord_3871245).sum := by decide
  have hdescent : baseEnd_3871245 < baseStart_3871245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871258 : List Nat := [3, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_3871258 : Nat := 118140960795 + 3871258 * 2 ^ 59
def prefixEnd_3871258 : Nat := 4983230072969 + 3 ^ 40 * 3871258 * 2
def baseEnd_3871258 : Nat := 441736909236293315326981

theorem tailTrace_3871258 : CollatzResearch.WordTrace tailWord_3871258 prefixEnd_3871258 441736909236293315326981 := by
  unfold tailWord_3871258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35299094752275224768503607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94130919339400599382676285 35299094752275224768503607)
  ·
    refine ⟨52948642128412837152755411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35299094752275224768503607 52948642128412837152755411)
    ·
      refine ⟨79422963192619255729133117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52948642128412837152755411 79422963192619255729133117)
      ·
        refine ⟨29783611197232220898424919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79422963192619255729133117 29783611197232220898424919)
        ·
          refine ⟨44675416795848331347637379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29783611197232220898424919 44675416795848331347637379)
          ·
            refine ⟨67013125193772497021456069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44675416795848331347637379 67013125193772497021456069)
            ·
              refine ⟨12564960973832343191523013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67013125193772497021456069 12564960973832343191523013)
              ·
                refine ⟨2355930182593564348410565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12564960973832343191523013 2355930182593564348410565)
                ·
                  refine ⟨441736909236293315326981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2355930182593564348410565 441736909236293315326981)
                  ·
                    rfl

theorem cell22_3871258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_3871258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871258 prefixEnd_3871258 := by exact prefixLift 3871258
  have htrace : WordTrace (prefixWord ++ tailWord_3871258) baseStart_3871258 baseEnd_3871258 := by
    simpa [prefixWord, tailWord_3871258, baseEnd_3871258] using wordTrace_append hprefix tailTrace_3871258
  have hstable : (prefixWord ++ tailWord_3871258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871258).length < 2 ^ (prefixWord ++ tailWord_3871258).sum := by decide
  have hdescent : baseEnd_3871258 < baseStart_3871258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871324 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3871324 : Nat := 118140960795 + 3871324 * 2 ^ 59
def prefixEnd_3871324 : Nat := 4983230072969 + 3 ^ 40 * 3871324 * 2
def baseEnd_3871324 : Nat := 1325233320857677773830741

theorem tailTrace_3871324 : CollatzResearch.WordTrace tailWord_3871324 prefixEnd_3871324 1325233320857677773830741 := by
  unfold tailWord_3871324
  simp only [CollatzResearch.WordTrace]
  refine ⟨70599393113430896172958513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94132524151241194897278017 70599393113430896172958513)
  ·
    refine ⟨52949544835073172129718885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70599393113430896172958513 52949544835073172129718885)
    ·
      refine ⟨9928039656576219774322291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52949544835073172129718885 9928039656576219774322291)
      ·
        refine ⟨14892059484864329661483437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9928039656576219774322291 14892059484864329661483437)
        ·
          refine ⟨5584522306824123623056289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14892059484864329661483437 5584522306824123623056289)
          ·
            refine ⟨4188391730118092717292217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5584522306824123623056289 4188391730118092717292217)
            ·
              refine ⟨3141293797588569537969163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188391730118092717292217 3141293797588569537969163)
              ·
                refine ⟨4711940696382854306953745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141293797588569537969163 4711940696382854306953745)
                ·
                  refine ⟨3533955522287140730215309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4711940696382854306953745 3533955522287140730215309)
                  ·
                    refine ⟨1325233320857677773830741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533955522287140730215309 1325233320857677773830741)
                    ·
                      rfl

theorem cell22_3871324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3871324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871324 prefixEnd_3871324 := by exact prefixLift 3871324
  have htrace : WordTrace (prefixWord ++ tailWord_3871324) baseStart_3871324 baseEnd_3871324 := by
    simpa [prefixWord, tailWord_3871324, baseEnd_3871324] using wordTrace_append hprefix tailTrace_3871324
  have hstable : (prefixWord ++ tailWord_3871324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871324).length < 2 ^ (prefixWord ++ tailWord_3871324).sum := by decide
  have hdescent : baseEnd_3871324 < baseStart_3871324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871380 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3871380 : Nat := 118140960795 + 3871380 * 2 ^ 59
def prefixEnd_3871380 : Nat := 4983230072969 + 3 ^ 40 * 3871380 * 2
def baseEnd_3871380 : Nat := 1325252490802112294430569

theorem tailTrace_3871380 : CollatzResearch.WordTrace tailWord_3871380 prefixEnd_3871380 1325252490802112294430569 := by
  unfold tailWord_3871380
  simp only [CollatzResearch.WordTrace]
  refine ⟨70600414357329456954977797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94133885809772609273303729 70600414357329456954977797)
  ·
    refine ⟨13237577691999273179058337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70600414357329456954977797 13237577691999273179058337)
    ·
      refine ⟨9928183268999454884293753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13237577691999273179058337 9928183268999454884293753)
      ·
        refine ⟨7446137451749591163220315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9928183268999454884293753 7446137451749591163220315)
        ·
          refine ⟨11169206177624386744830473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7446137451749591163220315 11169206177624386744830473)
          ·
            refine ⟨8376904633218290058622855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11169206177624386744830473 8376904633218290058622855)
            ·
              refine ⟨12565356949827435087934283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8376904633218290058622855 12565356949827435087934283)
              ·
                refine ⟨18848035424741152631901425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12565356949827435087934283 18848035424741152631901425)
                ·
                  refine ⟨14136026568555864473926069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18848035424741152631901425 14136026568555864473926069)
                  ·
                    refine ⟨1325252490802112294430569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14136026568555864473926069 1325252490802112294430569)
                    ·
                      rfl

theorem cell22_3871380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3871380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871380 prefixEnd_3871380 := by exact prefixLift 3871380
  have htrace : WordTrace (prefixWord ++ tailWord_3871380) baseStart_3871380 baseEnd_3871380 := by
    simpa [prefixWord, tailWord_3871380, baseEnd_3871380] using wordTrace_append hprefix tailTrace_3871380
  have hstable : (prefixWord ++ tailWord_3871380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871380).length < 2 ^ (prefixWord ++ tailWord_3871380).sum := by decide
  have hdescent : baseEnd_3871380 < baseStart_3871380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871408 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 4, 3]
def baseStart_3871408 : Nat := 118140960795 + 3871408 * 2 ^ 59
def prefixEnd_3871408 : Nat := 4983230072969 + 3 ^ 40 * 3871408 * 2
def baseEnd_3871408 : Nat := 1325262075774329554730483

theorem tailTrace_3871408 : CollatzResearch.WordTrace tailWord_3871408 prefixEnd_3871408 1325262075774329554730483 := by
  unfold tailWord_3871408
  simp only [CollatzResearch.WordTrace]
  refine ⟨70600924979278737345987439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94134566639038316461316585 70600924979278737345987439)
  ·
    refine ⟨105901387468918106018981159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70600924979278737345987439 105901387468918106018981159)
    ·
      refine ⟨158852081203377159028471739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105901387468918106018981159 158852081203377159028471739)
      ·
        refine ⟨238278121805065738542707609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158852081203377159028471739 238278121805065738542707609)
        ·
          refine ⟨178708591353799303907030707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238278121805065738542707609 178708591353799303907030707)
          ·
            refine ⟨268062887030698955860546061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178708591353799303907030707 268062887030698955860546061)
            ·
              refine ⟨100523582636512108447704773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268062887030698955860546061 100523582636512108447704773)
              ·
                refine ⟨18848171744346020333944645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100523582636512108447704773 18848171744346020333944645)
                ·
                  refine ⟨3534032202064878812614621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18848171744346020333944645 3534032202064878812614621)
                  ·
                    refine ⟨1325262075774329554730483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3534032202064878812614621 1325262075774329554730483)
                    ·
                      rfl

theorem cell22_3871408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_3871408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871408 prefixEnd_3871408 := by exact prefixLift 3871408
  have htrace : WordTrace (prefixWord ++ tailWord_3871408) baseStart_3871408 baseEnd_3871408 := by
    simpa [prefixWord, tailWord_3871408, baseEnd_3871408] using wordTrace_append hprefix tailTrace_3871408
  have hstable : (prefixWord ++ tailWord_3871408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871408).length < 2 ^ (prefixWord ++ tailWord_3871408).sum := by decide
  have hdescent : baseEnd_3871408 < baseStart_3871408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871442 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_3871442 : Nat := 118140960795 + 3871442 * 2 ^ 59
def prefixEnd_3871442 : Nat := 4983230072969 + 3 ^ 40 * 3871442 * 2
def baseEnd_3871442 : Nat := 1325273714669164799380379

theorem tailTrace_3871442 : CollatzResearch.WordTrace tailWord_3871442 prefixEnd_3871442 1325273714669164799380379 := by
  unfold tailWord_3871442
  simp only [CollatzResearch.WordTrace]
  refine ⟨35300772510108574624678145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94135393360289532332475053 35300772510108574624678145)
  ·
    refine ⟨26475579382581430968508609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35300772510108574624678145 26475579382581430968508609)
    ·
      refine ⟨19856684536936073226381457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26475579382581430968508609 19856684536936073226381457)
      ·
        refine ⟨14892513402702054919786093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19856684536936073226381457 14892513402702054919786093)
        ·
          refine ⟨5584692526013270594919785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14892513402702054919786093 5584692526013270594919785)
          ·
            refine ⟨4188519394509952946189839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5584692526013270594919785 4188519394509952946189839)
            ·
              refine ⟨6282779091764929419284759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188519394509952946189839 6282779091764929419284759)
              ·
                refine ⟨9424168637647394128927139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6282779091764929419284759 9424168637647394128927139)
                ·
                  refine ⟨14136252956471091193390709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9424168637647394128927139 14136252956471091193390709)
                  ·
                    refine ⟨1325273714669164799380379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14136252956471091193390709 1325273714669164799380379)
                    ·
                      rfl

theorem cell22_3871442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_3871442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871442 prefixEnd_3871442 := by exact prefixLift 3871442
  have htrace : WordTrace (prefixWord ++ tailWord_3871442) baseStart_3871442 baseEnd_3871442 := by
    simpa [prefixWord, tailWord_3871442, baseEnd_3871442] using wordTrace_append hprefix tailTrace_3871442
  have hstable : (prefixWord ++ tailWord_3871442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871442).length < 2 ^ (prefixWord ++ tailWord_3871442).sum := by decide
  have hdescent : baseEnd_3871442 < baseStart_3871442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871455 : List Nat := [1, 1, 2, 3, 2, 5, 2, 6]
def baseStart_3871455 : Nat := 118140960795 + 3871455 * 2 ^ 59
def prefixEnd_3871455 : Nat := 4983230072969 + 3 ^ 40 * 3871455 * 2
def baseEnd_3871455 : Nat := 147253129426093010978371

theorem tailTrace_3871455 : CollatzResearch.WordTrace tailWord_3871455 prefixEnd_3871455 147253129426093010978371 := by
  unfold tailWord_3871455
  simp only [CollatzResearch.WordTrace]
  refine ⟨141203564189387201718935819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94135709459591467812623879 141203564189387201718935819)
  ·
    refine ⟨211805346284080802578403729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141203564189387201718935819 211805346284080802578403729)
    ·
      refine ⟨158854009713060601933802797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211805346284080802578403729 158854009713060601933802797)
      ·
        refine ⟨59570253642397725725176049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158854009713060601933802797 59570253642397725725176049)
        ·
          refine ⟨44677690231798294293882037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59570253642397725725176049 44677690231798294293882037)
          ·
            refine ⟨4188533459231090090051441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44677690231798294293882037 4188533459231090090051441)
            ·
              refine ⟨3141400094423317567538581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4188533459231090090051441 3141400094423317567538581)
              ·
                refine ⟨147253129426093010978371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3141400094423317567538581 147253129426093010978371)
                ·
                  rfl

theorem cell22_3871455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 6].length) (baseStart_3871455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871455 prefixEnd_3871455 := by exact prefixLift 3871455
  have htrace : WordTrace (prefixWord ++ tailWord_3871455) baseStart_3871455 baseEnd_3871455 := by
    simpa [prefixWord, tailWord_3871455, baseEnd_3871455] using wordTrace_append hprefix tailTrace_3871455
  have hstable : (prefixWord ++ tailWord_3871455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871455).length < 2 ^ (prefixWord ++ tailWord_3871455).sum := by decide
  have hdescent : baseEnd_3871455 < baseStart_3871455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871498 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3871498 : Nat := 118140960795 + 3871498 * 2 ^ 59
def prefixEnd_3871498 : Nat := 4983230072969 + 3 ^ 40 * 3871498 * 2
def baseEnd_3871498 : Nat := 1325292884613599319980207

theorem tailTrace_3871498 : CollatzResearch.WordTrace tailWord_3871498 prefixEnd_3871498 1325292884613599319980207 := by
  unfold tailWord_3871498
  simp only [CollatzResearch.WordTrace]
  refine ⟨35301283132057855015687787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94136755018820946708500765 35301283132057855015687787)
  ·
    refine ⟨52951924698086782523531681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35301283132057855015687787 52951924698086782523531681)
    ·
      refine ⟨39713943523565086892648761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52951924698086782523531681 39713943523565086892648761)
      ·
        refine ⟨29785457642673815169486571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39713943523565086892648761 29785457642673815169486571)
        ·
          refine ⟨44678186464010722754229857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29785457642673815169486571 44678186464010722754229857)
          ·
            refine ⟨33508639848008042065672393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44678186464010722754229857 33508639848008042065672393)
            ·
              refine ⟨25131479886006031549254295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33508639848008042065672393 25131479886006031549254295)
              ·
                refine ⟨37697219829009047323881443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25131479886006031549254295 37697219829009047323881443)
                ·
                  refine ⟨56545829743513570985822165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37697219829009047323881443 56545829743513570985822165)
                  ·
                    refine ⟨1325292884613599319980207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56545829743513570985822165 1325292884613599319980207)
                    ·
                      rfl

theorem cell22_3871498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3871498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871498 prefixEnd_3871498 := by exact prefixLift 3871498
  have htrace : WordTrace (prefixWord ++ tailWord_3871498) baseStart_3871498 baseEnd_3871498 := by
    simpa [prefixWord, tailWord_3871498, baseEnd_3871498] using wordTrace_append hprefix tailTrace_3871498
  have hstable : (prefixWord ++ tailWord_3871498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871498).length < 2 ^ (prefixWord ++ tailWord_3871498).sum := by decide
  have hdescent : baseEnd_3871498 < baseStart_3871498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871543 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 3, 5]
def baseStart_3871543 : Nat := 118140960795 + 3871543 * 2 ^ 59
def prefixEnd_3871543 : Nat := 4983230072969 + 3 ^ 40 * 3871543 * 2
def baseEnd_3871543 : Nat := 1325308289033234202605069

theorem tailTrace_3871543 : CollatzResearch.WordTrace tailWord_3871543 prefixEnd_3871543 1325308289033234202605069 := by
  unfold tailWord_3871543
  simp only [CollatzResearch.WordTrace]
  refine ⟨141206773813068392748139283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94137849208712261832092855 141206773813068392748139283)
  ·
    refine ⟨211810160719602589122208925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141206773813068392748139283 211810160719602589122208925)
    ·
      refine ⟨79428810269850970920828347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211810160719602589122208925 79428810269850970920828347)
      ·
        refine ⟨119143215404776456381242521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79428810269850970920828347 119143215404776456381242521)
        ·
          refine ⟨89357411553582342285931891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119143215404776456381242521 89357411553582342285931891)
          ·
            refine ⟨134036117330373513428897837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89357411553582342285931891 134036117330373513428897837)
            ·
              refine ⟨50263543998890067535836689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134036117330373513428897837 50263543998890067535836689)
              ·
                refine ⟨37697657999167550651877517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50263543998890067535836689 37697657999167550651877517)
                ·
                  refine ⟨14136621749687831494454069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37697657999167550651877517 14136621749687831494454069)
                  ·
                    refine ⟨1325308289033234202605069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14136621749687831494454069 1325308289033234202605069)
                    ·
                      rfl

theorem cell22_3871543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_3871543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871543 prefixEnd_3871543 := by exact prefixLift 3871543
  have htrace : WordTrace (prefixWord ++ tailWord_3871543) baseStart_3871543 baseEnd_3871543 := by
    simpa [prefixWord, tailWord_3871543, baseEnd_3871543] using wordTrace_append hprefix tailTrace_3871543
  have hstable : (prefixWord ++ tailWord_3871543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871543).length < 2 ^ (prefixWord ++ tailWord_3871543).sum := by decide
  have hdescent : baseEnd_3871543 < baseStart_3871543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871560 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_3871560 : Nat := 118140960795 + 3871560 * 2 ^ 59
def prefixEnd_3871560 : Nat := 4983230072969 + 3 ^ 40 * 3871560 * 2
def baseEnd_3871560 : Nat := 1325314108480651824930017

theorem tailTrace_3871560 : CollatzResearch.WordTrace tailWord_3871560 prefixEnd_3871560 1325314108480651824930017 := by
  unfold tailWord_3871560
  simp only [CollatzResearch.WordTrace]
  refine ⟨70603696927003402325754067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94138262569337869767672089 70603696927003402325754067)
  ·
    refine ⟨105905545390505103488631101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70603696927003402325754067 105905545390505103488631101)
    ·
      refine ⟨39714579521439413808236663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105905545390505103488631101 39714579521439413808236663)
      ·
        refine ⟨59571869282159120712354995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39714579521439413808236663 59571869282159120712354995)
        ·
          refine ⟨89357803923238681068532493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59571869282159120712354995 89357803923238681068532493)
          ·
            refine ⟨33509176471214505400699685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89357803923238681068532493 33509176471214505400699685)
            ·
              refine ⟨6282970588352719762631191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33509176471214505400699685 6282970588352719762631191)
              ·
                refine ⟨9424455882529079643946787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6282970588352719762631191 9424455882529079643946787)
                ·
                  refine ⟨14136683823793619465920181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9424455882529079643946787 14136683823793619465920181)
                  ·
                    refine ⟨1325314108480651824930017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14136683823793619465920181 1325314108480651824930017)
                    ·
                      rfl

theorem cell22_3871560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_3871560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871560 prefixEnd_3871560 := by exact prefixLift 3871560
  have htrace : WordTrace (prefixWord ++ tailWord_3871560) baseStart_3871560 baseEnd_3871560 := by
    simpa [prefixWord, tailWord_3871560, baseEnd_3871560] using wordTrace_append hprefix tailTrace_3871560
  have hstable : (prefixWord ++ tailWord_3871560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871560).length < 2 ^ (prefixWord ++ tailWord_3871560).sum := by decide
  have hdescent : baseEnd_3871560 < baseStart_3871560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871575 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 1, 6]
def baseStart_3871575 : Nat := 118140960795 + 3871575 * 2 ^ 59
def prefixEnd_3871575 : Nat := 4983230072969 + 3 ^ 40 * 3871575 * 2
def baseEnd_3871575 : Nat := 1325319243287196785804971

theorem tailTrace_3871575 : CollatzResearch.WordTrace tailWord_3871575 prefixEnd_3871575 1325319243287196785804971 := by
  unfold tailWord_3871575
  simp only [CollatzResearch.WordTrace]
  refine ⟨141207940948952462213304179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94138627299301641475536119 141207940948952462213304179)
  ·
    refine ⟨211811911423428693319956269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141207940948952462213304179 211811911423428693319956269)
    ·
      refine ⟨79429466783785759994983601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211811911423428693319956269 79429466783785759994983601)
      ·
        refine ⟨59572100087839319996237701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79429466783785759994983601 59572100087839319996237701)
        ·
          refine ⟨11169768766469872499294569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59572100087839319996237701 11169768766469872499294569)
          ·
            refine ⟨8377326574852404374470927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11169768766469872499294569 8377326574852404374470927)
            ·
              refine ⟨12565989862278606561706391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377326574852404374470927 12565989862278606561706391)
              ·
                refine ⟨18848984793417909842559587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12565989862278606561706391 18848984793417909842559587)
                ·
                  refine ⟨28273477190126864763839381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18848984793417909842559587 28273477190126864763839381)
                  ·
                    refine ⟨1325319243287196785804971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28273477190126864763839381 1325319243287196785804971)
                    ·
                      rfl

theorem cell22_3871575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_3871575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871575 prefixEnd_3871575 := by exact prefixLift 3871575
  have htrace : WordTrace (prefixWord ++ tailWord_3871575) baseStart_3871575 baseEnd_3871575 := by
    simpa [prefixWord, tailWord_3871575, baseEnd_3871575] using wordTrace_append hprefix tailTrace_3871575
  have hstable : (prefixWord ++ tailWord_3871575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871575).length < 2 ^ (prefixWord ++ tailWord_3871575).sum := by decide
  have hdescent : baseEnd_3871575 < baseStart_3871575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871603 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 1, 8]
def baseStart_3871603 : Nat := 118140960795 + 3871603 * 2 ^ 59
def prefixEnd_3871603 : Nat := 4983230072969 + 3 ^ 40 * 3871603 * 2
def baseEnd_3871603 : Nat := 1325328828259414046104885

theorem tailTrace_3871603 : CollatzResearch.WordTrace tailWord_3871603 prefixEnd_3871603 1325328828259414046104885 := by
  unfold tailWord_3871603
  simp only [CollatzResearch.WordTrace]
  refine ⟨141208962192851022995323463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94139308128567348663548975 141208962192851022995323463)
  ·
    refine ⟨211813443289276534492985195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141208962192851022995323463 211813443289276534492985195)
    ·
      refine ⟨317720164933914801739477793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211813443289276534492985195 317720164933914801739477793)
      ·
        refine ⟨238290123700436101304608345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317720164933914801739477793 238290123700436101304608345)
        ·
          refine ⟨178717592775327075978456259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238290123700436101304608345 178717592775327075978456259)
          ·
            refine ⟨268076389162990613967684389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178717592775327075978456259 268076389162990613967684389)
            ·
              refine ⟨50264322968060740118940823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268076389162990613967684389 50264322968060740118940823)
              ·
                refine ⟨75396484452091110178411235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50264322968060740118940823 75396484452091110178411235)
                ·
                  refine ⟨113094726678136665267616853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75396484452091110178411235 113094726678136665267616853)
                  ·
                    refine ⟨1325328828259414046104885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113094726678136665267616853 1325328828259414046104885)
                    ·
                      rfl

theorem cell22_3871603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_3871603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871603 prefixEnd_3871603 := by exact prefixLift 3871603
  have htrace : WordTrace (prefixWord ++ tailWord_3871603) baseStart_3871603 baseEnd_3871603 := by
    simpa [prefixWord, tailWord_3871603, baseEnd_3871603] using wordTrace_append hprefix tailTrace_3871603
  have hstable : (prefixWord ++ tailWord_3871603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871603).length < 2 ^ (prefixWord ++ tailWord_3871603).sum := by decide
  have hdescent : baseEnd_3871603 < baseStart_3871603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871695 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 3, 5]
def baseStart_3871695 : Nat := 118140960795 + 3871695 * 2 ^ 59
def prefixEnd_3871695 : Nat := 4983230072969 + 3 ^ 40 * 3871695 * 2
def baseEnd_3871695 : Nat := 1325360321739556472804603

theorem tailTrace_3871695 : CollatzResearch.WordTrace tailWord_3871695 prefixEnd_3871695 1325360321739556472804603 := by
  unfold tailWord_3871695
  simp only [CollatzResearch.WordTrace]
  refine ⟨141212317708517722707672539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94141545139011815138448359 141212317708517722707672539)
  ·
    refine ⟨211818476562776584061508809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141212317708517722707672539 211818476562776584061508809)
    ·
      refine ⟨158863857422082438046131607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211818476562776584061508809 158863857422082438046131607)
      ·
        refine ⟨238295786133123657069197411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158863857422082438046131607 238295786133123657069197411)
        ·
          refine ⟨357443679199685485603796117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238295786133123657069197411 357443679199685485603796117)
          ·
            refine ⟨16755172462485257137677943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 357443679199685485603796117 16755172462485257137677943)
            ·
              refine ⟨25132758693727885706516915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16755172462485257137677943 25132758693727885706516915)
              ·
                refine ⟨37699138040591828559775373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25132758693727885706516915 37699138040591828559775373)
                ·
                  refine ⟨14137176765221935709915765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37699138040591828559775373 14137176765221935709915765)
                  ·
                    refine ⟨1325360321739556472804603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14137176765221935709915765 1325360321739556472804603)
                    ·
                      rfl

theorem cell22_3871695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_3871695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871695 prefixEnd_3871695 := by exact prefixLift 3871695
  have htrace : WordTrace (prefixWord ++ tailWord_3871695) baseStart_3871695 baseEnd_3871695 := by
    simpa [prefixWord, tailWord_3871695, baseEnd_3871695] using wordTrace_append hprefix tailTrace_3871695
  have hstable : (prefixWord ++ tailWord_3871695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871695).length < 2 ^ (prefixWord ++ tailWord_3871695).sum := by decide
  have hdescent : baseEnd_3871695 < baseStart_3871695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871697 : List Nat := [1, 2, 2, 1, 2, 1, 4, 5, 4]
def baseStart_3871697 : Nat := 118140960795 + 3871697 * 2 ^ 59
def prefixEnd_3871697 : Nat := 4983230072969 + 3 ^ 40 * 3871697 * 2
def baseEnd_3871697 : Nat := 441787002126809711418199

theorem tailTrace_3871697 : CollatzResearch.WordTrace tailWord_3871697 prefixEnd_3871697 441787002126809711418199 := by
  unfold tailWord_3871697
  simp only [CollatzResearch.WordTrace]
  refine ⟨141212390654510477049245345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94141593769673651366163563 141212390654510477049245345)
  ·
    refine ⟨105909292990882857786934009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141212390654510477049245345 105909292990882857786934009)
    ·
      refine ⟨79431969743162143340200507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105909292990882857786934009 79431969743162143340200507)
      ·
        refine ⟨119147954614743215010300761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79431969743162143340200507 119147954614743215010300761)
        ·
          refine ⟨89360965961057411257725571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119147954614743215010300761 89360965961057411257725571)
          ·
            refine ⟨134041448941586116886588357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89360965961057411257725571 134041448941586116886588357)
            ·
              refine ⟨25132771676547396916235317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134041448941586116886588357 25132771676547396916235317)
              ·
                refine ⟨2356197344676318460897061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25132771676547396916235317 2356197344676318460897061)
                ·
                  refine ⟨441787002126809711418199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2356197344676318460897061 441787002126809711418199)
                  ·
                    rfl

theorem cell22_3871697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 4].length) (baseStart_3871697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871697 prefixEnd_3871697 := by exact prefixLift 3871697
  have htrace : WordTrace (prefixWord ++ tailWord_3871697) baseStart_3871697 baseEnd_3871697 := by
    simpa [prefixWord, tailWord_3871697, baseEnd_3871697] using wordTrace_append hprefix tailTrace_3871697
  have hstable : (prefixWord ++ tailWord_3871697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871697).length < 2 ^ (prefixWord ++ tailWord_3871697).sum := by decide
  have hdescent : baseEnd_3871697 < baseStart_3871697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871729 : List Nat := [1, 2, 2, 2, 4, 1, 2, 3, 2, 3]
def baseStart_3871729 : Nat := 118140960795 + 3871729 * 2 ^ 59
def prefixEnd_3871729 : Nat := 4983230072969 + 3 ^ 40 * 3871729 * 2
def baseEnd_3871729 : Nat := 1325371960634391717454499

theorem tailTrace_3871729 : CollatzResearch.WordTrace tailWord_3871729 prefixEnd_3871729 1325371960634391717454499 := by
  unfold tailWord_3871729
  simp only [CollatzResearch.WordTrace]
  refine ⟨141213557790394546514410241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94142371860263031009606827 141213557790394546514410241)
  ·
    refine ⟨105910168342795909885807681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141213557790394546514410241 105910168342795909885807681)
    ·
      refine ⟨79432626257096932414355761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105910168342795909885807681 79432626257096932414355761)
      ·
        refine ⟨59574469692822699310766821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79432626257096932414355761 59574469692822699310766821)
        ·
          refine ⟨11170213067404256120768779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59574469692822699310766821 11170213067404256120768779)
          ·
            refine ⟨16755319601106384181153169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11170213067404256120768779 16755319601106384181153169)
            ·
              refine ⟨12566489700829788135864877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16755319601106384181153169 12566489700829788135864877)
              ·
                refine ⟨4712433637811170550949329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12566489700829788135864877 4712433637811170550949329)
                ·
                  refine ⟨3534325228358377913211997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4712433637811170550949329 3534325228358377913211997)
                  ·
                    refine ⟨1325371960634391717454499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3534325228358377913211997 1325371960634391717454499)
                    ·
                      rfl

theorem cell22_3871729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_3871729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871729 prefixEnd_3871729 := by exact prefixLift 3871729
  have htrace : WordTrace (prefixWord ++ tailWord_3871729) baseStart_3871729 baseEnd_3871729 := by
    simpa [prefixWord, tailWord_3871729, baseEnd_3871729] using wordTrace_append hprefix tailTrace_3871729
  have hstable : (prefixWord ++ tailWord_3871729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871729).length < 2 ^ (prefixWord ++ tailWord_3871729).sum := by decide
  have hdescent : baseEnd_3871729 < baseStart_3871729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871838 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3871838 : Nat := 118140960795 + 3871838 * 2 ^ 59
def prefixEnd_3871838 : Nat := 4983230072969 + 3 ^ 40 * 3871838 * 2
def baseEnd_3871838 : Nat := 441803091187317255493055

theorem tailTrace_3871838 : CollatzResearch.WordTrace tailWord_3871838 prefixEnd_3871838 441803091187317255493055 := by
  unfold tailWord_3871838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17652191668374957266266021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94145022231333105420085445 17652191668374957266266021)
  ·
    refine ⟨3309785937820304487424879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17652191668374957266266021 3309785937820304487424879)
    ·
      refine ⟨4964678906730456731137319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3309785937820304487424879 4964678906730456731137319)
      ·
        refine ⟨7447018360095685096705979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4964678906730456731137319 7447018360095685096705979)
        ·
          refine ⟨11170527540143527645058969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447018360095685096705979 11170527540143527645058969)
          ·
            refine ⟨8377895655107645733794227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11170527540143527645058969 8377895655107645733794227)
            ·
              refine ⟨12566843482661468600691341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377895655107645733794227 12566843482661468600691341)
              ·
                refine ⟨4712566305998050725259253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12566843482661468600691341 4712566305998050725259253)
                ·
                  refine ⟨441803091187317255493055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4712566305998050725259253 441803091187317255493055)
                  ·
                    rfl

theorem cell22_3871838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3871838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871838 prefixEnd_3871838 := by exact prefixLift 3871838
  have htrace : WordTrace (prefixWord ++ tailWord_3871838) baseStart_3871838 baseEnd_3871838 := by
    simpa [prefixWord, tailWord_3871838, baseEnd_3871838] using wordTrace_append hprefix tailTrace_3871838
  have hstable : (prefixWord ++ tailWord_3871838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871838).length < 2 ^ (prefixWord ++ tailWord_3871838).sum := by decide
  have hdescent : baseEnd_3871838 < baseStart_3871838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871877 : List Nat := [1, 3, 1, 1, 6, 10]
def baseStart_3871877 : Nat := 118140960795 + 3871877 * 2 ^ 59
def prefixEnd_3871877 : Nat := 4983230072969 + 3 ^ 40 * 3871877 * 2
def baseEnd_3871877 : Nat := 16363242272332946478445

theorem tailTrace_3871877 : CollatzResearch.WordTrace tailWord_3871877 prefixEnd_3871877 16363242272332946478445 := by
  unfold tailWord_3871877
  simp only [CollatzResearch.WordTrace]
  refine ⟨141218955793858367790797885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94145970529238911860531923 141218955793858367790797885)
  ·
    refine ⟨52957108422696887921549207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141218955793858367790797885 52957108422696887921549207)
    ·
      refine ⟨79435662634045331882323811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52957108422696887921549207 79435662634045331882323811)
      ·
        refine ⟨119153493951067997823485717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79435662634045331882323811 119153493951067997823485717)
        ·
          refine ⟨5585320028956312397975893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119153493951067997823485717 5585320028956312397975893)
          ·
            refine ⟨16363242272332946478445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5585320028956312397975893 16363242272332946478445)
            ·
              rfl

theorem cell22_3871877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 10].length) (baseStart_3871877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871877 prefixEnd_3871877 := by exact prefixLift 3871877
  have htrace : WordTrace (prefixWord ++ tailWord_3871877) baseStart_3871877 baseEnd_3871877 := by
    simpa [prefixWord, tailWord_3871877, baseEnd_3871877] using wordTrace_append hprefix tailTrace_3871877
  have hstable : (prefixWord ++ tailWord_3871877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871877).length < 2 ^ (prefixWord ++ tailWord_3871877).sum := by decide
  have hdescent : baseEnd_3871877 < baseStart_3871877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871881 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 2, 3]
def baseStart_3871881 : Nat := 118140960795 + 3871881 * 2 ^ 59
def prefixEnd_3871881 : Nat := 4983230072969 + 3 ^ 40 * 3871881 * 2
def baseEnd_3871881 : Nat := 1325423993340713987654033

theorem tailTrace_3871881 : CollatzResearch.WordTrace tailWord_3871881 prefixEnd_3871881 1325423993340713987654033 := by
  unfold tailWord_3871881
  simp only [CollatzResearch.WordTrace]
  refine ⟨141219101685843876473943497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94146067790562584315962331 141219101685843876473943497)
  ·
    refine ⟨105914326264382907355457623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141219101685843876473943497 105914326264382907355457623)
    ·
      refine ⟨158871489396574361033186435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105914326264382907355457623 158871489396574361033186435)
      ·
        refine ⟨238307234094861541549779653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158871489396574361033186435 238307234094861541549779653)
        ·
          refine ⟨44682606392786539040583685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238307234094861541549779653 44682606392786539040583685)
          ·
            refine ⟨8377988698647476070109441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44682606392786539040583685 8377988698647476070109441)
            ·
              refine ⟨6283491523985607052582081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8377988698647476070109441 6283491523985607052582081)
              ·
                refine ⟨4712618642989205289436561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6283491523985607052582081 4712618642989205289436561)
                ·
                  refine ⟨3534463982241903967077421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4712618642989205289436561 3534463982241903967077421)
                  ·
                    refine ⟨1325423993340713987654033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3534463982241903967077421 1325423993340713987654033)
                    ·
                      rfl

theorem cell22_3871881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_3871881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871881 prefixEnd_3871881 := by exact prefixLift 3871881
  have htrace : WordTrace (prefixWord ++ tailWord_3871881) baseStart_3871881 baseEnd_3871881 := by
    simpa [prefixWord, tailWord_3871881, baseEnd_3871881] using wordTrace_append hprefix tailTrace_3871881
  have hstable : (prefixWord ++ tailWord_3871881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871881).length < 2 ^ (prefixWord ++ tailWord_3871881).sum := by decide
  have hdescent : baseEnd_3871881 < baseStart_3871881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871909 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_3871909 : Nat := 118140960795 + 3871909 * 2 ^ 59
def prefixEnd_3871909 : Nat := 4983230072969 + 3 ^ 40 * 3871909 * 2
def baseEnd_3871909 : Nat := 1325433578312931247953947

theorem tailTrace_3871909 : CollatzResearch.WordTrace tailWord_3871909 prefixEnd_3871909 1325433578312931247953947 := by
  unfold tailWord_3871909
  simp only [CollatzResearch.WordTrace]
  refine ⟨141220122929742437255962781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94146748619828291503975187 141220122929742437255962781)
  ·
    refine ⟨52957546098653413970986043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141220122929742437255962781 52957546098653413970986043)
    ·
      refine ⟨79436319147980120956479065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52957546098653413970986043 79436319147980120956479065)
      ·
        refine ⟨59577239360985090717359299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79436319147980120956479065 59577239360985090717359299)
        ·
          refine ⟨89365859041477636076038949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59577239360985090717359299 89365859041477636076038949)
          ·
            refine ⟨16756098570277056764257303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89365859041477636076038949 16756098570277056764257303)
            ·
              refine ⟨25134147855415585146385955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16756098570277056764257303 25134147855415585146385955)
              ·
                refine ⟨37701221783123377719578933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25134147855415585146385955 37701221783123377719578933)
                ·
                  refine ⟨3534489542167816661210525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37701221783123377719578933 3534489542167816661210525)
                  ·
                    refine ⟨1325433578312931247953947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3534489542167816661210525 1325433578312931247953947)
                    ·
                      rfl

theorem cell22_3871909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_3871909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871909 prefixEnd_3871909 := by exact prefixLift 3871909
  have htrace : WordTrace (prefixWord ++ tailWord_3871909) baseStart_3871909 baseEnd_3871909 := by
    simpa [prefixWord, tailWord_3871909, baseEnd_3871909] using wordTrace_append hprefix tailTrace_3871909
  have hstable : (prefixWord ++ tailWord_3871909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871909).length < 2 ^ (prefixWord ++ tailWord_3871909).sum := by decide
  have hdescent : baseEnd_3871909 < baseStart_3871909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871911 : List Nat := [1, 1, 6, 2, 1, 2, 3, 6]
def baseStart_3871911 : Nat := 118140960795 + 3871911 * 2 ^ 59
def prefixEnd_3871911 : Nat := 4983230072969 + 3 ^ 40 * 3871911 * 2
def baseEnd_3871911 : Nat := 147270473661533767711549

theorem tailTrace_3871911 : CollatzResearch.WordTrace tailWord_3871911 prefixEnd_3871911 147270473661533767711549 := by
  unfold tailWord_3871911
  simp only [CollatzResearch.WordTrace]
  refine ⟨141220195875735191597535587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94146797250490127731690391 141220195875735191597535587)
  ·
    refine ⟨211830293813602787396303381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141220195875735191597535587 211830293813602787396303381)
    ·
      refine ⟨9929545022512630659201721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211830293813602787396303381 9929545022512630659201721)
      ·
        refine ⟨7447158766884472994401291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9929545022512630659201721 7447158766884472994401291)
        ·
          refine ⟨11170738150326709491601937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447158766884472994401291 11170738150326709491601937)
          ·
            refine ⟨8378053612745032118701453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11170738150326709491601937 8378053612745032118701453)
            ·
              refine ⟨3141770104779387044513045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8378053612745032118701453 3141770104779387044513045)
              ·
                refine ⟨147270473661533767711549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3141770104779387044513045 147270473661533767711549)
                ·
                  rfl

theorem cell22_3871911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 6].length) (baseStart_3871911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871911 prefixEnd_3871911 := by exact prefixLift 3871911
  have htrace : WordTrace (prefixWord ++ tailWord_3871911) baseStart_3871911 baseEnd_3871911 := by
    simpa [prefixWord, tailWord_3871911, baseEnd_3871911] using wordTrace_append hprefix tailTrace_3871911
  have hstable : (prefixWord ++ tailWord_3871911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871911).length < 2 ^ (prefixWord ++ tailWord_3871911).sum := by decide
  have hdescent : baseEnd_3871911 < baseStart_3871911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3871954 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3871954 : Nat := 118140960795 + 3871954 * 2 ^ 59
def prefixEnd_3871954 : Nat := 4983230072969 + 3 ^ 40 * 3871954 * 2
def baseEnd_3871954 : Nat := 1325448982732566130578809

theorem tailTrace_3871954 : CollatzResearch.WordTrace tailWord_3871954 prefixEnd_3871954 1325448982732566130578809 := by
  unfold tailWord_3871954
  simp only [CollatzResearch.WordTrace]
  refine ⟨35305441053644852485337729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94147842809719606627567277 35305441053644852485337729)
  ·
    refine ⟨26479080790233639364003297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35305441053644852485337729 26479080790233639364003297)
    ·
      refine ⟨19859310592675229523002473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26479080790233639364003297 19859310592675229523002473)
      ·
        refine ⟨14894482944506422142251855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19859310592675229523002473 14894482944506422142251855)
        ·
          refine ⟨22341724416759633213377783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14894482944506422142251855 22341724416759633213377783)
          ·
            refine ⟨33512586625139449820066675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22341724416759633213377783 33512586625139449820066675)
            ·
              refine ⟨50268879937709174730100013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33512586625139449820066675 50268879937709174730100013)
              ·
                refine ⟨18850829976640940523787505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50268879937709174730100013 18850829976640940523787505)
                ·
                  refine ⟨14138122482480705392840629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18850829976640940523787505 14138122482480705392840629)
                  ·
                    refine ⟨1325448982732566130578809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14138122482480705392840629 1325448982732566130578809)
                    ·
                      rfl

theorem cell22_3871954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3871954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3871954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3871954 prefixEnd_3871954 := by exact prefixLift 3871954
  have htrace : WordTrace (prefixWord ++ tailWord_3871954) baseStart_3871954 baseEnd_3871954 := by
    simpa [prefixWord, tailWord_3871954, baseEnd_3871954] using wordTrace_append hprefix tailTrace_3871954
  have hstable : (prefixWord ++ tailWord_3871954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3871954).length < 2 ^ (prefixWord ++ tailWord_3871954).sum := by decide
  have hdescent : baseEnd_3871954 < baseStart_3871954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3871954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872001 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 6]
def baseStart_3872001 : Nat := 118140960795 + 3872001 * 2 ^ 59
def prefixEnd_3872001 : Nat := 4983230072969 + 3 ^ 40 * 3872001 * 2
def baseEnd_3872001 : Nat := 441821690597691224884555

theorem tailTrace_3872001 : CollatzResearch.WordTrace tailWord_3872001 prefixEnd_3872001 441821690597691224884555 := by
  unfold tailWord_3872001
  simp only [CollatzResearch.WordTrace]
  refine ⟨141223478445409136968311857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94148985630272757978874571 141223478445409136968311857)
  ·
    refine ⟨105917608834056852726233893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141223478445409136968311857 105917608834056852726233893)
    ·
      refine ⟨19859551656385659886168855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105917608834056852726233893 19859551656385659886168855)
      ·
        refine ⟨29789327484578489829253283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19859551656385659886168855 29789327484578489829253283)
        ·
          refine ⟨44683991226867734743879925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29789327484578489829253283 44683991226867734743879925)
          ·
            refine ⟨4189124177518850132238743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44683991226867734743879925 4189124177518850132238743)
            ·
              refine ⟨6283686266278275198358115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189124177518850132238743 6283686266278275198358115)
              ·
                refine ⟨9425529399417412797537173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283686266278275198358115 9425529399417412797537173)
                ·
                  refine ⟨441821690597691224884555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9425529399417412797537173 441821690597691224884555)
                  ·
                    rfl

theorem cell22_3872001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_3872001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872001 prefixEnd_3872001 := by exact prefixLift 3872001
  have htrace : WordTrace (prefixWord ++ tailWord_3872001) baseStart_3872001 baseEnd_3872001 := by
    simpa [prefixWord, tailWord_3872001, baseEnd_3872001] using wordTrace_append hprefix tailTrace_3872001
  have hstable : (prefixWord ++ tailWord_3872001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872001).length < 2 ^ (prefixWord ++ tailWord_3872001).sum := by decide
  have hdescent : baseEnd_3872001 < baseStart_3872001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872108 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 5]
def baseStart_3872108 : Nat := 118140960795 + 3872108 * 2 ^ 59
def prefixEnd_3872108 : Nat := 4983230072969 + 3 ^ 40 * 3872108 * 2
def baseEnd_3872108 : Nat := 441833900026587020742779

theorem tailTrace_3872108 : CollatzResearch.WordTrace tailWord_3872108 prefixEnd_3872108 441833900026587020742779 := by
  unfold tailWord_3872108
  simp only [CollatzResearch.WordTrace]
  refine ⟨70613690528010747121228489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94151587370680996161637985 70613690528010747121228489)
  ·
    refine ⟨52960267896008060340921367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70613690528010747121228489 52960267896008060340921367)
    ·
      refine ⟨79440401844012090511382051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52960267896008060340921367 79440401844012090511382051)
      ·
        refine ⟨119160602766018135767073077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79440401844012090511382051 119160602766018135767073077)
        ·
          refine ⟨11171306509314200228163101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119160602766018135767073077 11171306509314200228163101)
          ·
            refine ⟨4189239940992825085561163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11171306509314200228163101 4189239940992825085561163)
            ·
              refine ⟨6283859911489237628341745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189239940992825085561163 6283859911489237628341745)
              ·
                refine ⟨4712894933616928221256309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6283859911489237628341745 4712894933616928221256309)
                ·
                  refine ⟨441833900026587020742779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4712894933616928221256309 441833900026587020742779)
                  ·
                    rfl

theorem cell22_3872108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_3872108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872108 prefixEnd_3872108 := by exact prefixLift 3872108
  have htrace : WordTrace (prefixWord ++ tailWord_3872108) baseStart_3872108 baseEnd_3872108 := by
    simpa [prefixWord, tailWord_3872108, baseEnd_3872108] using wordTrace_append hprefix tailTrace_3872108
  have hstable : (prefixWord ++ tailWord_3872108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872108).length < 2 ^ (prefixWord ++ tailWord_3872108).sum := by decide
  have hdescent : baseEnd_3872108 < baseStart_3872108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872136 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 6]
def baseStart_3872136 : Nat := 118140960795 + 3872136 * 2 ^ 59
def prefixEnd_3872136 : Nat := 4983230072969 + 3 ^ 40 * 3872136 * 2
def baseEnd_3872136 : Nat := 441837095017326107509417

theorem tailTrace_3872136 : CollatzResearch.WordTrace tailWord_3872136 prefixEnd_3872136 441837095017326107509417 := by
  unfold tailWord_3872136
  simp only [CollatzResearch.WordTrace]
  refine ⟨70614201149960027512238131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94152268199946703349650841 70614201149960027512238131)
  ·
    refine ⟨105921301724940041268357197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70614201149960027512238131 105921301724940041268357197)
    ·
      refine ⟨39720488146852515475633949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105921301724940041268357197 39720488146852515475633949)
      ·
        refine ⟨14895183055069693303362731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39720488146852515475633949 14895183055069693303362731)
        ·
          refine ⟨22342774582604539955044097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14895183055069693303362731 22342774582604539955044097)
          ·
            refine ⟨16757080936953404966283073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22342774582604539955044097 16757080936953404966283073)
            ·
              refine ⟨12567810702715053724712305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16757080936953404966283073 12567810702715053724712305)
              ·
                refine ⟨9425858027036290293534229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12567810702715053724712305 9425858027036290293534229)
                ·
                  refine ⟨441837095017326107509417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9425858027036290293534229 441837095017326107509417)
                  ·
                    rfl

theorem cell22_3872136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_3872136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872136 prefixEnd_3872136 := by exact prefixLift 3872136
  have htrace : WordTrace (prefixWord ++ tailWord_3872136) baseStart_3872136 baseEnd_3872136 := by
    simpa [prefixWord, tailWord_3872136, baseEnd_3872136] using wordTrace_append hprefix tailTrace_3872136
  have hstable : (prefixWord ++ tailWord_3872136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872136).length < 2 ^ (prefixWord ++ tailWord_3872136).sum := by decide
  have hdescent : baseEnd_3872136 < baseStart_3872136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872146 : List Nat := [3, 2, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3872146 : Nat := 118140960795 + 3872146 * 2 ^ 59
def prefixEnd_3872146 : Nat := 4983230072969 + 3 ^ 40 * 3872146 * 2
def baseEnd_3872146 : Nat := 1325514708256341629778221

theorem tailTrace_3872146 : CollatzResearch.WordTrace tailWord_3872146 prefixEnd_3872146 1325514708256341629778221 := by
  unfold tailWord_3872146
  simp only [CollatzResearch.WordTrace]
  refine ⟨35307191757470956683085073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94152511353255884488226861 35307191757470956683085073)
  ·
    refine ⟨26480393818103217512313805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35307191757470956683085073 26480393818103217512313805)
    ·
      refine ⟨9930147681788706567117677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26480393818103217512313805 9930147681788706567117677)
      ·
        refine ⟨3723805380670764962669129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9930147681788706567117677 3723805380670764962669129)
        ·
          refine ⟨2792854035503073722001847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3723805380670764962669129 2792854035503073722001847)
          ·
            refine ⟨4189281053254610583002771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2792854035503073722001847 4189281053254610583002771)
            ·
              refine ⟨6283921579881915874504157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189281053254610583002771 6283921579881915874504157)
              ·
                refine ⟨2356470592455718452939059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6283921579881915874504157 2356470592455718452939059)
                ·
                  refine ⟨3534705888683577679408589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356470592455718452939059 3534705888683577679408589)
                  ·
                    refine ⟨1325514708256341629778221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3534705888683577679408589 1325514708256341629778221)
                    ·
                      rfl

theorem cell22_3872146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3872146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872146 prefixEnd_3872146 := by exact prefixLift 3872146
  have htrace : WordTrace (prefixWord ++ tailWord_3872146) baseStart_3872146 baseEnd_3872146 := by
    simpa [prefixWord, tailWord_3872146, baseEnd_3872146] using wordTrace_append hprefix tailTrace_3872146
  have hstable : (prefixWord ++ tailWord_3872146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872146).length < 2 ^ (prefixWord ++ tailWord_3872146).sum := by decide
  have hdescent : baseEnd_3872146 < baseStart_3872146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872153 : List Nat := [1, 2, 1, 2, 1, 5, 3, 3, 4]
def baseStart_3872153 : Nat := 118140960795 + 3872153 * 2 ^ 59
def prefixEnd_3872153 : Nat := 4983230072969 + 3 ^ 40 * 3872153 * 2
def baseEnd_3872153 : Nat := 441839034833131981617733

theorem tailTrace_3872153 : CollatzResearch.WordTrace tailWord_3872153 prefixEnd_3872153 441839034833131981617733 := by
  unfold tailWord_3872153
  simp only [CollatzResearch.WordTrace]
  refine ⟨141229022340858466927845113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94152681560572311285230075 141229022340858466927845113)
  ·
    refine ⟨105921766755643850195883835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141229022340858466927845113 105921766755643850195883835)
    ·
      refine ⟨158882650133465775293825753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105921766755643850195883835 158882650133465775293825753)
      ·
        refine ⟨119161987600099331470369315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158882650133465775293825753 119161987600099331470369315)
        ·
          refine ⟨178742981400148997205553973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119161987600099331470369315 178742981400148997205553973)
          ·
            refine ⟨16757154506263968488020685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178742981400148997205553973 16757154506263968488020685)
            ·
              refine ⟨6283932939848988183007757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16757154506263968488020685 6283932939848988183007757)
              ·
                refine ⟨2356474852443370568627909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6283932939848988183007757 2356474852443370568627909)
                ·
                  refine ⟨441839034833131981617733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2356474852443370568627909 441839034833131981617733)
                  ·
                    rfl

theorem cell22_3872153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 4].length) (baseStart_3872153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872153 prefixEnd_3872153 := by exact prefixLift 3872153
  have htrace : WordTrace (prefixWord ++ tailWord_3872153) baseStart_3872153 baseEnd_3872153 := by
    simpa [prefixWord, tailWord_3872153, baseEnd_3872153] using wordTrace_append hprefix tailTrace_3872153
  have hstable : (prefixWord ++ tailWord_3872153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872153).length < 2 ^ (prefixWord ++ tailWord_3872153).sum := by decide
  have hdescent : baseEnd_3872153 < baseStart_3872153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872181 : List Nat := [1, 3, 3, 2, 2, 1, 1, 9]
def baseStart_3872181 : Nat := 118140960795 + 3872181 * 2 ^ 59
def prefixEnd_3872181 : Nat := 4983230072969 + 3 ^ 40 * 3872181 * 2
def baseEnd_3872181 : Nat := 147280743274623689461457

theorem tailTrace_3872181 : CollatzResearch.WordTrace tailWord_3872181 prefixEnd_3872181 147280743274623689461457 := by
  unfold tailWord_3872181
  simp only [CollatzResearch.WordTrace]
  refine ⟨141230043584757027709864397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94153362389838018473242931 141230043584757027709864397)
  ·
    refine ⟨52961266344283885391199149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141230043584757027709864397 52961266344283885391199149)
    ·
      refine ⟨19860474879106457021699681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52961266344283885391199149 19860474879106457021699681)
      ·
        refine ⟨14895356159329842766274761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19860474879106457021699681 14895356159329842766274761)
        ·
          refine ⟨11171517119497382074706071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14895356159329842766274761 11171517119497382074706071)
          ·
            refine ⟨16757275679246073112059107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11171517119497382074706071 16757275679246073112059107)
            ·
              refine ⟨25135913518869109668088661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16757275679246073112059107 25135913518869109668088661)
              ·
                refine ⟨147280743274623689461457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25135913518869109668088661 147280743274623689461457)
                ·
                  rfl

theorem cell22_3872181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 9].length) (baseStart_3872181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872181 prefixEnd_3872181 := by exact prefixLift 3872181
  have htrace : WordTrace (prefixWord ++ tailWord_3872181) baseStart_3872181 baseEnd_3872181 := by
    simpa [prefixWord, tailWord_3872181, baseEnd_3872181] using wordTrace_append hprefix tailTrace_3872181
  have hstable : (prefixWord ++ tailWord_3872181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872181).length < 2 ^ (prefixWord ++ tailWord_3872181).sum := by decide
  have hdescent : baseEnd_3872181 < baseStart_3872181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872185 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 2, 3]
def baseStart_3872185 : Nat := 118140960795 + 3872185 * 2 ^ 59
def prefixEnd_3872185 : Nat := 4983230072969 + 3 ^ 40 * 3872185 * 2
def baseEnd_3872185 : Nat := 1325528058753358528053101

theorem tailTrace_3872185 : CollatzResearch.WordTrace tailWord_3872185 prefixEnd_3872185 1325528058753358528053101 := by
  unfold tailWord_3872185
  simp only [CollatzResearch.WordTrace]
  refine ⟨141230189476742536393010009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94153459651161690928673339 141230189476742536393010009)
  ·
    refine ⟨105922642107556902294757507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141230189476742536393010009 105922642107556902294757507)
    ·
      refine ⟨158883963161335353442136261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105922642107556902294757507 158883963161335353442136261)
      ·
        refine ⟨29790743092750378770400549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158883963161335353442136261 29790743092750378770400549)
        ·
          refine ⟨5585764329890696019450103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29790743092750378770400549 5585764329890696019450103)
          ·
            refine ⟨8378646494836044029175155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5585764329890696019450103 8378646494836044029175155)
            ·
              refine ⟨12567969742254066043762733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378646494836044029175155 12567969742254066043762733)
              ·
                refine ⟨4712988653345274766411025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12567969742254066043762733 4712988653345274766411025)
                ·
                  refine ⟨3534741490008956074808269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4712988653345274766411025 3534741490008956074808269)
                  ·
                    refine ⟨1325528058753358528053101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3534741490008956074808269 1325528058753358528053101)
                    ·
                      rfl

theorem cell22_3872185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_3872185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872185 prefixEnd_3872185 := by exact prefixLift 3872185
  have htrace : WordTrace (prefixWord ++ tailWord_3872185) baseStart_3872185 baseEnd_3872185 := by
    simpa [prefixWord, tailWord_3872185, baseEnd_3872185] using wordTrace_append hprefix tailTrace_3872185
  have hstable : (prefixWord ++ tailWord_3872185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872185).length < 2 ^ (prefixWord ++ tailWord_3872185).sum := by decide
  have hdescent : baseEnd_3872185 < baseStart_3872185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872241 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_3872241 : Nat := 118140960795 + 3872241 * 2 ^ 59
def prefixEnd_3872241 : Nat := 4983230072969 + 3 ^ 40 * 3872241 * 2
def baseEnd_3872241 : Nat := 1325547228697793048652929

theorem tailTrace_3872241 : CollatzResearch.WordTrace tailWord_3872241 prefixEnd_3872241 1325547228697793048652929 := by
  unfold tailWord_3872241
  simp only [CollatzResearch.WordTrace]
  refine ⟨141232231964539657957048577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94154821309693105304699051 141232231964539657957048577)
  ·
    refine ⟨105924173973404743467786433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141232231964539657957048577 105924173973404743467786433)
    ·
      refine ⟨79443130480053557600839825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105924173973404743467786433 79443130480053557600839825)
      ·
        refine ⟨59582347860040168200629869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79443130480053557600839825 59582347860040168200629869)
        ·
          refine ⟨22343380447515063075236201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59582347860040168200629869 22343380447515063075236201)
          ·
            refine ⟨16757535335636297306427151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22343380447515063075236201 16757535335636297306427151)
            ·
              refine ⟨25136303003454445959640727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16757535335636297306427151 25136303003454445959640727)
              ·
                refine ⟨37704454505181668939461091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25136303003454445959640727 37704454505181668939461091)
                ·
                  refine ⟨56556681757772503409191637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37704454505181668939461091 56556681757772503409191637)
                  ·
                    refine ⟨1325547228697793048652929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56556681757772503409191637 1325547228697793048652929)
                    ·
                      rfl

theorem cell22_3872241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_3872241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872241 prefixEnd_3872241 := by exact prefixLift 3872241
  have htrace : WordTrace (prefixWord ++ tailWord_3872241) baseStart_3872241 baseEnd_3872241 := by
    simpa [prefixWord, tailWord_3872241, baseEnd_3872241] using wordTrace_append hprefix tailTrace_3872241
  have hstable : (prefixWord ++ tailWord_3872241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872241).length < 2 ^ (prefixWord ++ tailWord_3872241).sum := by decide
  have hdescent : baseEnd_3872241 < baseStart_3872241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872273 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_3872273 : Nat := 118140960795 + 3872273 * 2 ^ 59
def prefixEnd_3872273 : Nat := 4983230072969 + 3 ^ 40 * 3872273 * 2
def baseEnd_3872273 : Nat := 1325558182951755631852831

theorem tailTrace_3872273 : CollatzResearch.WordTrace tailWord_3872273 prefixEnd_3872273 1325558182951755631852831 := by
  unfold tailWord_3872273
  simp only [CollatzResearch.WordTrace]
  refine ⟨141233399100423727422213473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94155599400282484948142315 141233399100423727422213473)
  ·
    refine ⟨105925049325317795566660105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141233399100423727422213473 105925049325317795566660105)
    ·
      refine ⟨79443786993988346674995079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105925049325317795566660105 79443786993988346674995079)
      ·
        refine ⟨119165680490982520012492619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79443786993988346674995079 119165680490982520012492619)
        ·
          refine ⟨178748520736473780018738929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119165680490982520012492619 178748520736473780018738929)
          ·
            refine ⟨134061390552355335014054197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178748520736473780018738929 134061390552355335014054197)
            ·
              refine ⟨12568255364283312657567581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134061390552355335014054197 12568255364283312657567581)
              ·
                refine ⟨4713095761606242246587843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12568255364283312657567581 4713095761606242246587843)
                ·
                  refine ⟨7069643642409363369881765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713095761606242246587843 7069643642409363369881765)
                  ·
                    refine ⟨1325558182951755631852831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7069643642409363369881765 1325558182951755631852831)
                    ·
                      rfl

theorem cell22_3872273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_3872273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872273 prefixEnd_3872273 := by exact prefixLift 3872273
  have htrace : WordTrace (prefixWord ++ tailWord_3872273) baseStart_3872273 baseEnd_3872273 := by
    simpa [prefixWord, tailWord_3872273, baseEnd_3872273] using wordTrace_append hprefix tailTrace_3872273
  have hstable : (prefixWord ++ tailWord_3872273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872273).length < 2 ^ (prefixWord ++ tailWord_3872273).sum := by decide
  have hdescent : baseEnd_3872273 < baseStart_3872273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872288 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 6]
def baseStart_3872288 : Nat := 118140960795 + 3872288 * 2 ^ 59
def prefixEnd_3872288 : Nat := 4983230072969 + 3 ^ 40 * 3872288 * 2
def baseEnd_3872288 : Nat := 441854439252766864242595

theorem tailTrace_3872288 : CollatzResearch.WordTrace tailWord_3872288 prefixEnd_3872288 441854439252766864242595 := by
  unfold tailWord_3872288
  simp only [CollatzResearch.WordTrace]
  refine ⟨70616973097684692492004759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94155964130246256656006345 70616973097684692492004759)
  ·
    refine ⟨105925459646527038738007139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70616973097684692492004759 105925459646527038738007139)
    ·
      refine ⟨158888189469790558107010709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105925459646527038738007139 158888189469790558107010709)
      ·
        refine ⟨7447883881396432411266127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158888189469790558107010709 7447883881396432411266127)
        ·
          refine ⟨11171825822094648616899191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447883881396432411266127 11171825822094648616899191)
          ·
            refine ⟨16757738733141972925348787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11171825822094648616899191 16757738733141972925348787)
            ·
              refine ⟨25136608099712959388023181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16757738733141972925348787 25136608099712959388023181)
              ·
                refine ⟨9426228037392359770508693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25136608099712959388023181 9426228037392359770508693)
                ·
                  refine ⟨441854439252766864242595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9426228037392359770508693 441854439252766864242595)
                  ·
                    rfl

theorem cell22_3872288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_3872288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872288 prefixEnd_3872288 := by exact prefixLift 3872288
  have htrace : WordTrace (prefixWord ++ tailWord_3872288) baseStart_3872288 baseEnd_3872288 := by
    simpa [prefixWord, tailWord_3872288, baseEnd_3872288] using wordTrace_append hprefix tailTrace_3872288
  have hstable : (prefixWord ++ tailWord_3872288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872288).length < 2 ^ (prefixWord ++ tailWord_3872288).sum := by decide
  have hdescent : baseEnd_3872288 < baseStart_3872288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872442 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 1, 4]
def baseStart_3872442 : Nat := 118140960795 + 3872442 * 2 ^ 59
def prefixEnd_3872442 : Nat := 4983230072969 + 3 ^ 40 * 3872442 * 2
def baseEnd_3872442 : Nat := 1325616035105495524377313

theorem tailTrace_3872442 : CollatzResearch.WordTrace tailWord_3872442 prefixEnd_3872442 1325616035105495524377313 := by
  unfold tailWord_3872442
  simp only [CollatzResearch.WordTrace]
  refine ⟨35309890759202867321278895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94159708691207646190077053 35309890759202867321278895)
  ·
    refine ⟨52964836138804300981918343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35309890759202867321278895 52964836138804300981918343)
    ·
      refine ⟨79447254208206451472877515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52964836138804300981918343 79447254208206451472877515)
      ·
        refine ⟨119170881312309677209316273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79447254208206451472877515 119170881312309677209316273)
        ·
          refine ⟨89378160984232257906987205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119170881312309677209316273 89378160984232257906987205)
          ·
            refine ⟨16758405184543548357560101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89378160984232257906987205 16758405184543548357560101)
            ·
              refine ⟨3142200972101915317042519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16758405184543548357560101 3142200972101915317042519)
              ·
                refine ⟨4713301458152872975563779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142200972101915317042519 4713301458152872975563779)
                ·
                  refine ⟨7069952187229309463345669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713301458152872975563779 7069952187229309463345669)
                  ·
                    refine ⟨1325616035105495524377313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7069952187229309463345669 1325616035105495524377313)
                    ·
                      rfl

theorem cell22_3872442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_3872442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872442 prefixEnd_3872442 := by exact prefixLift 3872442
  have htrace : WordTrace (prefixWord ++ tailWord_3872442) baseStart_3872442 baseEnd_3872442 := by
    simpa [prefixWord, tailWord_3872442, baseEnd_3872442] using wordTrace_append hprefix tailTrace_3872442
  have hstable : (prefixWord ++ tailWord_3872442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872442).length < 2 ^ (prefixWord ++ tailWord_3872442).sum := by decide
  have hdescent : baseEnd_3872442 < baseStart_3872442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872455 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 4, 3]
def baseStart_3872455 : Nat := 118140960795 + 3872455 * 2 ^ 59
def prefixEnd_3872455 : Nat := 4983230072969 + 3 ^ 40 * 3872455 * 2
def baseEnd_3872455 : Nat := 1325620485271167823802273

theorem tailTrace_3872455 : CollatzResearch.WordTrace tailWord_3872455 prefixEnd_3872455 1325620485271167823802273 := by
  unfold tailWord_3872455
  simp only [CollatzResearch.WordTrace]
  refine ⟨141240037185764372505338819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94160024790509581670225879 141240037185764372505338819)
  ·
    refine ⟨211860055778646558758008229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141240037185764372505338819 211860055778646558758008229)
    ·
      refine ⟨39723760458496229767126543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211860055778646558758008229 39723760458496229767126543)
      ·
        refine ⟨59585640687744344650689815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39723760458496229767126543 59585640687744344650689815)
        ·
          refine ⟨89378461031616516976034723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59585640687744344650689815 89378461031616516976034723)
          ·
            refine ⟨134067691547424775464052085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89378461031616516976034723 134067691547424775464052085)
            ·
              refine ⟨12568846082571072699754883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134067691547424775464052085 12568846082571072699754883)
              ·
                refine ⟨18853269123856609049632325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12568846082571072699754883 18853269123856609049632325)
                ·
                  refine ⟨3534987960723114196806061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18853269123856609049632325 3534987960723114196806061)
                  ·
                    refine ⟨1325620485271167823802273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3534987960723114196806061 1325620485271167823802273)
                    ·
                      rfl

theorem cell22_3872455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_3872455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872455 prefixEnd_3872455 := by exact prefixLift 3872455
  have htrace : WordTrace (prefixWord ++ tailWord_3872455) baseStart_3872455 baseEnd_3872455 := by
    simpa [prefixWord, tailWord_3872455, baseEnd_3872455] using wordTrace_append hprefix tailTrace_3872455
  have hstable : (prefixWord ++ tailWord_3872455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872455).length < 2 ^ (prefixWord ++ tailWord_3872455).sum := by decide
  have hdescent : baseEnd_3872455 < baseStart_3872455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872564 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 5]
def baseStart_3872564 : Nat := 118140960795 + 3872564 * 2 ^ 59
def prefixEnd_3872564 : Nat := 4983230072969 + 3 ^ 40 * 3872564 * 2
def baseEnd_3872564 : Nat := 441885932732909290942313

theorem tailTrace_3872564 : CollatzResearch.WordTrace tailWord_3872564 prefixEnd_3872564 441885932732909290942313 := by
  unfold tailWord_3872564
  simp only [CollatzResearch.WordTrace]
  refine ⟨70622006371184742060528373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94162675161579656080704497 70622006371184742060528373)
  ·
    refine ⟨6620813097298569568174535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70622006371184742060528373 6620813097298569568174535)
    ·
      refine ⟨9931219645947854352261803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6620813097298569568174535 9931219645947854352261803)
      ·
        refine ⟨14896829468921781528392705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9931219645947854352261803 14896829468921781528392705)
        ·
          refine ⟨11172622101691336146294529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14896829468921781528392705 11172622101691336146294529)
          ·
            refine ⟨8379466576268502109720897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11172622101691336146294529 8379466576268502109720897)
            ·
              refine ⟨6284599932201376582290673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8379466576268502109720897 6284599932201376582290673)
              ·
                refine ⟨4713449949151032436718005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6284599932201376582290673 4713449949151032436718005)
                ·
                  refine ⟨441885932732909290942313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4713449949151032436718005 441885932732909290942313)
                  ·
                    rfl

theorem cell22_3872564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_3872564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872564 prefixEnd_3872564 := by exact prefixLift 3872564
  have htrace : WordTrace (prefixWord ++ tailWord_3872564) baseStart_3872564 baseEnd_3872564 := by
    simpa [prefixWord, tailWord_3872564, baseEnd_3872564] using wordTrace_append hprefix tailTrace_3872564
  have hstable : (prefixWord ++ tailWord_3872564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872564).length < 2 ^ (prefixWord ++ tailWord_3872564).sum := by decide
  have hdescent : baseEnd_3872564 < baseStart_3872564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872611 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 1, 4]
def baseStart_3872611 : Nat := 118140960795 + 3872611 * 2 ^ 59
def prefixEnd_3872611 : Nat := 4983230072969 + 3 ^ 40 * 3872611 * 2
def baseEnd_3872611 : Nat := 1325673887259235416901795

theorem tailTrace_3872611 : CollatzResearch.WordTrace tailWord_3872611 prefixEnd_3872611 1325673887259235416901795 := by
  unfold tailWord_3872611
  simp only [CollatzResearch.WordTrace]
  refine ⟨141245726973199211148017687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94163817982132807432011791 141245726973199211148017687)
  ·
    refine ⟨211868590459798816722026531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141245726973199211148017687 211868590459798816722026531)
    ·
      refine ⟨317802885689698225083039797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211868590459798816722026531 317802885689698225083039797)
      ·
        refine ⟨29794020533409208601534981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317802885689698225083039797 29794020533409208601534981)
        ·
          refine ⟨5586378850014226612787809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29794020533409208601534981 5586378850014226612787809)
          ·
            refine ⟨4189784137510669959590857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5586378850014226612787809 4189784137510669959590857)
            ·
              refine ⟨3142338103133002469693143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4189784137510669959590857 3142338103133002469693143)
              ·
                refine ⟨4713507154699503704539715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142338103133002469693143 4713507154699503704539715)
                ·
                  refine ⟨7070260732049255556809573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713507154699503704539715 7070260732049255556809573)
                  ·
                    refine ⟨1325673887259235416901795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7070260732049255556809573 1325673887259235416901795)
                    ·
                      rfl

theorem cell22_3872611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 4].length) (baseStart_3872611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872611 prefixEnd_3872611 := by exact prefixLift 3872611
  have htrace : WordTrace (prefixWord ++ tailWord_3872611) baseStart_3872611 baseEnd_3872611 := by
    simpa [prefixWord, tailWord_3872611, baseEnd_3872611] using wordTrace_append hprefix tailTrace_3872611
  have hstable : (prefixWord ++ tailWord_3872611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872611).length < 2 ^ (prefixWord ++ tailWord_3872611).sum := by decide
  have hdescent : baseEnd_3872611 < baseStart_3872611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872620 : List Nat := [2, 2, 1, 1, 4, 3, 9]
def baseStart_3872620 : Nat := 118140960795 + 3872620 * 2 ^ 59
def prefixEnd_3872620 : Nat := 4983230072969 + 3 ^ 40 * 3872620 * 2
def baseEnd_3872620 : Nat := 49099146968265273830621

theorem tailTrace_3872620 : CollatzResearch.WordTrace tailWord_3872620 prefixEnd_3872620 49099146968265273830621 := by
  unfold tailWord_3872620
  simp only [CollatzResearch.WordTrace]
  refine ⟨70623027615083302842547657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94164036820111070456730209 70623027615083302842547657)
  ·
    refine ⟨52967270711312477131910743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70623027615083302842547657 52967270711312477131910743)
    ·
      refine ⟨79450906066968715697866115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52967270711312477131910743 79450906066968715697866115)
      ·
        refine ⟨119176359100453073546799173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79450906066968715697866115 119176359100453073546799173)
        ·
          refine ⟨22345567331334951290024845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119176359100453073546799173 22345567331334951290024845)
          ·
            refine ⟨8379587749250606733759317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22345567331334951290024845 8379587749250606733759317)
            ·
              refine ⟨49099146968265273830621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8379587749250606733759317 49099146968265273830621)
              ·
                rfl

theorem cell22_3872620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 9].length) (baseStart_3872620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872620 prefixEnd_3872620 := by exact prefixLift 3872620
  have htrace : WordTrace (prefixWord ++ tailWord_3872620) baseStart_3872620 baseEnd_3872620 := by
    simpa [prefixWord, tailWord_3872620, baseEnd_3872620] using wordTrace_append hprefix tailTrace_3872620
  have hstable : (prefixWord ++ tailWord_3872620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872620).length < 2 ^ (prefixWord ++ tailWord_3872620).sum := by decide
  have hdescent : baseEnd_3872620 < baseStart_3872620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872641 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 1, 5]
def baseStart_3872641 : Nat := 118140960795 + 3872641 * 2 ^ 59
def prefixEnd_3872641 : Nat := 4983230072969 + 3 ^ 40 * 3872641 * 2
def baseEnd_3872641 : Nat := 1325684156872325338651703

theorem tailTrace_3872641 : CollatzResearch.WordTrace tailWord_3872641 prefixEnd_3872641 1325684156872325338651703 := by
  unfold tailWord_3872641
  simp only [CollatzResearch.WordTrace]
  refine ⟨141246821163090526271609777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94164547442060350847739851 141246821163090526271609777)
  ·
    refine ⟨105935115872317894703707333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141246821163090526271609777 105935115872317894703707333)
    ·
      refine ⟨19862834226059605256945125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105935115872317894703707333 19862834226059605256945125)
      ·
        refine ⟨3724281417386175985677211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19862834226059605256945125 3724281417386175985677211)
        ·
          refine ⟨5586422126079263978515817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724281417386175985677211 5586422126079263978515817)
          ·
            refine ⟨4189816594559447983886863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5586422126079263978515817 4189816594559447983886863)
            ·
              refine ⟨6284724891839171975830295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189816594559447983886863 6284724891839171975830295)
              ·
                refine ⟨9427087337758757963745443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284724891839171975830295 9427087337758757963745443)
                ·
                  refine ⟨14140631006638136945618165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9427087337758757963745443 14140631006638136945618165)
                  ·
                    refine ⟨1325684156872325338651703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14140631006638136945618165 1325684156872325338651703)
                    ·
                      rfl

theorem cell22_3872641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_3872641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872641 prefixEnd_3872641 := by exact prefixLift 3872641
  have htrace : WordTrace (prefixWord ++ tailWord_3872641) baseStart_3872641 baseEnd_3872641 := by
    simpa [prefixWord, tailWord_3872641, baseEnd_3872641] using wordTrace_append hprefix tailTrace_3872641
  have hstable : (prefixWord ++ tailWord_3872641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872641).length < 2 ^ (prefixWord ++ tailWord_3872641).sum := by decide
  have hdescent : baseEnd_3872641 < baseStart_3872641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872654 : List Nat := [4, 1, 1, 5, 1, 1, 1, 8]
def baseStart_3872654 : Nat := 118140960795 + 3872654 * 2 ^ 59
def prefixEnd_3872654 : Nat := 4983230072969 + 3 ^ 40 * 3872654 * 2
def baseEnd_3872654 : Nat := 147298734115333070897407

theorem tailTrace_3872654 : CollatzResearch.WordTrace tailWord_3872654 prefixEnd_3872654 147298734115333070897407 := by
  unfold tailWord_3872654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17655911914005428686479127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94164863541362286327888677 17655911914005428686479127)
  ·
    refine ⟨26483867871008143029718691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17655911914005428686479127 26483867871008143029718691)
    ·
      refine ⟨39725801806512214544578037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26483867871008143029718691 39725801806512214544578037)
      ·
        refine ⟨3724293919360520113554191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39725801806512214544578037 3724293919360520113554191)
        ·
          refine ⟨5586440879040780170331287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724293919360520113554191 5586440879040780170331287)
          ·
            refine ⟨8379661318561170255496931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5586440879040780170331287 8379661318561170255496931)
            ·
              refine ⟨12569491977841755383245397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8379661318561170255496931 12569491977841755383245397)
              ·
                refine ⟨147298734115333070897407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12569491977841755383245397 147298734115333070897407)
                ·
                  rfl

theorem cell22_3872654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_3872654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872654 prefixEnd_3872654 := by exact prefixLift 3872654
  have htrace : WordTrace (prefixWord ++ tailWord_3872654) baseStart_3872654 baseEnd_3872654 := by
    simpa [prefixWord, tailWord_3872654, baseEnd_3872654] using wordTrace_append hprefix tailTrace_3872654
  have hstable : (prefixWord ++ tailWord_3872654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872654).length < 2 ^ (prefixWord ++ tailWord_3872654).sum := by decide
  have hdescent : baseEnd_3872654 < baseStart_3872654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872665 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 7]
def baseStart_3872665 : Nat := 118140960795 + 3872665 * 2 ^ 59
def prefixEnd_3872665 : Nat := 4983230072969 + 3 ^ 40 * 3872665 * 2
def baseEnd_3872665 : Nat := 441897457520932425350543

theorem tailTrace_3872665 : CollatzResearch.WordTrace tailWord_3872665 prefixEnd_3872665 441897457520932425350543 := by
  unfold tailWord_3872665
  simp only [CollatzResearch.WordTrace]
  refine ⟨141247696515003578370483449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94165131010002385580322299 141247696515003578370483449)
  ·
    refine ⟨105935772386252683777862587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141247696515003578370483449 105935772386252683777862587)
    ·
      refine ⟨158903658579379025666793881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105935772386252683777862587 158903658579379025666793881)
      ·
        refine ⟨119177743934534269250095411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158903658579379025666793881 119177743934534269250095411)
        ·
          refine ⟨178766615901801403875143117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119177743934534269250095411 178766615901801403875143117)
          ·
            refine ⟨67037480963175526453178669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178766615901801403875143117 67037480963175526453178669)
            ·
              refine ⟨25139055361190822419942001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67037480963175526453178669 25139055361190822419942001)
              ·
                refine ⟨18854291520893116814956501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25139055361190822419942001 18854291520893116814956501)
                ·
                  refine ⟨441897457520932425350543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18854291520893116814956501 441897457520932425350543)
                  ·
                    rfl

theorem cell22_3872665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_3872665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872665 prefixEnd_3872665 := by exact prefixLift 3872665
  have htrace : WordTrace (prefixWord ++ tailWord_3872665) baseStart_3872665 baseEnd_3872665 := by
    simpa [prefixWord, tailWord_3872665, baseEnd_3872665] using wordTrace_append hprefix tailTrace_3872665
  have hstable : (prefixWord ++ tailWord_3872665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872665).length < 2 ^ (prefixWord ++ tailWord_3872665).sum := by decide
  have hdescent : baseEnd_3872665 < baseStart_3872665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872692 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3872692 : Nat := 118140960795 + 3872692 * 2 ^ 59
def prefixEnd_3872692 : Nat := 4983230072969 + 3 ^ 40 * 3872692 * 2
def baseEnd_3872692 : Nat := 1325701615214578205626547

theorem tailTrace_3872692 : CollatzResearch.WordTrace tailWord_3872692 prefixEnd_3872692 1325701615214578205626547 := by
  unfold tailWord_3872692
  simp only [CollatzResearch.WordTrace]
  refine ⟨70624340642952880990858165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94165787523937174654477553 70624340642952880990858165)
  ·
    refine ⟨6621031935276832592892953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70624340642952880990858165 6621031935276832592892953)
    ·
      refine ⟨4965773951457624444669715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6621031935276832592892953 4965773951457624444669715)
      ·
        refine ⟨7448660927186436667004573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965773951457624444669715 7448660927186436667004573)
        ·
          refine ⟨2793247847694913750126715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7448660927186436667004573 2793247847694913750126715)
          ·
            refine ⟨4189871771542370625190073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793247847694913750126715 4189871771542370625190073)
            ·
              refine ⟨3142403828656777968892555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4189871771542370625190073 3142403828656777968892555)
              ·
                refine ⟨4713605742985166953338833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142403828656777968892555 4713605742985166953338833)
                ·
                  refine ⟨3535204307238875215004125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4713605742985166953338833 3535204307238875215004125)
                  ·
                    refine ⟨1325701615214578205626547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3535204307238875215004125 1325701615214578205626547)
                    ·
                      rfl

theorem cell22_3872692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3872692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872692 prefixEnd_3872692 := by exact prefixLift 3872692
  have htrace : WordTrace (prefixWord ++ tailWord_3872692) baseStart_3872692 baseEnd_3872692 := by
    simpa [prefixWord, tailWord_3872692, baseEnd_3872692] using wordTrace_append hprefix tailTrace_3872692
  have hstable : (prefixWord ++ tailWord_3872692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872692).length < 2 ^ (prefixWord ++ tailWord_3872692).sum := by decide
  have hdescent : baseEnd_3872692 < baseStart_3872692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872695 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 2, 8]
def baseStart_3872695 : Nat := 118140960795 + 3872695 * 2 ^ 59
def prefixEnd_3872695 : Nat := 4983230072969 + 3 ^ 40 * 3872695 * 2
def baseEnd_3872695 : Nat := 1325702642175887197801537

theorem tailTrace_3872695 : CollatzResearch.WordTrace tailWord_3872695 prefixEnd_3872695 1325702642175887197801537 := by
  unfold tailWord_3872695
  simp only [CollatzResearch.WordTrace]
  refine ⟨141248790704894893494075539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94165860469929928996050359 141248790704894893494075539)
  ·
    refine ⟨211873186057342340241113309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141248790704894893494075539 211873186057342340241113309)
    ·
      refine ⟨79452444771503377590417491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211873186057342340241113309 79452444771503377590417491)
      ·
        refine ⟨119178667157255066385626237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79452444771503377590417491 119178667157255066385626237)
        ·
          refine ⟨44692000183970649894609839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119178667157255066385626237 44692000183970649894609839)
          ·
            refine ⟨67038000275955974841914759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44692000183970649894609839 67038000275955974841914759)
            ·
              refine ⟨100557000413933962262872139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67038000275955974841914759 100557000413933962262872139)
              ·
                refine ⟨150835500620900943394308209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100557000413933962262872139 150835500620900943394308209)
                ·
                  refine ⟨113126625465675707545731157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150835500620900943394308209 113126625465675707545731157)
                  ·
                    refine ⟨1325702642175887197801537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113126625465675707545731157 1325702642175887197801537)
                    ·
                      rfl

theorem cell22_3872695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_3872695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872695 prefixEnd_3872695 := by exact prefixLift 3872695
  have htrace : WordTrace (prefixWord ++ tailWord_3872695) baseStart_3872695 baseEnd_3872695 := by
    simpa [prefixWord, tailWord_3872695, baseEnd_3872695] using wordTrace_append hprefix tailTrace_3872695
  have hstable : (prefixWord ++ tailWord_3872695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872695).length < 2 ^ (prefixWord ++ tailWord_3872695).sum := by decide
  have hdescent : baseEnd_3872695 < baseStart_3872695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872962 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3872962 : Nat := 118140960795 + 3872962 * 2 ^ 59
def prefixEnd_3872962 : Nat := 4983230072969 + 3 ^ 40 * 3872962 * 2
def baseEnd_3872962 : Nat := 1325794041732387501375719

theorem tailTrace_3872962 : CollatzResearch.WordTrace tailWord_3872962 prefixEnd_3872962 1325794041732387501375719 := by
  unfold tailWord_3872962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35314632248731899523511285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94172352663285065396030093 35314632248731899523511285)
  ·
    refine ⟨3310746773318615580329183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35314632248731899523511285 3310746773318615580329183)
    ·
      refine ⟨4966120159977923370493775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3310746773318615580329183 4966120159977923370493775)
      ·
        refine ⟨7449180239966885055740663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966120159977923370493775 7449180239966885055740663)
        ·
          refine ⟨11173770359950327583610995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7449180239966885055740663 11173770359950327583610995)
          ·
            refine ⟨16760655539925491375416493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11173770359950327583610995 16760655539925491375416493)
            ·
              refine ⟨6285245827472059265781185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16760655539925491375416493 6285245827472059265781185)
              ·
                refine ⟨4713934370604044449335889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285245827472059265781185 4713934370604044449335889)
                ·
                  refine ⟨3535450777953033337001917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4713934370604044449335889 3535450777953033337001917)
                  ·
                    refine ⟨1325794041732387501375719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3535450777953033337001917 1325794041732387501375719)
                    ·
                      rfl

theorem cell22_3872962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3872962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872962 prefixEnd_3872962 := by exact prefixLift 3872962
  have htrace : WordTrace (prefixWord ++ tailWord_3872962) baseStart_3872962 baseEnd_3872962 := by
    simpa [prefixWord, tailWord_3872962, baseEnd_3872962] using wordTrace_append hprefix tailTrace_3872962
  have hstable : (prefixWord ++ tailWord_3872962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872962).length < 2 ^ (prefixWord ++ tailWord_3872962).sum := by decide
  have hdescent : baseEnd_3872962 < baseStart_3872962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3872969 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 5]
def baseStart_3872969 : Nat := 118140960795 + 3872969 * 2 ^ 59
def prefixEnd_3872969 : Nat := 4983230072969 + 3 ^ 40 * 3872969 * 2
def baseEnd_3872969 : Nat := 441932145991813938816899

theorem tailTrace_3872969 : CollatzResearch.WordTrace tailWord_3872969 prefixEnd_3872969 441932145991813938816899 := by
  unfold tailWord_3872969
  simp only [CollatzResearch.WordTrace]
  refine ⟨141258784305902238289549961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94172522870601492193033307 141258784305902238289549961)
  ·
    refine ⟨105944088229426678717162471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141258784305902238289549961 105944088229426678717162471)
    ·
      refine ⟨158916132344140018075743707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105944088229426678717162471 158916132344140018075743707)
      ·
        refine ⟨238374198516210027113615561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158916132344140018075743707 238374198516210027113615561)
        ·
          refine ⟨178780648887157520335211671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238374198516210027113615561 178780648887157520335211671)
          ·
            refine ⟨268170973330736280502817507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178780648887157520335211671 268170973330736280502817507)
            ·
              refine ⟨402256459996104420754226261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268170973330736280502817507 402256459996104420754226261)
              ·
                refine ⟨4713942890579348680713589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 402256459996104420754226261 4713942890579348680713589)
                ·
                  refine ⟨441932145991813938816899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4713942890579348680713589 441932145991813938816899)
                  ·
                    rfl

theorem cell22_3872969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_3872969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3872969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3872969 prefixEnd_3872969 := by exact prefixLift 3872969
  have htrace : WordTrace (prefixWord ++ tailWord_3872969) baseStart_3872969 baseEnd_3872969 := by
    simpa [prefixWord, tailWord_3872969, baseEnd_3872969] using wordTrace_append hprefix tailTrace_3872969
  have hstable : (prefixWord ++ tailWord_3872969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3872969).length < 2 ^ (prefixWord ++ tailWord_3872969).sum := by decide
  have hdescent : baseEnd_3872969 < baseStart_3872969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3872969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873029 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_3873029 : Nat := 118140960795 + 3873029 * 2 ^ 59
def prefixEnd_3873029 : Nat := 4983230072969 + 3 ^ 40 * 3873029 * 2
def baseEnd_3873029 : Nat := 1325816977201621659950513

theorem tailTrace_3873029 : CollatzResearch.WordTrace tailWord_3873029 prefixEnd_3873029 1325816977201621659950513 := by
  unfold tailWord_3873029
  simp only [CollatzResearch.WordTrace]
  refine ⟨141260972685684868536734141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94173981790456579024489427 141260972685684868536734141)
  ·
    refine ⟨52972864757131825701275303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141260972685684868536734141 52972864757131825701275303)
    ·
      refine ⟨79459297135697738551912955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52972864757131825701275303 79459297135697738551912955)
      ·
        refine ⟨119188945703546607827869433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79459297135697738551912955 119188945703546607827869433)
        ·
          refine ⟨89391709277659955870902075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119188945703546607827869433 89391709277659955870902075)
          ·
            refine ⟨134087563916489933806353113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89391709277659955870902075 134087563916489933806353113)
            ·
              refine ⟨100565672937367450354764835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134087563916489933806353113 100565672937367450354764835)
              ·
                refine ⟨150848509406051175532147253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100565672937367450354764835 150848509406051175532147253)
                ·
                  refine ⟨14142047756817297706138805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150848509406051175532147253 14142047756817297706138805)
                  ·
                    refine ⟨1325816977201621659950513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14142047756817297706138805 1325816977201621659950513)
                    ·
                      rfl

theorem cell22_3873029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_3873029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873029 prefixEnd_3873029 := by exact prefixLift 3873029
  have htrace : WordTrace (prefixWord ++ tailWord_3873029) baseStart_3873029 baseEnd_3873029 := by
    simpa [prefixWord, tailWord_3873029, baseEnd_3873029] using wordTrace_append hprefix tailTrace_3873029
  have hstable : (prefixWord ++ tailWord_3873029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873029).length < 2 ^ (prefixWord ++ tailWord_3873029).sum := by decide
  have hdescent : baseEnd_3873029 < baseStart_3873029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873050 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_3873050 : Nat := 118140960795 + 3873050 * 2 ^ 59
def prefixEnd_3873050 : Nat := 4983230072969 + 3 ^ 40 * 3873050 * 2
def baseEnd_3873050 : Nat := 1325824165930784605175449

theorem tailTrace_3873050 : CollatzResearch.WordTrace tailWord_3873050 prefixEnd_3873050 1325824165930784605175449 := by
  unfold tailWord_3873050
  simp only [CollatzResearch.WordTrace]
  refine ⟨35315434654652197280812151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94174492412405859415499069 35315434654652197280812151)
  ·
    refine ⟨52973151981978295921218227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35315434654652197280812151 52973151981978295921218227)
    ·
      refine ⟨79459727972967443881827341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52973151981978295921218227 79459727972967443881827341)
      ·
        refine ⟨29797397989862791455685253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79459727972967443881827341 29797397989862791455685253)
        ·
          refine ⟨5587012123099273397940985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29797397989862791455685253 5587012123099273397940985)
          ·
            refine ⟨4190259092324455048455739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5587012123099273397940985 4190259092324455048455739)
            ·
              refine ⟨6285388638486682572683609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190259092324455048455739 6285388638486682572683609)
              ·
                refine ⟨4714041478865011929512707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285388638486682572683609 4714041478865011929512707)
                ·
                  refine ⟨7071062218297517894269061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714041478865011929512707 7071062218297517894269061)
                  ·
                    refine ⟨1325824165930784605175449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7071062218297517894269061 1325824165930784605175449)
                    ·
                      rfl

theorem cell22_3873050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_3873050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873050 prefixEnd_3873050 := by exact prefixLift 3873050
  have htrace : WordTrace (prefixWord ++ tailWord_3873050) baseStart_3873050 baseEnd_3873050 := by
    simpa [prefixWord, tailWord_3873050, baseEnd_3873050] using wordTrace_append hprefix tailTrace_3873050
  have hstable : (prefixWord ++ tailWord_3873050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873050).length < 2 ^ (prefixWord ++ tailWord_3873050).sum := by decide
  have hdescent : baseEnd_3873050 < baseStart_3873050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873059 : List Nat := [1, 1, 1, 4, 2, 2, 1, 10]
def baseStart_3873059 : Nat := 118140960795 + 3873059 * 2 ^ 59
def prefixEnd_3873059 : Nat := 4983230072969 + 3 ^ 40 * 3873059 * 2
def baseEnd_3873059 : Nat := 147314138534967953522269

theorem tailTrace_3873059 : CollatzResearch.WordTrace tailWord_3873059 prefixEnd_3873059 147314138534967953522269 := by
  unfold tailWord_3873059
  simp only [CollatzResearch.WordTrace]
  refine ⟨141262066875576183660326231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94174711250384122440217487 141262066875576183660326231)
  ·
    refine ⟨211893100313364275490489347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141262066875576183660326231 211893100313364275490489347)
    ·
      refine ⟨317839650470046413235734021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211893100313364275490489347 317839650470046413235734021)
      ·
        refine ⟨59594934463133702481700129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317839650470046413235734021 59594934463133702481700129)
        ·
          refine ⟨44696200847350276861275097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59594934463133702481700129 44696200847350276861275097)
          ·
            refine ⟨33522150635512707645956323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44696200847350276861275097 33522150635512707645956323)
            ·
              refine ⟨50283225953269061468934485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33522150635512707645956323 50283225953269061468934485)
              ·
                refine ⟨147314138534967953522269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50283225953269061468934485 147314138534967953522269)
                ·
                  rfl

theorem cell22_3873059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 10].length) (baseStart_3873059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873059 prefixEnd_3873059 := by exact prefixLift 3873059
  have htrace : WordTrace (prefixWord ++ tailWord_3873059) baseStart_3873059 baseEnd_3873059 := by
    simpa [prefixWord, tailWord_3873059, baseEnd_3873059] using wordTrace_append hprefix tailTrace_3873059
  have hstable : (prefixWord ++ tailWord_3873059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873059).length < 2 ^ (prefixWord ++ tailWord_3873059).sum := by decide
  have hdescent : baseEnd_3873059 < baseStart_3873059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873076 : List Nat := [2, 5, 1, 1, 1, 12]
def baseStart_3873076 : Nat := 118140960795 + 3873076 * 2 ^ 59
def prefixEnd_3873076 : Nat := 4983230072969 + 3 ^ 40 * 3873076 * 2
def baseEnd_3873076 : Nat := 16368309460026286469449

theorem tailTrace_3873076 : CollatzResearch.WordTrace tailWord_3873076 prefixEnd_3873076 16368309460026286469449 := by
  unfold tailWord_3873076
  simp only [CollatzResearch.WordTrace]
  refine ⟨70631343458257297781847541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94175124611009730375796721 70631343458257297781847541)
  ·
    refine ⟨6621688449211621667048207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70631343458257297781847541 6621688449211621667048207)
    ·
      refine ⟨9932532673817432500572311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6621688449211621667048207 9932532673817432500572311)
      ·
        refine ⟨14898799010726148750858467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9932532673817432500572311 14898799010726148750858467)
        ·
          refine ⟨22348198516089223126287701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14898799010726148750858467 22348198516089223126287701)
          ·
            refine ⟨16368309460026286469449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 22348198516089223126287701 16368309460026286469449)
            ·
              rfl

theorem cell22_3873076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 12].length) (baseStart_3873076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873076 prefixEnd_3873076 := by exact prefixLift 3873076
  have htrace : WordTrace (prefixWord ++ tailWord_3873076) baseStart_3873076 baseEnd_3873076 := by
    simpa [prefixWord, tailWord_3873076, baseEnd_3873076] using wordTrace_append hprefix tailTrace_3873076
  have hstable : (prefixWord ++ tailWord_3873076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873076).length < 2 ^ (prefixWord ++ tailWord_3873076).sum := by decide
  have hdescent : baseEnd_3873076 < baseStart_3873076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873108 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_3873108 : Nat := 118140960795 + 3873108 * 2 ^ 59
def prefixEnd_3873108 : Nat := 4983230072969 + 3 ^ 40 * 3873108 * 2
def baseEnd_3873108 : Nat := 1325844020516091787225271

theorem tailTrace_3873108 : CollatzResearch.WordTrace tailWord_3873108 prefixEnd_3873108 1325844020516091787225271 := by
  unfold tailWord_3873108
  simp only [CollatzResearch.WordTrace]
  refine ⟨70631927026199332514429989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94175902701599110019239985 70631927026199332514429989)
  ·
    refine ⟨13243486317412374846455623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70631927026199332514429989 13243486317412374846455623)
    ·
      refine ⟨19865229476118562269683435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13243486317412374846455623 19865229476118562269683435)
      ·
        refine ⟨29797844214177843404525153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19865229476118562269683435 29797844214177843404525153)
        ·
          refine ⟨22348383160633382553393865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29797844214177843404525153 22348383160633382553393865)
          ·
            refine ⟨16761287370475036915045399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22348383160633382553393865 16761287370475036915045399)
            ·
              refine ⟨25141931055712555372568099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16761287370475036915045399 25141931055712555372568099)
              ·
                refine ⟨37712896583568833058852149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25141931055712555372568099 37712896583568833058852149)
                ·
                  refine ⟨3535584054709578099267389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37712896583568833058852149 3535584054709578099267389)
                  ·
                    refine ⟨1325844020516091787225271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3535584054709578099267389 1325844020516091787225271)
                    ·
                      rfl

theorem cell22_3873108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_3873108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873108 prefixEnd_3873108 := by exact prefixLift 3873108
  have htrace : WordTrace (prefixWord ++ tailWord_3873108) baseStart_3873108 baseEnd_3873108 := by
    simpa [prefixWord, tailWord_3873108, baseEnd_3873108] using wordTrace_append hprefix tailTrace_3873108
  have hstable : (prefixWord ++ tailWord_3873108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873108).length < 2 ^ (prefixWord ++ tailWord_3873108).sum := by decide
  have hdescent : baseEnd_3873108 < baseStart_3873108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873118 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3873118 : Nat := 118140960795 + 3873118 * 2 ^ 59
def prefixEnd_3873118 : Nat := 4983230072969 + 3 ^ 40 * 3873118 * 2
def baseEnd_3873118 : Nat := 1325847443720455094475241

theorem tailTrace_3873118 : CollatzResearch.WordTrace tailWord_3873118 prefixEnd_3873118 1325847443720455094475241 := by
  unfold tailWord_3873118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17658027347795304592090501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94176145854908291157816005 17658027347795304592090501)
  ·
    refine ⟨3310880127711619611016969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17658027347795304592090501 3310880127711619611016969)
    ·
      refine ⟨2483160095783714708262727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3310880127711619611016969 2483160095783714708262727)
      ·
        refine ⟨3724740143675572062394091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2483160095783714708262727 3724740143675572062394091)
        ·
          refine ⟨5587110215513358093591137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724740143675572062394091 5587110215513358093591137)
          ·
            refine ⟨4190332661635018570193353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5587110215513358093591137 4190332661635018570193353)
            ·
              refine ⟨3142749496226263927645015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4190332661635018570193353 3142749496226263927645015)
              ·
                refine ⟨4714124244339395891467523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142749496226263927645015 4714124244339395891467523)
                ·
                  refine ⟨7071186366509093837201285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714124244339395891467523 7071186366509093837201285)
                  ·
                    refine ⟨1325847443720455094475241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7071186366509093837201285 1325847443720455094475241)
                    ·
                      rfl

theorem cell22_3873118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3873118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873118 prefixEnd_3873118 := by exact prefixLift 3873118
  have htrace : WordTrace (prefixWord ++ tailWord_3873118) baseStart_3873118 baseEnd_3873118 := by
    simpa [prefixWord, tailWord_3873118, baseEnd_3873118] using wordTrace_append hprefix tailTrace_3873118
  have hstable : (prefixWord ++ tailWord_3873118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873118).length < 2 ^ (prefixWord ++ tailWord_3873118).sum := by decide
  have hdescent : baseEnd_3873118 < baseStart_3873118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873125 : List Nat := [1, 3, 1, 3, 1, 3, 1, 5, 1, 3]
def baseStart_3873125 : Nat := 118140960795 + 3873125 * 2 ^ 59
def prefixEnd_3873125 : Nat := 4983230072969 + 3 ^ 40 * 3873125 * 2
def baseEnd_3873125 : Nat := 1325849839963509409550219

theorem tailTrace_3873125 : CollatzResearch.WordTrace tailWord_3873125 prefixEnd_3873125 1325849839963509409550219 := by
  unfold tailWord_3873125
  simp only [CollatzResearch.WordTrace]
  refine ⟨141264474093337076932228829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94176316062224717954819219 141264474093337076932228829)
  ·
    refine ⟨52974177785001403849585811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141264474093337076932228829 52974177785001403849585811)
    ·
      refine ⟨79461266677502105774378717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52974177785001403849585811 79461266677502105774378717)
      ·
        refine ⟨29797975004063289665392019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79461266677502105774378717 29797975004063289665392019)
        ·
          refine ⟨44696962506094934498088029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29797975004063289665392019 44696962506094934498088029)
          ·
            refine ⟨16761360939785600436783011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44696962506094934498088029 16761360939785600436783011)
            ·
              refine ⟨25142041409678400655174517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16761360939785600436783011 25142041409678400655174517)
              ·
                refine ⟨2357066382157350061422611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25142041409678400655174517 2357066382157350061422611)
                ·
                  refine ⟨3535599573236025092133917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357066382157350061422611 3535599573236025092133917)
                  ·
                    refine ⟨1325849839963509409550219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3535599573236025092133917 1325849839963509409550219)
                    ·
                      rfl

theorem cell22_3873125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_3873125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873125 prefixEnd_3873125 := by exact prefixLift 3873125
  have htrace : WordTrace (prefixWord ++ tailWord_3873125) baseStart_3873125 baseEnd_3873125 := by
    simpa [prefixWord, tailWord_3873125, baseEnd_3873125] using wordTrace_append hprefix tailTrace_3873125
  have hstable : (prefixWord ++ tailWord_3873125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873125).length < 2 ^ (prefixWord ++ tailWord_3873125).sum := by decide
  have hdescent : baseEnd_3873125 < baseStart_3873125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873136 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_3873136 : Nat := 118140960795 + 3873136 * 2 ^ 59
def prefixEnd_3873136 : Nat := 4983230072969 + 3 ^ 40 * 3873136 * 2
def baseEnd_3873136 : Nat := 1325853605488309047525185

theorem tailTrace_3873136 : CollatzResearch.WordTrace tailWord_3873136 prefixEnd_3873136 1325853605488309047525185 := by
  unfold tailWord_3873136
  simp only [CollatzResearch.WordTrace]
  refine ⟨70632437648148612905439631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94176583530864817207252841 70632437648148612905439631)
  ·
    refine ⟨105948656472222919358159447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70632437648148612905439631 105948656472222919358159447)
    ·
      refine ⟨158922984708334379037239171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105948656472222919358159447 158922984708334379037239171)
      ·
        refine ⟨238384477062501568555858757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158922984708334379037239171 238384477062501568555858757)
        ·
          refine ⟨44697089449219044104223517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238384477062501568555858757 44697089449219044104223517)
          ·
            refine ⟨16761408543457141539083819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44697089449219044104223517 16761408543457141539083819)
            ·
              refine ⟨25142112815185712308625729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16761408543457141539083819 25142112815185712308625729)
              ·
                refine ⟨18856584611389284231469297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25142112815185712308625729 18856584611389284231469297)
                ·
                  refine ⟨14142438458541963173601973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18856584611389284231469297 14142438458541963173601973)
                  ·
                    refine ⟨1325853605488309047525185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14142438458541963173601973 1325853605488309047525185)
                    ·
                      rfl

theorem cell22_3873136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_3873136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873136 prefixEnd_3873136 := by exact prefixLift 3873136
  have htrace : WordTrace (prefixWord ++ tailWord_3873136) baseStart_3873136 baseEnd_3873136 := by
    simpa [prefixWord, tailWord_3873136, baseEnd_3873136] using wordTrace_append hprefix tailTrace_3873136
  have hstable : (prefixWord ++ tailWord_3873136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873136).length < 2 ^ (prefixWord ++ tailWord_3873136).sum := by decide
  have hdescent : baseEnd_3873136 < baseStart_3873136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873138 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_3873138 : Nat := 118140960795 + 3873138 * 2 ^ 59
def prefixEnd_3873138 : Nat := 4983230072969 + 3 ^ 40 * 3873138 * 2
def baseEnd_3873138 : Nat := 441951430043060569658393

theorem tailTrace_3873138 : CollatzResearch.WordTrace tailWord_3873138 prefixEnd_3873138 441951430043060569658393 := by
  unfold tailWord_3873138
  simp only [CollatzResearch.WordTrace]
  refine ⟨35316237060572495038113017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94176632161526653434968045 35316237060572495038113017)
  ·
    refine ⟨26487177795429371278584763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35316237060572495038113017 26487177795429371278584763)
    ·
      refine ⟨39730766693144056917877145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26487177795429371278584763 39730766693144056917877145)
      ·
        refine ⟨29798075019858042688407859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39730766693144056917877145 29798075019858042688407859)
        ·
          refine ⟨44697112529787064032611789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29798075019858042688407859 44697112529787064032611789)
          ·
            refine ⟨16761417198670149012229421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44697112529787064032611789 16761417198670149012229421)
            ·
              refine ⟨6285531449501305879586033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16761417198670149012229421 6285531449501305879586033)
              ·
                refine ⟨4714148587125979409689525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285531449501305879586033 4714148587125979409689525)
                ·
                  refine ⟨441951430043060569658393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4714148587125979409689525 441951430043060569658393)
                  ·
                    rfl

theorem cell22_3873138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_3873138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873138 prefixEnd_3873138 := by exact prefixLift 3873138
  have htrace : WordTrace (prefixWord ++ tailWord_3873138) baseStart_3873138 baseEnd_3873138 := by
    simpa [prefixWord, tailWord_3873138, baseEnd_3873138] using wordTrace_append hprefix tailTrace_3873138
  have hstable : (prefixWord ++ tailWord_3873138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873138).length < 2 ^ (prefixWord ++ tailWord_3873138).sum := by decide
  have hdescent : baseEnd_3873138 < baseStart_3873138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873153 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3873153 : Nat := 118140960795 + 3873153 * 2 ^ 59
def prefixEnd_3873153 : Nat := 4983230072969 + 3 ^ 40 * 3873153 * 2
def baseEnd_3873153 : Nat := 1325859424935726669850133

theorem tailTrace_3873153 : CollatzResearch.WordTrace tailWord_3873153 prefixEnd_3873153 1325859424935726669850133 := by
  unfold tailWord_3873153
  simp only [CollatzResearch.WordTrace]
  refine ⟨141265495337235637714248113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94176996891490425142832075 141265495337235637714248113)
  ·
    refine ⟨105949121502926728285686085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141265495337235637714248113 105949121502926728285686085)
    ·
      refine ⟨19865460281798761553566141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105949121502926728285686085 19865460281798761553566141)
      ·
        refine ⟨7449547605674535582587303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19865460281798761553566141 7449547605674535582587303)
        ·
          refine ⟨11174321408511803373880955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7449547605674535582587303 11174321408511803373880955)
          ·
            refine ⟨16761482112767705060821433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11174321408511803373880955 16761482112767705060821433)
            ·
              refine ⟨12571111584575778795616075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16761482112767705060821433 12571111584575778795616075)
              ·
                refine ⟨18856667376863668193424113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12571111584575778795616075 18856667376863668193424113)
                ·
                  refine ⟨14142500532647751145068085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18856667376863668193424113 14142500532647751145068085)
                  ·
                    refine ⟨1325859424935726669850133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14142500532647751145068085 1325859424935726669850133)
                    ·
                      rfl

theorem cell22_3873153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3873153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873153 prefixEnd_3873153 := by exact prefixLift 3873153
  have htrace : WordTrace (prefixWord ++ tailWord_3873153) baseStart_3873153 baseEnd_3873153 := by
    simpa [prefixWord, tailWord_3873153, baseEnd_3873153] using wordTrace_append hprefix tailTrace_3873153
  have hstable : (prefixWord ++ tailWord_3873153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873153).length < 2 ^ (prefixWord ++ tailWord_3873153).sum := by decide
  have hdescent : baseEnd_3873153 < baseStart_3873153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873155 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 5]
def baseStart_3873155 : Nat := 118140960795 + 3873155 * 2 ^ 59
def prefixEnd_3873155 : Nat := 4983230072969 + 3 ^ 40 * 3873155 * 2
def baseEnd_3873155 : Nat := 441953369858866443766709

theorem tailTrace_3873155 : CollatzResearch.WordTrace tailWord_3873155 prefixEnd_3873155 441953369858866443766709 := by
  unfold tailWord_3873155
  simp only [CollatzResearch.WordTrace]
  refine ⟨141265568283228392055820919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94177045522152261370547279 141265568283228392055820919)
  ·
    refine ⟨211898352424842588083731379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141265568283228392055820919 211898352424842588083731379)
    ·
      refine ⟨317847528637263882125597069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211898352424842588083731379 317847528637263882125597069)
      ·
        refine ⟨119192823238973955797098901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317847528637263882125597069 119192823238973955797098901)
        ·
          refine ⟨5587163589326904177989011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119192823238973955797098901 5587163589326904177989011)
          ·
            refine ⟨8380745383990356266983517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587163589326904177989011 8380745383990356266983517)
            ·
              refine ⟨3142779518996383600118819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8380745383990356266983517 3142779518996383600118819)
              ·
                refine ⟨4714169278494575400178229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142779518996383600118819 4714169278494575400178229)
                ·
                  refine ⟨441953369858866443766709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4714169278494575400178229 441953369858866443766709)
                  ·
                    rfl

theorem cell22_3873155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 5].length) (baseStart_3873155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873155 prefixEnd_3873155 := by exact prefixLift 3873155
  have htrace : WordTrace (prefixWord ++ tailWord_3873155) baseStart_3873155 baseEnd_3873155 := by
    simpa [prefixWord, tailWord_3873155, baseEnd_3873155] using wordTrace_append hprefix tailTrace_3873155
  have hstable : (prefixWord ++ tailWord_3873155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873155).length < 2 ^ (prefixWord ++ tailWord_3873155).sum := by decide
  have hdescent : baseEnd_3873155 < baseStart_3873155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873258 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_3873258 : Nat := 118140960795 + 3873258 * 2 ^ 59
def prefixEnd_3873258 : Nat := 4983230072969 + 3 ^ 40 * 3873258 * 2
def baseEnd_3873258 : Nat := 1325895368581541395974811

theorem tailTrace_3873258 : CollatzResearch.WordTrace tailWord_3873258 prefixEnd_3873258 1325895368581541395974811 := by
  unfold tailWord_3873258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35317331250463810161705107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94179550001236827097880285 35317331250463810161705107)
  ·
    refine ⟨52975996875695715242557661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35317331250463810161705107 52975996875695715242557661)
    ·
      refine ⟨19865998828385893215959123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52975996875695715242557661 19865998828385893215959123)
      ·
        refine ⟨29798998242578839823938685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19865998828385893215959123 29798998242578839823938685)
        ·
          refine ⟨11174624340967064933977007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29798998242578839823938685 11174624340967064933977007)
          ·
            refine ⟨16761936511450597400965511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11174624340967064933977007 16761936511450597400965511)
            ·
              refine ⟨25142904767175896101448267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16761936511450597400965511 25142904767175896101448267)
              ·
                refine ⟨37714357150763844152172401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25142904767175896101448267 37714357150763844152172401)
                ·
                  refine ⟨28285767863072883114129301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37714357150763844152172401 28285767863072883114129301)
                  ·
                    refine ⟨1325895368581541395974811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28285767863072883114129301 1325895368581541395974811)
                    ·
                      rfl

theorem cell22_3873258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_3873258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873258 prefixEnd_3873258 := by exact prefixLift 3873258
  have htrace : WordTrace (prefixWord ++ tailWord_3873258) baseStart_3873258 baseEnd_3873258 := by
    simpa [prefixWord, tailWord_3873258, baseEnd_3873258] using wordTrace_append hprefix tailTrace_3873258
  have hstable : (prefixWord ++ tailWord_3873258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873258).length < 2 ^ (prefixWord ++ tailWord_3873258).sum := by decide
  have hdescent : baseEnd_3873258 < baseStart_3873258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873273 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 5]
def baseStart_3873273 : Nat := 118140960795 + 3873273 * 2 ^ 59
def prefixEnd_3873273 : Nat := 4983230072969 + 3 ^ 40 * 3873273 * 2
def baseEnd_3873273 : Nat := 441966834462695452283255

theorem tailTrace_3873273 : CollatzResearch.WordTrace tailWord_3873273 prefixEnd_3873273 441966834462695452283255 := by
  unfold tailWord_3873273
  simp only [CollatzResearch.WordTrace]
  refine ⟨141269872096800898208616473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94179914731200598805744315 141269872096800898208616473)
  ·
    refine ⟨105952404072600673656462355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141269872096800898208616473 105952404072600673656462355)
    ·
      refine ⟨158928606108901010484693533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105952404072600673656462355 158928606108901010484693533)
      ·
        refine ⟨59598227290837878931760075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158928606108901010484693533 59598227290837878931760075)
        ·
          refine ⟨89397340936256818397640113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59598227290837878931760075 89397340936256818397640113)
          ·
            refine ⟨67048005702192613798230085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89397340936256818397640113 67048005702192613798230085)
            ·
              refine ⟨12571501069161115087168141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67048005702192613798230085 12571501069161115087168141)
              ·
                refine ⟨4714312900935418157688053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12571501069161115087168141 4714312900935418157688053)
                ·
                  refine ⟨441966834462695452283255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4714312900935418157688053 441966834462695452283255)
                  ·
                    rfl

theorem cell22_3873273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_3873273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873273 prefixEnd_3873273 := by exact prefixLift 3873273
  have htrace : WordTrace (prefixWord ++ tailWord_3873273) baseStart_3873273 baseEnd_3873273 := by
    simpa [prefixWord, tailWord_3873273, baseEnd_3873273] using wordTrace_append hprefix tailTrace_3873273
  have hstable : (prefixWord ++ tailWord_3873273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873273).length < 2 ^ (prefixWord ++ tailWord_3873273).sum := by decide
  have hdescent : baseEnd_3873273 < baseStart_3873273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873294 : List Nat := [4, 1, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_3873294 : Nat := 118140960795 + 3873294 * 2 ^ 59
def prefixEnd_3873294 : Nat := 4983230072969 + 3 ^ 40 * 3873294 * 2
def baseEnd_3873294 : Nat := 1325907692117249302074701

theorem tailTrace_3873294 : CollatzResearch.WordTrace tailWord_3873294 prefixEnd_3873294 1325907692117249302074701 := by
  unfold tailWord_3873294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17658829753715602349391367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94180425353149879196753957 17658829753715602349391367)
  ·
    refine ⟨26488244630573403524087051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17658829753715602349391367 26488244630573403524087051)
    ·
      refine ⟨39732366945860105286130577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26488244630573403524087051 39732366945860105286130577)
      ·
        refine ⟨29799275209395078964597933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39732366945860105286130577 29799275209395078964597933)
        ·
          refine ⟨11174728203523154611724225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29799275209395078964597933 11174728203523154611724225)
          ·
            refine ⟨8381046152642365958793169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11174728203523154611724225 8381046152642365958793169)
            ·
              refine ⟨6285784614481774469094877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8381046152642365958793169 6285784614481774469094877)
              ·
                refine ⟨2357169230430665425910579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6285784614481774469094877 2357169230430665425910579)
                ·
                  refine ⟨3535753845645998138865869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357169230430665425910579 3535753845645998138865869)
                  ·
                    refine ⟨1325907692117249302074701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3535753845645998138865869 1325907692117249302074701)
                    ·
                      rfl

theorem cell22_3873294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_3873294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873294 prefixEnd_3873294 := by exact prefixLift 3873294
  have htrace : WordTrace (prefixWord ++ tailWord_3873294) baseStart_3873294 baseEnd_3873294 := by
    simpa [prefixWord, tailWord_3873294, baseEnd_3873294] using wordTrace_append hprefix tailTrace_3873294
  have hstable : (prefixWord ++ tailWord_3873294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873294).length < 2 ^ (prefixWord ++ tailWord_3873294).sum := by decide
  have hdescent : baseEnd_3873294 < baseStart_3873294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873384 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 2, 3]
def baseStart_3873384 : Nat := 118140960795 + 3873384 * 2 ^ 59
def prefixEnd_3873384 : Nat := 4983230072969 + 3 ^ 40 * 3873384 * 2
def baseEnd_3873384 : Nat := 1325938500956519067324425

theorem tailTrace_3873384 : CollatzResearch.WordTrace tailWord_3873384 prefixEnd_3873384 1325938500956519067324425 := by
  unfold tailWord_3873384
  simp only [CollatzResearch.WordTrace]
  refine ⟨70636960299699382082953603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94182613732932509443938137 70636960299699382082953603)
  ·
    refine ⟨105955440449549073124430405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70636960299699382082953603 105955440449549073124430405)
    ·
      refine ⟨19866645084290451210830701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105955440449549073124430405 19866645084290451210830701)
      ·
        refine ⟨7449991906608919204061513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19866645084290451210830701 7449991906608919204061513)
        ·
          refine ⟨5587493929956689403046135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7449991906608919204061513 5587493929956689403046135)
          ·
            refine ⟨8381240894935034104569203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587493929956689403046135 8381240894935034104569203)
            ·
              refine ⟨12571861342402551156853805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8381240894935034104569203 12571861342402551156853805)
              ·
                refine ⟨4714448003400956683820177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12571861342402551156853805 4714448003400956683820177)
                ·
                  refine ⟨3535836002550717512865133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4714448003400956683820177 3535836002550717512865133)
                  ·
                    refine ⟨1325938500956519067324425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3535836002550717512865133 1325938500956519067324425)
                    ·
                      rfl

theorem cell22_3873384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_3873384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873384 prefixEnd_3873384 := by exact prefixLift 3873384
  have htrace : WordTrace (prefixWord ++ tailWord_3873384) baseStart_3873384 baseEnd_3873384 := by
    simpa [prefixWord, tailWord_3873384, baseEnd_3873384] using wordTrace_append hprefix tailTrace_3873384
  have hstable : (prefixWord ++ tailWord_3873384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873384).length < 2 ^ (prefixWord ++ tailWord_3873384).sum := by decide
  have hdescent : baseEnd_3873384 < baseStart_3873384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873423 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 4, 5]
def baseStart_3873423 : Nat := 118140960795 + 3873423 * 2 ^ 59
def prefixEnd_3873423 : Nat := 4983230072969 + 3 ^ 40 * 3873423 * 2
def baseEnd_3873423 : Nat := 1325951851453535965599305

theorem tailTrace_3873423 : CollatzResearch.WordTrace tailWord_3873423 prefixEnd_3873423 1325951851453535965599305 := by
  unfold tailWord_3873423
  simp only [CollatzResearch.WordTrace]
  refine ⟨141275343046257473826576923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94183562030838315884384615 141275343046257473826576923)
  ·
    refine ⟨211913014569386210739865385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141275343046257473826576923 211913014569386210739865385)
    ·
      refine ⟨158934760927039658054899039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211913014569386210739865385 158934760927039658054899039)
      ·
        refine ⟨238402141390559487082348559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158934760927039658054899039 238402141390559487082348559)
        ·
          refine ⟨357603212085839230623522839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238402141390559487082348559 357603212085839230623522839)
          ·
            refine ⟨536404818128758845935284259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357603212085839230623522839 536404818128758845935284259)
            ·
              refine ⟨804607227193138268902926389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536404818128758845935284259 804607227193138268902926389)
              ·
                refine ⟨75431927549356712709649349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804607227193138268902926389 75431927549356712709649349)
                ·
                  refine ⟨14143486415504383633059253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75431927549356712709649349 14143486415504383633059253)
                  ·
                    refine ⟨1325951851453535965599305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14143486415504383633059253 1325951851453535965599305)
                    ·
                      rfl

theorem cell22_3873423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_3873423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873423 prefixEnd_3873423 := by exact prefixLift 3873423
  have htrace : WordTrace (prefixWord ++ tailWord_3873423) baseStart_3873423 baseEnd_3873423 := by
    simpa [prefixWord, tailWord_3873423, baseEnd_3873423] using wordTrace_append hprefix tailTrace_3873423
  have hstable : (prefixWord ++ tailWord_3873423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873423).length < 2 ^ (prefixWord ++ tailWord_3873423).sum := by decide
  have hdescent : baseEnd_3873423 < baseStart_3873423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873455 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 3, 4]
def baseStart_3873455 : Nat := 118140960795 + 3873455 * 2 ^ 59
def prefixEnd_3873455 : Nat := 4983230072969 + 3 ^ 40 * 3873455 * 2
def baseEnd_3873455 : Nat := 1325962805707498548799207

theorem tailTrace_3873455 : CollatzResearch.WordTrace tailWord_3873455 prefixEnd_3873455 1325962805707498548799207 := by
  unfold tailWord_3873455
  simp only [CollatzResearch.WordTrace]
  refine ⟨141276510182141543291741819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94184340121427695527827879 141276510182141543291741819)
  ·
    refine ⟨211914765273212314937612729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141276510182141543291741819 211914765273212314937612729)
    ·
      refine ⟨158936073954909236203209547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211914765273212314937612729 158936073954909236203209547)
      ·
        refine ⟨238404110932363854304814321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158936073954909236203209547 238404110932363854304814321)
        ·
          refine ⟨178803083199272890728610741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238404110932363854304814321 178803083199272890728610741)
          ·
            refine ⟨16762789049931833505807257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178803083199272890728610741 16762789049931833505807257)
            ·
              refine ⟨12572091787448875129355443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16762789049931833505807257 12572091787448875129355443)
              ·
                refine ⟨18858137681173312694033165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12572091787448875129355443 18858137681173312694033165)
                ·
                  refine ⟨7071801630439992260262437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18858137681173312694033165 7071801630439992260262437)
                  ·
                    refine ⟨1325962805707498548799207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7071801630439992260262437 1325962805707498548799207)
                    ·
                      rfl

theorem cell22_3873455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_3873455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873455 prefixEnd_3873455 := by exact prefixLift 3873455
  have htrace : WordTrace (prefixWord ++ tailWord_3873455) baseStart_3873455 baseEnd_3873455 := by
    simpa [prefixWord, tailWord_3873455, baseEnd_3873455] using wordTrace_append hprefix tailTrace_3873455
  have hstable : (prefixWord ++ tailWord_3873455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873455).length < 2 ^ (prefixWord ++ tailWord_3873455).sum := by decide
  have hdescent : baseEnd_3873455 < baseStart_3873455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873470 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_3873470 : Nat := 118140960795 + 3873470 * 2 ^ 59
def prefixEnd_3873470 : Nat := 4983230072969 + 3 ^ 40 * 3873470 * 2
def baseEnd_3873470 : Nat := 441989313504681169891387

theorem tailTrace_3873470 : CollatzResearch.WordTrace tailWord_3873470 prefixEnd_3873470 441989313504681169891387 := by
  unfold tailWord_3873470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659632159635900106692233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94184704851391467235691909 17659632159635900106692233)
  ·
    refine ⟨13244724119726925080019175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17659632159635900106692233 13244724119726925080019175)
    ·
      refine ⟨19867086179590387620028763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13244724119726925080019175 19867086179590387620028763)
      ·
        refine ⟨29800629269385581430043145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19867086179590387620028763 29800629269385581430043145)
        ·
          refine ⟨22350471952039186072532359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29800629269385581430043145 22350471952039186072532359)
          ·
            refine ⟨33525707928058779108798539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22350471952039186072532359 33525707928058779108798539)
            ·
              refine ⟨50288561892088168663197809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33525707928058779108798539 50288561892088168663197809)
              ·
                refine ⟨37716421419066126497398357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50288561892088168663197809 37716421419066126497398357)
                ·
                  refine ⟨441989313504681169891387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37716421419066126497398357 441989313504681169891387)
                  ·
                    rfl

theorem cell22_3873470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_3873470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873470 prefixEnd_3873470 := by exact prefixLift 3873470
  have htrace : WordTrace (prefixWord ++ tailWord_3873470) baseStart_3873470 baseEnd_3873470 := by
    simpa [prefixWord, tailWord_3873470, baseEnd_3873470] using wordTrace_append hprefix tailTrace_3873470
  have hstable : (prefixWord ++ tailWord_3873470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873470).length < 2 ^ (prefixWord ++ tailWord_3873470).sum := by decide
  have hdescent : baseEnd_3873470 < baseStart_3873470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873472 : List Nat := [2, 1, 1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_3873472 : Nat := 118140960795 + 3873472 * 2 ^ 59
def prefixEnd_3873472 : Nat := 4983230072969 + 3 ^ 40 * 3873472 * 2
def baseEnd_3873472 : Nat := 1325968625154916171124155

theorem tailTrace_3873472 : CollatzResearch.WordTrace tailWord_3873472 prefixEnd_3873472 1325968625154916171124155 := by
  unfold tailWord_3873472
  simp only [CollatzResearch.WordTrace]
  refine ⟨70638565111539977597555335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94184753482053303463407113 70638565111539977597555335)
  ·
    refine ⟨105957847667309966396333003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70638565111539977597555335 105957847667309966396333003)
    ·
      refine ⟨158936771500964949594499505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105957847667309966396333003 158936771500964949594499505)
      ·
        refine ⟨119202578625723712195874629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158936771500964949594499505 119202578625723712195874629)
        ·
          refine ⟨22350483492323196036726493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119202578625723712195874629 22350483492323196036726493)
          ·
            refine ⟨8381431309621198513772435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22350483492323196036726493 8381431309621198513772435)
            ·
              refine ⟨12572146964431797770658653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8381431309621198513772435 12572146964431797770658653)
              ·
                refine ⟨4714555111661924163996995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12572146964431797770658653 4714555111661924163996995)
                ·
                  refine ⟨7071832667492886245995493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714555111661924163996995 7071832667492886245995493)
                  ·
                    refine ⟨1325968625154916171124155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7071832667492886245995493 1325968625154916171124155)
                    ·
                      rfl

theorem cell22_3873472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_3873472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873472 prefixEnd_3873472 := by exact prefixLift 3873472
  have htrace : WordTrace (prefixWord ++ tailWord_3873472) baseStart_3873472 baseEnd_3873472 := by
    simpa [prefixWord, tailWord_3873472, baseEnd_3873472] using wordTrace_append hprefix tailTrace_3873472
  have hstable : (prefixWord ++ tailWord_3873472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873472).length < 2 ^ (prefixWord ++ tailWord_3873472).sum := by decide
  have hdescent : baseEnd_3873472 < baseStart_3873472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873517 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3873517 : Nat := 118140960795 + 3873517 * 2 ^ 59
def prefixEnd_3873517 : Nat := 4983230072969 + 3 ^ 40 * 3873517 * 2
def baseEnd_3873517 : Nat := 1325984029574551053749017

theorem tailTrace_3873517 : CollatzResearch.WordTrace tailWord_3873517 prefixEnd_3873517 1325984029574551053749017 := by
  unfold tailWord_3873517
  simp only [CollatzResearch.WordTrace]
  refine ⟨141278771507916927880498805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94185847671944618586999203 141278771507916927880498805)
  ·
    refine ⟨13244884828867211988796763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141278771507916927880498805 13244884828867211988796763)
    ·
      refine ⟨19867327243300817983195145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13244884828867211988796763 19867327243300817983195145)
      ·
        refine ⟨14900495432475613487396359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19867327243300817983195145 14900495432475613487396359)
        ·
          refine ⟨22350743148713420231094539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14900495432475613487396359 22350743148713420231094539)
          ·
            refine ⟨33526114723070130346641809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22350743148713420231094539 33526114723070130346641809)
            ·
              refine ⟨25144586042302597759981357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33526114723070130346641809 25144586042302597759981357)
              ·
                refine ⟨9429219765863474159993009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25144586042302597759981357 9429219765863474159993009)
                ·
                  refine ⟨7071914824397605619994757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9429219765863474159993009 7071914824397605619994757)
                  ·
                    refine ⟨1325984029574551053749017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7071914824397605619994757 1325984029574551053749017)
                    ·
                      rfl

theorem cell22_3873517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3873517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873517 prefixEnd_3873517 := by exact prefixLift 3873517
  have htrace : WordTrace (prefixWord ++ tailWord_3873517) baseStart_3873517 baseEnd_3873517 := by
    simpa [prefixWord, tailWord_3873517, baseEnd_3873517] using wordTrace_append hprefix tailTrace_3873517
  have hstable : (prefixWord ++ tailWord_3873517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873517).length < 2 ^ (prefixWord ++ tailWord_3873517).sum := by decide
  have hdescent : baseEnd_3873517 < baseStart_3873517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873534 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3873534 : Nat := 118140960795 + 3873534 * 2 ^ 59
def prefixEnd_3873534 : Nat := 4983230072969 + 3 ^ 40 * 3873534 * 2
def baseEnd_3873534 : Nat := 1325989849021968676073965

theorem tailTrace_3873534 : CollatzResearch.WordTrace tailWord_3873534 prefixEnd_3873534 1325989849021968676073965 := by
  unfold tailWord_3873534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659923943606917472983457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94186261032570226522578437 17659923943606917472983457)
  ·
    refine ⟨13244942957705188104737593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17659923943606917472983457 13244942957705188104737593)
    ·
      refine ⟨9933707218278891078553195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13244942957705188104737593 9933707218278891078553195)
      ·
        refine ⟨14900560827418336617829793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9933707218278891078553195 14900560827418336617829793)
        ·
          refine ⟨11175420620563752463372345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14900560827418336617829793 11175420620563752463372345)
          ·
            refine ⟨8381565465422814347529259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11175420620563752463372345 8381565465422814347529259)
            ·
              refine ⟨12572348198134221521293889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8381565465422814347529259 12572348198134221521293889)
              ·
                refine ⟨9429261148600666140970417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12572348198134221521293889 9429261148600666140970417)
                ·
                  refine ⟨7071945861450499605727813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9429261148600666140970417 7071945861450499605727813)
                  ·
                    refine ⟨1325989849021968676073965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7071945861450499605727813 1325989849021968676073965)
                    ·
                      rfl

theorem cell22_3873534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3873534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873534 prefixEnd_3873534 := by exact prefixLift 3873534
  have htrace : WordTrace (prefixWord ++ tailWord_3873534) baseStart_3873534 baseEnd_3873534 := by
    simpa [prefixWord, tailWord_3873534, baseEnd_3873534] using wordTrace_append hprefix tailTrace_3873534
  have hstable : (prefixWord ++ tailWord_3873534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873534).length < 2 ^ (prefixWord ++ tailWord_3873534).sum := by decide
  have hdescent : baseEnd_3873534 < baseStart_3873534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873594 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_3873594 : Nat := 118140960795 + 3873594 * 2 ^ 59
def prefixEnd_3873594 : Nat := 4983230072969 + 3 ^ 40 * 3873594 * 2
def baseEnd_3873594 : Nat := 442003462749382839857927

theorem tailTrace_3873594 : CollatzResearch.WordTrace tailWord_3873594 prefixEnd_3873594 442003462749382839857927 := by
  unfold tailWord_3873594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35320394982159492507762959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94187719952425313354034557 35320394982159492507762959)
  ·
    refine ⟨52980592473239238761644439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35320394982159492507762959 52980592473239238761644439)
    ·
      refine ⟨79470888709858858142466659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52980592473239238761644439 79470888709858858142466659)
      ·
        refine ⟨119206333064788287213699989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79470888709858858142466659 119206333064788287213699989)
        ·
          refine ⟨5587796862411950963142187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119206333064788287213699989 5587796862411950963142187)
          ·
            refine ⟨8381695293617926444713281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587796862411950963142187 8381695293617926444713281)
            ·
              refine ⟨6286271470213444833534961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8381695293617926444713281 6286271470213444833534961)
              ·
                refine ⟨4714703602660083625151221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286271470213444833534961 4714703602660083625151221)
                ·
                  refine ⟨442003462749382839857927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4714703602660083625151221 442003462749382839857927)
                  ·
                    rfl

theorem cell22_3873594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_3873594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873594 prefixEnd_3873594 := by exact prefixLift 3873594
  have htrace : WordTrace (prefixWord ++ tailWord_3873594) baseStart_3873594 baseEnd_3873594 := by
    simpa [prefixWord, tailWord_3873594, baseEnd_3873594] using wordTrace_append hprefix tailTrace_3873594
  have hstable : (prefixWord ++ tailWord_3873594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873594).length < 2 ^ (prefixWord ++ tailWord_3873594).sum := by decide
  have hdescent : baseEnd_3873594 < baseStart_3873594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873598 : List Nat := [4, 2, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_3873598 : Nat := 118140960795 + 3873598 * 2 ^ 59
def prefixEnd_3873598 : Nat := 4983230072969 + 3 ^ 40 * 3873598 * 2
def baseEnd_3873598 : Nat := 1326011757529893842473769

theorem tailTrace_3873598 : CollatzResearch.WordTrace tailWord_3873598 prefixEnd_3873598 1326011757529893842473769 := by
  unfold tailWord_3873598
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660215727577934839274681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94187817213748985809464965 17660215727577934839274681)
  ·
    refine ⟨13245161795683451129456011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17660215727577934839274681 13245161795683451129456011)
    ·
      refine ⟨19867742693525176694184017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13245161795683451129456011 19867742693525176694184017)
      ·
        refine ⟨14900807020143882520638013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19867742693525176694184017 14900807020143882520638013)
        ·
          refine ⟨5587802632553955945239255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14900807020143882520638013 5587802632553955945239255)
          ·
            refine ⟨8381703948830933917858883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587802632553955945239255 8381703948830933917858883)
            ·
              refine ⟨12572555923246400876788325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8381703948830933917858883 12572555923246400876788325)
              ·
                refine ⟨2357354235608700164397811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12572555923246400876788325 2357354235608700164397811)
                ·
                  refine ⟨3536031353413050246596717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357354235608700164397811 3536031353413050246596717)
                  ·
                    refine ⟨1326011757529893842473769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3536031353413050246596717 1326011757529893842473769)
                    ·
                      rfl

theorem cell22_3873598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_3873598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873598 prefixEnd_3873598 := by exact prefixLift 3873598
  have htrace : WordTrace (prefixWord ++ tailWord_3873598) baseStart_3873598 baseEnd_3873598 := by
    simpa [prefixWord, tailWord_3873598, baseEnd_3873598] using wordTrace_append hprefix tailTrace_3873598
  have hstable : (prefixWord ++ tailWord_3873598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873598).length < 2 ^ (prefixWord ++ tailWord_3873598).sum := by decide
  have hdescent : baseEnd_3873598 < baseStart_3873598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873637 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_3873637 : Nat := 118140960795 + 3873637 * 2 ^ 59
def prefixEnd_3873637 : Nat := 4983230072969 + 3 ^ 40 * 3873637 * 2
def baseEnd_3873637 : Nat := 1326025108026910740748649

theorem tailTrace_3873637 : CollatzResearch.WordTrace tailWord_3873637 prefixEnd_3873637 1326025108026910740748649 := by
  unfold tailWord_3873637
  simp only [CollatzResearch.WordTrace]
  refine ⟨141283148267482188374867165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94188765511654792249911443 141283148267482188374867165)
  ·
    refine ⟨52981180600305820640575187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141283148267482188374867165 52981180600305820640575187)
    ·
      refine ⟨79471770900458730960862781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52981180600305820640575187 79471770900458730960862781)
      ·
        refine ⟨29801914087672024110323543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79471770900458730960862781 29801914087672024110323543)
        ·
          refine ⟨44702871131508036165485315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29801914087672024110323543 44702871131508036165485315)
          ·
            refine ⟨67054306697262054248227973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44702871131508036165485315 67054306697262054248227973)
            ·
              refine ⟨12572682505736635171542745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67054306697262054248227973 12572682505736635171542745)
              ·
                refine ⟨9429511879302476378657059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12572682505736635171542745 9429511879302476378657059)
                ·
                  refine ⟨14144267818953714567985589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429511879302476378657059 14144267818953714567985589)
                  ·
                    refine ⟨1326025108026910740748649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14144267818953714567985589 1326025108026910740748649)
                    ·
                      rfl

theorem cell22_3873637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_3873637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873637 prefixEnd_3873637 := by exact prefixLift 3873637
  have htrace : WordTrace (prefixWord ++ tailWord_3873637) baseStart_3873637 baseEnd_3873637 := by
    simpa [prefixWord, tailWord_3873637, baseEnd_3873637] using wordTrace_append hprefix tailTrace_3873637
  have hstable : (prefixWord ++ tailWord_3873637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873637).length < 2 ^ (prefixWord ++ tailWord_3873637).sum := by decide
  have hdescent : baseEnd_3873637 < baseStart_3873637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873639 : List Nat := [1, 1, 5, 1, 2, 2, 1, 5, 4]
def baseStart_3873639 : Nat := 118140960795 + 3873639 * 2 ^ 59
def prefixEnd_3873639 : Nat := 4983230072969 + 3 ^ 40 * 3873639 * 2
def baseEnd_3873639 : Nat := 442008597555927800732881

theorem tailTrace_3873639 : CollatzResearch.WordTrace tailWord_3873639 prefixEnd_3873639 442008597555927800732881 := by
  unfold tailWord_3873639
  simp only [CollatzResearch.WordTrace]
  refine ⟨141283221213474942716439971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94188814142316628477626647 141283221213474942716439971)
  ·
    refine ⟨211924831820212414074659957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141283221213474942716439971 211924831820212414074659957)
    ·
      refine ⟨19867952983144913819499371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211924831820212414074659957 19867952983144913819499371)
      ·
        refine ⟨29801929474717370729249057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19867952983144913819499371 29801929474717370729249057)
        ·
          refine ⟨22351447106038028046936793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29801929474717370729249057 22351447106038028046936793)
          ·
            refine ⟨16763585329528521035202595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22351447106038028046936793 16763585329528521035202595)
            ·
              refine ⟨25145377994292781552803893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16763585329528521035202595 25145377994292781552803893)
              ·
                refine ⟨2357379186964948270575365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25145377994292781552803893 2357379186964948270575365)
                ·
                  refine ⟨442008597555927800732881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2357379186964948270575365 442008597555927800732881)
                  ·
                    rfl

theorem cell22_3873639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 4].length) (baseStart_3873639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873639 prefixEnd_3873639 := by exact prefixLift 3873639
  have htrace : WordTrace (prefixWord ++ tailWord_3873639) baseStart_3873639 baseEnd_3873639 := by
    simpa [prefixWord, tailWord_3873639, baseEnd_3873639] using wordTrace_append hprefix tailTrace_3873639
  have hstable : (prefixWord ++ tailWord_3873639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873639).length < 2 ^ (prefixWord ++ tailWord_3873639).sum := by decide
  have hdescent : baseEnd_3873639 < baseStart_3873639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873787 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 1, 6]
def baseStart_3873787 : Nat := 118140960795 + 3873787 * 2 ^ 59
def prefixEnd_3873787 : Nat := 4983230072969 + 3 ^ 40 * 3873787 * 2
def baseEnd_3873787 : Nat := 1326076456092360349498189

theorem tailTrace_3873787 : CollatzResearch.WordTrace tailWord_3873787 prefixEnd_3873787 1326076456092360349498189 := by
  unfold tailWord_3873787
  simp only [CollatzResearch.WordTrace]
  refine ⟨141288619216938763992827615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94192412811292509328551743 141288619216938763992827615)
  ·
    refine ⟨211932928825408145989241423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141288619216938763992827615 211932928825408145989241423)
    ·
      refine ⟨317899393238112218983862135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211932928825408145989241423 317899393238112218983862135)
      ·
        refine ⟨476849089857168328475793203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317899393238112218983862135 476849089857168328475793203)
        ·
          refine ⟨715273634785752492713689805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476849089857168328475793203 715273634785752492713689805)
          ·
            refine ⟨268227613044657184767633677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715273634785752492713689805 268227613044657184767633677)
            ·
              refine ⟨100585354891746444287862629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268227613044657184767633677 100585354891746444287862629)
              ·
                refine ⟨18859754042202458303974243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100585354891746444287862629 18859754042202458303974243)
                ·
                  refine ⟨28289631063303687455961365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18859754042202458303974243 28289631063303687455961365)
                  ·
                    refine ⟨1326076456092360349498189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28289631063303687455961365 1326076456092360349498189)
                    ·
                      rfl

theorem cell22_3873787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_3873787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873787 prefixEnd_3873787 := by exact prefixLift 3873787
  have htrace : WordTrace (prefixWord ++ tailWord_3873787) baseStart_3873787 baseEnd_3873787 := by
    simpa [prefixWord, tailWord_3873787, baseEnd_3873787] using wordTrace_append hprefix tailTrace_3873787
  have hstable : (prefixWord ++ tailWord_3873787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873787).length < 2 ^ (prefixWord ++ tailWord_3873787).sum := by decide
  have hdescent : baseEnd_3873787 < baseStart_3873787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873789 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_3873789 : Nat := 118140960795 + 3873789 * 2 ^ 59
def prefixEnd_3873789 : Nat := 4983230072969 + 3 ^ 40 * 3873789 * 2
def baseEnd_3873789 : Nat := 1326077140733233010948183

theorem tailTrace_3873789 : CollatzResearch.WordTrace tailWord_3873789 prefixEnd_3873789 1326077140733233010948183 := by
  unfold tailWord_3873789
  simp only [CollatzResearch.WordTrace]
  refine ⟨141288692162931518334400421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94192461441954345556266947 141288692162931518334400421)
  ·
    refine ⟨26491629780549659687700079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141288692162931518334400421 26491629780549659687700079)
    ·
      refine ⟨39737444670824489531550119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26491629780549659687700079 39737444670824489531550119)
      ·
        refine ⟨59606167006236734297325179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39737444670824489531550119 59606167006236734297325179)
        ·
          refine ⟨89409250509355101445987769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59606167006236734297325179 89409250509355101445987769)
          ·
            refine ⟨67056937882016326084490827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89409250509355101445987769 67056937882016326084490827)
            ·
              refine ⟨100585406823024489126736241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67056937882016326084490827 100585406823024489126736241)
              ·
                refine ⟨75439055117268366845052181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100585406823024489126736241 75439055117268366845052181)
                ·
                  refine ⟨3536205708621954695861821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75439055117268366845052181 3536205708621954695861821)
                  ·
                    refine ⟨1326077140733233010948183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3536205708621954695861821 1326077140733233010948183)
                    ·
                      rfl

theorem cell22_3873789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_3873789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873789 prefixEnd_3873789 := by exact prefixLift 3873789
  have htrace : WordTrace (prefixWord ++ tailWord_3873789) baseStart_3873789 baseEnd_3873789 := by
    simpa [prefixWord, tailWord_3873789, baseEnd_3873789] using wordTrace_append hprefix tailTrace_3873789
  have hstable : (prefixWord ++ tailWord_3873789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873789).length < 2 ^ (prefixWord ++ tailWord_3873789).sum := by decide
  have hdescent : baseEnd_3873789 < baseStart_3873789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873804 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_3873804 : Nat := 118140960795 + 3873804 * 2 ^ 59
def prefixEnd_3873804 : Nat := 4983230072969 + 3 ^ 40 * 3873804 * 2
def baseEnd_3873804 : Nat := 1326082275539777971823137

theorem tailTrace_3873804 : CollatzResearch.WordTrace tailWord_3873804 prefixEnd_3873804 1326082275539777971823137 := by
  unfold tailWord_3873804
  simp only [CollatzResearch.WordTrace]
  refine ⟨70644619628938587948098233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94192826171918117264130977 70644619628938587948098233)
  ·
    refine ⟨52983464721703940961073675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70644619628938587948098233 52983464721703940961073675)
    ·
      refine ⟨79475197082555911441610513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52983464721703940961073675 79475197082555911441610513)
      ·
        refine ⟨59606397811916933581207885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79475197082555911441610513 59606397811916933581207885)
        ·
          refine ⟨22352399179468850092952957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59606397811916933581207885 22352399179468850092952957)
          ·
            refine ⟨8382149692300818784857359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22352399179468850092952957 8382149692300818784857359)
            ·
              refine ⟨12573224538451228177286039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382149692300818784857359 12573224538451228177286039)
              ·
                refine ⟨18859836807676842265929059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12573224538451228177286039 18859836807676842265929059)
                ·
                  refine ⟨28289755211515263398893589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18859836807676842265929059 28289755211515263398893589)
                  ·
                    refine ⟨1326082275539777971823137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28289755211515263398893589 1326082275539777971823137)
                    ·
                      rfl

theorem cell22_3873804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_3873804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873804 prefixEnd_3873804 := by exact prefixLift 3873804
  have htrace : WordTrace (prefixWord ++ tailWord_3873804) baseStart_3873804 baseEnd_3873804 := by
    simpa [prefixWord, tailWord_3873804, baseEnd_3873804] using wordTrace_append hprefix tailTrace_3873804
  have hstable : (prefixWord ++ tailWord_3873804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873804).length < 2 ^ (prefixWord ++ tailWord_3873804).sum := by decide
  have hdescent : baseEnd_3873804 < baseStart_3873804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873823 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 2, 3]
def baseStart_3873823 : Nat := 118140960795 + 3873823 * 2 ^ 59
def prefixEnd_3873823 : Nat := 4983230072969 + 3 ^ 40 * 3873823 * 2
def baseEnd_3873823 : Nat := 1326088779628068255598079

theorem tailTrace_3873823 : CollatzResearch.WordTrace tailWord_3873823 prefixEnd_3873823 1326088779628068255598079 := by
  unfold tailWord_3873823
  simp only [CollatzResearch.WordTrace]
  refine ⟨141289932244808342141138123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94193288163205561427425415 141289932244808342141138123)
  ·
    refine ⟨211934898367212513211707185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141289932244808342141138123 211934898367212513211707185)
    ·
      refine ⟨158951173775409384908780389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211934898367212513211707185 158951173775409384908780389)
      ·
        refine ⟨29803345082889259670396323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158951173775409384908780389 29803345082889259670396323)
        ·
          refine ⟨44705017624333889505594485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29803345082889259670396323 44705017624333889505594485)
          ·
            refine ⟨4191095402281302141149483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44705017624333889505594485 4191095402281302141149483)
            ·
              refine ⟨6286643103421953211724225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191095402281302141149483 6286643103421953211724225)
              ·
                refine ⟨4714982327566464908793169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286643103421953211724225 4714982327566464908793169)
                ·
                  refine ⟨3536236745674848681594877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4714982327566464908793169 3536236745674848681594877)
                  ·
                    refine ⟨1326088779628068255598079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3536236745674848681594877 1326088779628068255598079)
                    ·
                      rfl

theorem cell22_3873823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_3873823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873823 prefixEnd_3873823 := by exact prefixLift 3873823
  have htrace : WordTrace (prefixWord ++ tailWord_3873823) baseStart_3873823 baseEnd_3873823 := by
    simpa [prefixWord, tailWord_3873823, baseEnd_3873823] using wordTrace_append hprefix tailTrace_3873823
  have hstable : (prefixWord ++ tailWord_3873823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873823).length < 2 ^ (prefixWord ++ tailWord_3873823).sum := by decide
  have hdescent : baseEnd_3873823 < baseStart_3873823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873898 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_3873898 : Nat := 118140960795 + 3873898 * 2 ^ 59
def prefixEnd_3873898 : Nat := 4983230072969 + 3 ^ 40 * 3873898 * 2
def baseEnd_3873898 : Nat := 442038151220264353324283

theorem tailTrace_3873898 : CollatzResearch.WordTrace tailWord_3873898 prefixEnd_3873898 442038151220264353324283 := by
  unfold tailWord_3873898
  simp only [CollatzResearch.WordTrace]
  refine ⟨35323166929884157487529587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94195111813024419966745565 35323166929884157487529587)
  ·
    refine ⟨52984750394826236231294381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35323166929884157487529587 52984750394826236231294381)
    ·
      refine ⟨19869281398059838586735393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52984750394826236231294381 19869281398059838586735393)
      ·
        refine ⟨14901961048544878940051545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19869281398059838586735393 14901961048544878940051545)
        ·
          refine ⟨11176470786408659205038659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14901961048544878940051545 11176470786408659205038659)
          ·
            refine ⟨16764706179612988807557989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11176470786408659205038659 16764706179612988807557989)
            ·
              refine ⟨3143382408677435401417123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16764706179612988807557989 3143382408677435401417123)
              ·
                refine ⟨4715073613016153102125685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143382408677435401417123 4715073613016153102125685)
                ·
                  refine ⟨442038151220264353324283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4715073613016153102125685 442038151220264353324283)
                  ·
                    rfl

theorem cell22_3873898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_3873898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873898 prefixEnd_3873898 := by exact prefixLift 3873898
  have htrace : WordTrace (prefixWord ++ tailWord_3873898) baseStart_3873898 baseEnd_3873898 := by
    simpa [prefixWord, tailWord_3873898, baseEnd_3873898] using wordTrace_append hprefix tailTrace_3873898
  have hstable : (prefixWord ++ tailWord_3873898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873898).length < 2 ^ (prefixWord ++ tailWord_3873898).sum := by decide
  have hdescent : baseEnd_3873898 < baseStart_3873898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873943 : List Nat := [1, 1, 3, 3, 3, 2, 1, 4, 4]
def baseStart_3873943 : Nat := 118140960795 + 3873943 * 2 ^ 59
def prefixEnd_3873943 : Nat := 4983230072969 + 3 ^ 40 * 3873943 * 2
def baseEnd_3873943 : Nat := 442043286026809314199237

theorem tailTrace_3873943 : CollatzResearch.WordTrace tailWord_3873943 prefixEnd_3873943 442043286026809314199237 := by
  unfold tailWord_3873943
  simp only [CollatzResearch.WordTrace]
  refine ⟨141294309004373602635506483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94196206002915735090337655 141294309004373602635506483)
  ·
    refine ⟨211941463506560403953259725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141294309004373602635506483 211941463506560403953259725)
    ·
      refine ⟨79478048814960151482472397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211941463506560403953259725 79478048814960151482472397)
      ·
        refine ⟨29804268305610056805927149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79478048814960151482472397 29804268305610056805927149)
        ·
          refine ⟨11176600614603771302222681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29804268305610056805927149 11176600614603771302222681)
          ·
            refine ⟨8382450460952828476667011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11176600614603771302222681 8382450460952828476667011)
            ·
              refine ⟨12573675691429242715000517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382450460952828476667011 12573675691429242715000517)
              ·
                refine ⟨2357564192142983009062597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12573675691429242715000517 2357564192142983009062597)
                ·
                  refine ⟨442043286026809314199237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2357564192142983009062597 442043286026809314199237)
                  ·
                    rfl

theorem cell22_3873943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 4].length) (baseStart_3873943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3873943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3873943 prefixEnd_3873943 := by exact prefixLift 3873943
  have htrace : WordTrace (prefixWord ++ tailWord_3873943) baseStart_3873943 baseEnd_3873943 := by
    simpa [prefixWord, tailWord_3873943, baseEnd_3873943] using wordTrace_append hprefix tailTrace_3873943
  have hstable : (prefixWord ++ tailWord_3873943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873943).length < 2 ^ (prefixWord ++ tailWord_3873943).sum := by decide
  have hdescent : baseEnd_3873943 < baseStart_3873943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874108 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_3874108 : Nat := 118140960795 + 3874108 * 2 ^ 59
def prefixEnd_3874108 : Nat := 4983230072969 + 3 ^ 40 * 3874108 * 2
def baseEnd_3874108 : Nat := 1326186340952422512222205

theorem tailTrace_3874108 : CollatzResearch.WordTrace tailWord_3874108 prefixEnd_3874108 1326186340952422512222205 := by
  unfold tailWord_3874108
  simp only [CollatzResearch.WordTrace]
  refine ⟨70650163524387917907631489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94200218032517223876841985 70650163524387917907631489)
  ·
    refine ⟨52987622643290938430723617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70650163524387917907631489 52987622643290938430723617)
    ·
      refine ⟨39740716982468203823042713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52987622643290938430723617 39740716982468203823042713)
      ·
        refine ⟨29805537736851152867282035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39740716982468203823042713 29805537736851152867282035)
        ·
          refine ⟨44708306605276729300923053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29805537736851152867282035 44708306605276729300923053)
          ·
            refine ⟨16765614976978773487846145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44708306605276729300923053 16765614976978773487846145)
            ·
              refine ⟨12574211232734080115884609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16765614976978773487846145 12574211232734080115884609)
              ·
                refine ⟨9430658424550560086913457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12574211232734080115884609 9430658424550560086913457)
                ·
                  refine ⟨7072993818412920065185093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9430658424550560086913457 7072993818412920065185093)
                  ·
                    refine ⟨1326186340952422512222205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7072993818412920065185093 1326186340952422512222205)
                    ·
                      rfl

theorem cell22_3874108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_3874108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874108 prefixEnd_3874108 := by exact prefixLift 3874108
  have htrace : WordTrace (prefixWord ++ tailWord_3874108) baseStart_3874108 baseEnd_3874108 := by
    simpa [prefixWord, tailWord_3874108, baseEnd_3874108] using wordTrace_append hprefix tailTrace_3874108
  have hstable : (prefixWord ++ tailWord_3874108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874108).length < 2 ^ (prefixWord ++ tailWord_3874108).sum := by decide
  have hdescent : baseEnd_3874108 < baseStart_3874108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874136 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_3874136 : Nat := 118140960795 + 3874136 * 2 ^ 59
def prefixEnd_3874136 : Nat := 4983230072969 + 3 ^ 40 * 3874136 * 2
def baseEnd_3874136 : Nat := 1326195925924639772522119

theorem tailTrace_3874136 : CollatzResearch.WordTrace tailWord_3874136 prefixEnd_3874136 1326195925924639772522119 := by
  unfold tailWord_3874136
  simp only [CollatzResearch.WordTrace]
  refine ⟨70650674146337198298641131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94200898861782931064854841 70650674146337198298641131)
  ·
    refine ⟨105976011219505797447961697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70650674146337198298641131 105976011219505797447961697)
    ·
      refine ⟨79482008414629348085971273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105976011219505797447961697 79482008414629348085971273)
      ·
        refine ⟨59611506310972011064478455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79482008414629348085971273 59611506310972011064478455)
        ·
          refine ⟨89417259466458016596717683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59611506310972011064478455 89417259466458016596717683)
          ·
            refine ⟨134125889199687024895076525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89417259466458016596717683 134125889199687024895076525)
            ·
              refine ⟨50297208449882634335653697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134125889199687024895076525 50297208449882634335653697)
              ·
                refine ⟨37722906337411975751740273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50297208449882634335653697 37722906337411975751740273)
                ·
                  refine ⟨28292179753058981813805205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37722906337411975751740273 28292179753058981813805205)
                  ·
                    refine ⟨1326195925924639772522119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28292179753058981813805205 1326195925924639772522119)
                    ·
                      rfl

theorem cell22_3874136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_3874136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874136 prefixEnd_3874136 := by exact prefixLift 3874136
  have htrace : WordTrace (prefixWord ++ tailWord_3874136) baseStart_3874136 baseEnd_3874136 := by
    simpa [prefixWord, tailWord_3874136, baseEnd_3874136] using wordTrace_append hprefix tailTrace_3874136
  have hstable : (prefixWord ++ tailWord_3874136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874136).length < 2 ^ (prefixWord ++ tailWord_3874136).sum := by decide
  have hdescent : baseEnd_3874136 < baseStart_3874136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874138 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_3874138 : Nat := 118140960795 + 3874138 * 2 ^ 59
def prefixEnd_3874138 : Nat := 4983230072969 + 3 ^ 40 * 3874138 * 2
def baseEnd_3874138 : Nat := 1326196610565512433972113

theorem tailTrace_3874138 : CollatzResearch.WordTrace tailWord_3874138 prefixEnd_3874138 1326196610565512433972113 := by
  unfold tailWord_3874138
  simp only [CollatzResearch.WordTrace]
  refine ⟨35325355309666787734713767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94200947492444767292570045 35325355309666787734713767)
  ·
    refine ⟨52988032964500181602070651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35325355309666787734713767 52988032964500181602070651)
    ·
      refine ⟨79482049446750272403105977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52988032964500181602070651 79482049446750272403105977)
      ·
        refine ⟨59611537085062704302329483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79482049446750272403105977 59611537085062704302329483)
        ·
          refine ⟨89417305627594056453494225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59611537085062704302329483 89417305627594056453494225)
          ·
            refine ⟨67062979220695542340120669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89417305627594056453494225 67062979220695542340120669)
            ·
              refine ⟨25148617207760828377545251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67062979220695542340120669 25148617207760828377545251)
              ·
                refine ⟨37722925811641242566317877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25148617207760828377545251 37722925811641242566317877)
                ·
                  refine ⟨3536524294841366490592301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37722925811641242566317877 3536524294841366490592301)
                  ·
                    refine ⟨1326196610565512433972113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3536524294841366490592301 1326196610565512433972113)
                    ·
                      rfl

theorem cell22_3874138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_3874138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874138 prefixEnd_3874138 := by exact prefixLift 3874138
  have htrace : WordTrace (prefixWord ++ tailWord_3874138) baseStart_3874138 baseEnd_3874138 := by
    simpa [prefixWord, tailWord_3874138, baseEnd_3874138] using wordTrace_append hprefix tailTrace_3874138
  have hstable : (prefixWord ++ tailWord_3874138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874138).length < 2 ^ (prefixWord ++ tailWord_3874138).sum := by decide
  have hdescent : baseEnd_3874138 < baseStart_3874138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874183 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 2, 5]
def baseStart_3874183 : Nat := 118140960795 + 3874183 * 2 ^ 59
def prefixEnd_3874183 : Nat := 4983230072969 + 3 ^ 40 * 3874183 * 2
def baseEnd_3874183 : Nat := 1326212014985147316596975

theorem tailTrace_3874183 : CollatzResearch.WordTrace tailWord_3874183 prefixEnd_3874183 1326212014985147316596975 := by
  unfold tailWord_3874183
  simp only [CollatzResearch.WordTrace]
  refine ⟨141303062523504123624243203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94202041682336082416162135 141303062523504123624243203)
  ·
    refine ⟨211954593785256185436364805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141303062523504123624243203 211954593785256185436364805)
    ·
      refine ⟨39741486334735534769318401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211954593785256185436364805 39741486334735534769318401)
      ·
        refine ⟨29806114751051651076988801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39741486334735534769318401 29806114751051651076988801)
        ·
          refine ⟨22354586063288738307741601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29806114751051651076988801 22354586063288738307741601)
          ·
            refine ⟨16765939547466553730806201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22354586063288738307741601 16765939547466553730806201)
            ·
              refine ⟨12574454660599915298104651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16765939547466553730806201 12574454660599915298104651)
              ·
                refine ⟨18861681990899872947156977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12574454660599915298104651 18861681990899872947156977)
                ·
                  refine ⟨14146261493174904710367733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18861681990899872947156977 14146261493174904710367733)
                  ·
                    refine ⟨1326212014985147316596975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14146261493174904710367733 1326212014985147316596975)
                    ·
                      rfl

theorem cell22_3874183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_3874183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874183 prefixEnd_3874183 := by exact prefixLift 3874183
  have htrace : WordTrace (prefixWord ++ tailWord_3874183) baseStart_3874183 baseEnd_3874183 := by
    simpa [prefixWord, tailWord_3874183, baseEnd_3874183] using wordTrace_append hprefix tailTrace_3874183
  have hstable : (prefixWord ++ tailWord_3874183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874183).length < 2 ^ (prefixWord ++ tailWord_3874183).sum := by decide
  have hdescent : baseEnd_3874183 < baseStart_3874183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874215 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3874215 : Nat := 118140960795 + 3874215 * 2 ^ 59
def prefixEnd_3874215 : Nat := 4983230072969 + 3 ^ 40 * 3874215 * 2
def baseEnd_3874215 : Nat := 1326222969239109899796877

theorem tailTrace_3874215 : CollatzResearch.WordTrace tailWord_3874215 prefixEnd_3874215 1326222969239109899796877 := by
  unfold tailWord_3874215
  simp only [CollatzResearch.WordTrace]
  refine ⟨141304229659388193089408099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94202819772925462059605399 141304229659388193089408099)
  ·
    refine ⟨211956344489082289634112149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141304229659388193089408099 211956344489082289634112149)
    ·
      refine ⟨9935453647925732326599007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 211956344489082289634112149 9935453647925732326599007)
      ·
        refine ⟨14903180471888598489898511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9935453647925732326599007 14903180471888598489898511)
        ·
          refine ⟨22354770707832897734847767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14903180471888598489898511 22354770707832897734847767)
          ·
            refine ⟨33532156061749346602271651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22354770707832897734847767 33532156061749346602271651)
            ·
              refine ⟨50298234092624019903407477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33532156061749346602271651 50298234092624019903407477)
              ·
                refine ⟨4715459446183501865944451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50298234092624019903407477 4715459446183501865944451)
                ·
                  refine ⟨7073189169275252798916677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715459446183501865944451 7073189169275252798916677)
                  ·
                    refine ⟨1326222969239109899796877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7073189169275252798916677 1326222969239109899796877)
                    ·
                      rfl

theorem cell22_3874215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3874215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874215 prefixEnd_3874215 := by exact prefixLift 3874215
  have htrace : WordTrace (prefixWord ++ tailWord_3874215) baseStart_3874215 baseEnd_3874215 := by
    simpa [prefixWord, tailWord_3874215, baseEnd_3874215] using wordTrace_append hprefix tailTrace_3874215
  have hstable : (prefixWord ++ tailWord_3874215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874215).length < 2 ^ (prefixWord ++ tailWord_3874215).sum := by decide
  have hdescent : baseEnd_3874215 < baseStart_3874215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874262 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3874262 : Nat := 118140960795 + 3874262 * 2 ^ 59
def prefixEnd_3874262 : Nat := 4983230072969 + 3 ^ 40 * 3874262 * 2
def baseEnd_3874262 : Nat := 1326239058299617443871733

theorem tailTrace_3874262 : CollatzResearch.WordTrace tailWord_3874262 prefixEnd_3874262 1326239058299617443871733 := by
  unfold tailWord_3874262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8831621493138620007273065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94203962593478613410912693 8831621493138620007273065)
  ·
    refine ⟨6623716119853965005454799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8831621493138620007273065 6623716119853965005454799)
    ·
      refine ⟨9935574179780947508182199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6623716119853965005454799 9935574179780947508182199)
      ·
        refine ⟨14903361269671421262273299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9935574179780947508182199 14903361269671421262273299)
        ·
          refine ⟨22355041904507131893409949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14903361269671421262273299 22355041904507131893409949)
          ·
            refine ⟨8383140714190174460028731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22355041904507131893409949 8383140714190174460028731)
            ·
              refine ⟨12574711071285261690043097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383140714190174460028731 12574711071285261690043097)
              ·
                refine ⟨9431033303463946267532323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12574711071285261690043097 9431033303463946267532323)
                ·
                  refine ⟨14146549955195919401298485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9431033303463946267532323 14146549955195919401298485)
                  ·
                    refine ⟨1326239058299617443871733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14146549955195919401298485 1326239058299617443871733)
                    ·
                      rfl

theorem cell22_3874262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3874262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874262 prefixEnd_3874262 := by exact prefixLift 3874262
  have htrace : WordTrace (prefixWord ++ tailWord_3874262) baseStart_3874262 baseEnd_3874262 := by
    simpa [prefixWord, tailWord_3874262, baseEnd_3874262] using wordTrace_append hprefix tailTrace_3874262
  have hstable : (prefixWord ++ tailWord_3874262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874262).length < 2 ^ (prefixWord ++ tailWord_3874262).sum := by decide
  have hdescent : baseEnd_3874262 < baseStart_3874262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874288 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_3874288 : Nat := 118140960795 + 3874288 * 2 ^ 59
def prefixEnd_3874288 : Nat := 4983230072969 + 3 ^ 40 * 3874288 * 2
def baseEnd_3874288 : Nat := 1326247958630962042721653

theorem tailTrace_3874288 : CollatzResearch.WordTrace tailWord_3874288 prefixEnd_3874288 1326247958630962042721653 := by
  unfold tailWord_3874288
  simp only [CollatzResearch.WordTrace]
  refine ⟨70653446094061863278407759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94204594792082484371210345 70653446094061863278407759)
  ·
    refine ⟨105980169141092794917611639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70653446094061863278407759 105980169141092794917611639)
    ·
      refine ⟨158970253711639192376417459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105980169141092794917611639 158970253711639192376417459)
      ·
        refine ⟨238455380567458788564626189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158970253711639192376417459 238455380567458788564626189)
        ·
          refine ⟨89420767712797045711734821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238455380567458788564626189 89420767712797045711734821)
          ·
            refine ⟨16766393946149446070950279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89420767712797045711734821 16766393946149446070950279)
            ·
              refine ⟨25149590919224169106425419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16766393946149446070950279 25149590919224169106425419)
              ·
                refine ⟨37724386378836253659638129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25149590919224169106425419 37724386378836253659638129)
                ·
                  refine ⟨28293289784127190244728597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37724386378836253659638129 28293289784127190244728597)
                  ·
                    refine ⟨1326247958630962042721653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28293289784127190244728597 1326247958630962042721653)
                    ·
                      rfl

theorem cell22_3874288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_3874288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874288 prefixEnd_3874288 := by exact prefixLift 3874288
  have htrace : WordTrace (prefixWord ++ tailWord_3874288) baseStart_3874288 baseEnd_3874288 := by
    simpa [prefixWord, tailWord_3874288, baseEnd_3874288] using wordTrace_append hprefix tailTrace_3874288
  have hstable : (prefixWord ++ tailWord_3874288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874288).length < 2 ^ (prefixWord ++ tailWord_3874288).sum := by decide
  have hdescent : baseEnd_3874288 < baseStart_3874288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874337 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 5]
def baseStart_3874337 : Nat := 118140960795 + 3874337 * 2 ^ 59
def prefixEnd_3874337 : Nat := 4983230072969 + 3 ^ 40 * 3874337 * 2
def baseEnd_3874337 : Nat := 442088244110780749415501

theorem tailTrace_3874337 : CollatzResearch.WordTrace tailWord_3874337 prefixEnd_3874337 442088244110780749415501 := by
  unfold tailWord_3874337
  simp only [CollatzResearch.WordTrace]
  refine ⟨141308679364946207925349265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94205786243297471950232843 141308679364946207925349265)
  ·
    refine ⟨105981509523709655944011949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141308679364946207925349265 105981509523709655944011949)
    ·
      refine ⟨39743066071391120979004481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105981509523709655944011949 39743066071391120979004481)
      ·
        refine ⟨29807299553543340734253361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39743066071391120979004481 29807299553543340734253361)
        ·
          refine ⟨22355474665157505550690021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29807299553543340734253361 22355474665157505550690021)
          ·
            refine ⟨4191651499717032290754379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22355474665157505550690021 4191651499717032290754379)
            ·
              refine ⟨6287477249575548436131569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191651499717032290754379 6287477249575548436131569)
              ·
                refine ⟨4715607937181661327098677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6287477249575548436131569 4715607937181661327098677)
                ·
                  refine ⟨442088244110780749415501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4715607937181661327098677 442088244110780749415501)
                  ·
                    rfl

theorem cell22_3874337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_3874337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874337 prefixEnd_3874337 := by exact prefixLift 3874337
  have htrace : WordTrace (prefixWord ++ tailWord_3874337) baseStart_3874337 baseEnd_3874337 := by
    simpa [prefixWord, tailWord_3874337, baseEnd_3874337] using wordTrace_append hprefix tailTrace_3874337
  have hstable : (prefixWord ++ tailWord_3874337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874337).length < 2 ^ (prefixWord ++ tailWord_3874337).sum := by decide
  have hdescent : baseEnd_3874337 < baseStart_3874337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874367 : List Nat := [1, 1, 2, 2, 3, 4, 2, 2, 1, 4]
def baseStart_3874367 : Nat := 118140960795 + 3874367 * 2 ^ 59
def prefixEnd_3874367 : Nat := 4983230072969 + 3 ^ 40 * 3874367 * 2
def baseEnd_3874367 : Nat := 1326275001945432169996411

theorem tailTrace_3874367 : CollatzResearch.WordTrace tailWord_3874367 prefixEnd_3874367 1326275001945432169996411 := by
  unfold tailWord_3874367
  simp only [CollatzResearch.WordTrace]
  refine ⟨141309773554837523048941355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94206515703225015365960903 141309773554837523048941355)
  ·
    refine ⟨211964660332256284573412033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141309773554837523048941355 211964660332256284573412033)
    ·
      refine ⟨158973495249192213430059025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211964660332256284573412033 158973495249192213430059025)
      ·
        refine ⟨119230121436894160072544269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158973495249192213430059025 119230121436894160072544269)
        ·
          refine ⟨44711295538835310027204101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119230121436894160072544269 44711295538835310027204101)
          ·
            refine ⟨8383367913531620630100769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44711295538835310027204101 8383367913531620630100769)
            ·
              refine ⟨6287525935148715472575577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8383367913531620630100769 6287525935148715472575577)
              ·
                refine ⟨4715644451361536604431683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6287525935148715472575577 4715644451361536604431683)
                ·
                  refine ⟨7073466677042304906647525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715644451361536604431683 7073466677042304906647525)
                  ·
                    refine ⟨1326275001945432169996411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7073466677042304906647525 1326275001945432169996411)
                    ·
                      rfl

theorem cell22_3874367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_3874367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874367 prefixEnd_3874367 := by exact prefixLift 3874367
  have htrace : WordTrace (prefixWord ++ tailWord_3874367) baseStart_3874367 baseEnd_3874367 := by
    simpa [prefixWord, tailWord_3874367, baseEnd_3874367] using wordTrace_append hprefix tailTrace_3874367
  have hstable : (prefixWord ++ tailWord_3874367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874367).length < 2 ^ (prefixWord ++ tailWord_3874367).sum := by decide
  have hdescent : baseEnd_3874367 < baseStart_3874367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874410 : List Nat := [3, 1, 3, 2, 1, 2, 1, 9]
def baseStart_3874410 : Nat := 118140960795 + 3874410 * 2 ^ 59
def prefixEnd_3874410 : Nat := 4983230072969 + 3 ^ 40 * 3874410 * 2
def baseEnd_3874410 : Nat := 147365524636021599019031

theorem tailTrace_3874410 : CollatzResearch.WordTrace tailWord_3874410 prefixEnd_3874410 147365524636021599019031 := by
  unfold tailWord_3874410
  simp only [CollatzResearch.WordTrace]
  refine ⟨35327835473420435348189171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94207561262454494261837789 35327835473420435348189171)
  ·
    refine ⟨52991753210130653022283757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35327835473420435348189171 52991753210130653022283757)
    ·
      refine ⟨19871907453798994883356409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52991753210130653022283757 19871907453798994883356409)
      ·
        refine ⟨14903930590349246162517307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19871907453798994883356409 14903930590349246162517307)
        ·
          refine ⟨22355895885523869243775961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14903930590349246162517307 22355895885523869243775961)
          ·
            refine ⟨16766921914142901932831971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22355895885523869243775961 16766921914142901932831971)
            ·
              refine ⟨25150382871214352899247957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16766921914142901932831971 25150382871214352899247957)
              ·
                refine ⟨147365524636021599019031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25150382871214352899247957 147365524636021599019031)
                ·
                  rfl

theorem cell22_3874410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_3874410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874410 prefixEnd_3874410 := by exact prefixLift 3874410
  have htrace : WordTrace (prefixWord ++ tailWord_3874410) baseStart_3874410 baseEnd_3874410 := by
    simpa [prefixWord, tailWord_3874410, baseEnd_3874410] using wordTrace_append hprefix tailTrace_3874410
  have hstable : (prefixWord ++ tailWord_3874410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874410).length < 2 ^ (prefixWord ++ tailWord_3874410).sum := by decide
  have hdescent : baseEnd_3874410 < baseStart_3874410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874506 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_3874506 : Nat := 118140960795 + 3874506 * 2 ^ 59
def prefixEnd_3874506 : Nat := 4983230072969 + 3 ^ 40 * 3874506 * 2
def baseEnd_3874506 : Nat := 442107528162027380256995

theorem tailTrace_3874506 : CollatzResearch.WordTrace tailWord_3874506 prefixEnd_3874506 442107528162027380256995 := by
  unfold tailWord_3874506
  simp only [CollatzResearch.WordTrace]
  refine ⟨35328710825333487447062843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94209895534222633192167581 35328710825333487447062843)
  ·
    refine ⟨52993066238000231170594265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35328710825333487447062843 52993066238000231170594265)
    ·
      refine ⟨39744799678500173377945699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52993066238000231170594265 39744799678500173377945699)
      ·
        refine ⟨59617199517750260066918549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39744799678500173377945699 59617199517750260066918549)
        ·
          refine ⟨2794556227394543440636807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59617199517750260066918549 2794556227394543440636807)
          ·
            refine ⟨4191834341091815160955211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794556227394543440636807 4191834341091815160955211)
            ·
              refine ⟨6287751511637722741432817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191834341091815160955211 6287751511637722741432817)
              ·
                refine ⟨4715813633728292056074613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6287751511637722741432817 4715813633728292056074613)
                ·
                  refine ⟨442107528162027380256995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4715813633728292056074613 442107528162027380256995)
                  ·
                    rfl

theorem cell22_3874506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_3874506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874506 prefixEnd_3874506 := by exact prefixLift 3874506
  have htrace : WordTrace (prefixWord ++ tailWord_3874506) baseStart_3874506 baseEnd_3874506 := by
    simpa [prefixWord, tailWord_3874506, baseEnd_3874506] using wordTrace_append hprefix tailTrace_3874506
  have hstable : (prefixWord ++ tailWord_3874506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874506).length < 2 ^ (prefixWord ++ tailWord_3874506).sum := by decide
  have hdescent : baseEnd_3874506 < baseStart_3874506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874560 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_3874560 : Nat := 118140960795 + 3874560 * 2 ^ 59
def prefixEnd_3874560 : Nat := 4983230072969 + 3 ^ 40 * 3874560 * 2
def baseEnd_3874560 : Nat := 1326341069789643999920819

theorem tailTrace_3874560 : CollatzResearch.WordTrace tailWord_3874560 prefixEnd_3874560 1326341069789643999920819 := by
  unfold tailWord_3874560
  simp only [CollatzResearch.WordTrace]
  refine ⟨70658406421569158505358567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94211208562092211340478089 70658406421569158505358567)
  ·
    refine ⟨105987609632353737758037851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70658406421569158505358567 105987609632353737758037851)
    ·
      refine ⟨158981414448530606637056777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105987609632353737758037851 158981414448530606637056777)
      ·
        refine ⟨119236060836397954977792583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158981414448530606637056777 119236060836397954977792583)
        ·
          refine ⟨178854091254596932466688875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119236060836397954977792583 178854091254596932466688875)
          ·
            refine ⟨268281136881895398700033313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178854091254596932466688875 268281136881895398700033313)
            ·
              refine ⟨201210852661421549025024985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268281136881895398700033313 201210852661421549025024985)
              ·
                refine ⟨150908139496066161768768739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201210852661421549025024985 150908139496066161768768739)
                ·
                  refine ⟨226362209244099242653153109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150908139496066161768768739 226362209244099242653153109)
                  ·
                    refine ⟨1326341069789643999920819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 226362209244099242653153109 1326341069789643999920819)
                    ·
                      rfl

theorem cell22_3874560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_3874560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874560 prefixEnd_3874560 := by exact prefixLift 3874560
  have htrace : WordTrace (prefixWord ++ tailWord_3874560) baseStart_3874560 baseEnd_3874560 := by
    simpa [prefixWord, tailWord_3874560, baseEnd_3874560] using wordTrace_append hprefix tailTrace_3874560
  have hstable : (prefixWord ++ tailWord_3874560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874560).length < 2 ^ (prefixWord ++ tailWord_3874560).sum := by decide
  have hdescent : baseEnd_3874560 < baseStart_3874560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874564 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_3874564 : Nat := 118140960795 + 3874564 * 2 ^ 59
def prefixEnd_3874564 : Nat := 4983230072969 + 3 ^ 40 * 3874564 * 2
def baseEnd_3874564 : Nat := 1326342439071389322820807

theorem tailTrace_3874564 : CollatzResearch.WordTrace tailWord_3874564 prefixEnd_3874564 1326342439071389322820807 := by
  unfold tailWord_3874564
  simp only [CollatzResearch.WordTrace]
  refine ⟨70658479367561912846931373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94211305823415883795908497 70658479367561912846931373)
  ·
    refine ⟨26496929762835717317599265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70658479367561912846931373 26496929762835717317599265)
    ·
      refine ⟨19872697322126787988199449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26496929762835717317599265 19872697322126787988199449)
      ·
        refine ⟨14904522991595090991149587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19872697322126787988199449 14904522991595090991149587)
        ·
          refine ⟨22356784487392636486724381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14904522991595090991149587 22356784487392636486724381)
          ·
            refine ⟨8383794182772238682521643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22356784487392636486724381 8383794182772238682521643)
            ·
              refine ⟨12575691274158358023782465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383794182772238682521643 12575691274158358023782465)
              ·
                refine ⟨9431768455618768517836849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12575691274158358023782465 9431768455618768517836849)
                ·
                  refine ⟨7073826341714076388377637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9431768455618768517836849 7073826341714076388377637)
                  ·
                    refine ⟨1326342439071389322820807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7073826341714076388377637 1326342439071389322820807)
                    ·
                      rfl

theorem cell22_3874564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_3874564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874564 prefixEnd_3874564 := by exact prefixLift 3874564
  have htrace : WordTrace (prefixWord ++ tailWord_3874564) baseStart_3874564 baseEnd_3874564 := by
    simpa [prefixWord, tailWord_3874564, baseEnd_3874564] using wordTrace_append hprefix tailTrace_3874564
  have hstable : (prefixWord ++ tailWord_3874564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874564).length < 2 ^ (prefixWord ++ tailWord_3874564).sum := by decide
  have hdescent : baseEnd_3874564 < baseStart_3874564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874583 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 2, 3]
def baseStart_3874583 : Nat := 118140960795 + 3874583 * 2 ^ 59
def prefixEnd_3874583 : Nat := 4983230072969 + 3 ^ 40 * 3874583 * 2
def baseEnd_3874583 : Nat := 1326348943159679606595749

theorem tailTrace_3874583 : CollatzResearch.WordTrace tailWord_3874583 prefixEnd_3874583 1326348943159679606595749 := by
  unfold tailWord_3874583
  simp only [CollatzResearch.WordTrace]
  refine ⟨141317651722054991938804403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94211767814703327959202935 141317651722054991938804403)
  ·
    refine ⟨211976477583082487908206605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141317651722054991938804403 211976477583082487908206605)
    ·
      refine ⟨79491179093655932965577477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211976477583082487908206605 79491179093655932965577477)
      ·
        refine ⟨14904596080060487431045777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79491179093655932965577477 14904596080060487431045777)
        ·
          refine ⟨11178447060045365573284333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14904596080060487431045777 11178447060045365573284333)
          ·
            refine ⟨4191917647517012089981625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11178447060045365573284333 4191917647517012089981625)
            ·
              refine ⟨3143938235637759067486219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4191917647517012089981625 3143938235637759067486219)
              ·
                refine ⟨4715907353456638601229329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143938235637759067486219 4715907353456638601229329)
                ·
                  refine ⟨3536930515092478950921997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4715907353456638601229329 3536930515092478950921997)
                  ·
                    refine ⟨1326348943159679606595749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3536930515092478950921997 1326348943159679606595749)
                    ·
                      rfl

theorem cell22_3874583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_3874583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874583 prefixEnd_3874583 := by exact prefixLift 3874583
  have htrace : WordTrace (prefixWord ++ tailWord_3874583) baseStart_3874583 baseEnd_3874583 := by
    simpa [prefixWord, tailWord_3874583, baseEnd_3874583] using wordTrace_append hprefix tailTrace_3874583
  have hstable : (prefixWord ++ tailWord_3874583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874583).length < 2 ^ (prefixWord ++ tailWord_3874583).sum := by decide
  have hdescent : baseEnd_3874583 < baseStart_3874583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874594 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_3874594 : Nat := 118140960795 + 3874594 * 2 ^ 59
def prefixEnd_3874594 : Nat := 4983230072969 + 3 ^ 40 * 3874594 * 2
def baseEnd_3874594 : Nat := 1326352708684479244570715

theorem tailTrace_3874594 : CollatzResearch.WordTrace tailWord_3874594 prefixEnd_3874594 1326352708684479244570715 := by
  unfold tailWord_3874594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35329513231253785204363709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94212035283343427211636557 35329513231253785204363709)
  ·
    refine ⟨13248567461720169451636391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35329513231253785204363709 13248567461720169451636391)
    ·
      refine ⟨19872851192580254177454587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13248567461720169451636391 19872851192580254177454587)
      ·
        refine ⟨29809276788870381266181881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19872851192580254177454587 29809276788870381266181881)
        ·
          refine ⟨22356957591652785949636411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29809276788870381266181881 22356957591652785949636411)
          ·
            refine ⟨33535436387479178924454617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22356957591652785949636411 33535436387479178924454617)
            ·
              refine ⟨25151577290609384193340963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33535436387479178924454617 25151577290609384193340963)
              ·
                refine ⟨37727365935914076290011445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25151577290609384193340963 37727365935914076290011445)
                ·
                  refine ⟨3536940556491944652188573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37727365935914076290011445 3536940556491944652188573)
                  ·
                    refine ⟨1326352708684479244570715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3536940556491944652188573 1326352708684479244570715)
                    ·
                      rfl

theorem cell22_3874594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_3874594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874594 prefixEnd_3874594 := by exact prefixLift 3874594
  have htrace : WordTrace (prefixWord ++ tailWord_3874594) baseStart_3874594 baseEnd_3874594 := by
    simpa [prefixWord, tailWord_3874594, baseEnd_3874594] using wordTrace_append hprefix tailTrace_3874594
  have hstable : (prefixWord ++ tailWord_3874594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874594).length < 2 ^ (prefixWord ++ tailWord_3874594).sum := by decide
  have hdescent : baseEnd_3874594 < baseStart_3874594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874686 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_3874686 : Nat := 118140960795 + 3874686 * 2 ^ 59
def prefixEnd_3874686 : Nat := 4983230072969 + 3 ^ 40 * 3874686 * 2
def baseEnd_3874686 : Nat := 442128067388207223756811

theorem tailTrace_3874686 : CollatzResearch.WordTrace tailWord_3874686 prefixEnd_3874686 442128067388207223756811 := by
  unfold tailWord_3874686
  simp only [CollatzResearch.WordTrace]
  refine ⟨17665176055085230066225489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94214272293787893686535941 17665176055085230066225489)
  ·
    refine ⟨13248882041313922549669117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17665176055085230066225489 13248882041313922549669117)
    ·
      refine ⟨4968330765492720956125919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13248882041313922549669117 4968330765492720956125919)
      ·
        refine ⟨7452496148239081434188879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4968330765492720956125919 7452496148239081434188879)
        ·
          refine ⟨11178744222358622151283319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7452496148239081434188879 11178744222358622151283319)
          ·
            refine ⟨16768116333537933226924979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11178744222358622151283319 16768116333537933226924979)
            ·
              refine ⟨25152174500306899840387469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16768116333537933226924979 25152174500306899840387469)
              ·
                refine ⟨9432065437615087440145301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25152174500306899840387469 9432065437615087440145301)
                ·
                  refine ⟨442128067388207223756811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9432065437615087440145301 442128067388207223756811)
                  ·
                    rfl

theorem cell22_3874686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_3874686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874686 prefixEnd_3874686 := by exact prefixLift 3874686
  have htrace : WordTrace (prefixWord ++ tailWord_3874686) baseStart_3874686 baseEnd_3874686 := by
    simpa [prefixWord, tailWord_3874686, baseEnd_3874686] using wordTrace_append hprefix tailTrace_3874686
  have hstable : (prefixWord ++ tailWord_3874686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874686).length < 2 ^ (prefixWord ++ tailWord_3874686).sum := by decide
  have hdescent : baseEnd_3874686 < baseStart_3874686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874697 : List Nat := [1, 2, 1, 1, 5, 1, 2, 9]
def baseStart_3874697 : Nat := 118140960795 + 3874697 * 2 ^ 59
def prefixEnd_3874697 : Nat := 4983230072969 + 3 ^ 40 * 3874697 * 2
def baseEnd_3874697 : Nat := 147376440854380145471711

theorem tailTrace_3874697 : CollatzResearch.WordTrace tailWord_3874697 prefixEnd_3874697 147376440854380145471711 := by
  unfold tailWord_3874697
  simp only [CollatzResearch.WordTrace]
  refine ⟨141321809643641989408454345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94214539762427992938969563 141321809643641989408454345)
  ·
    refine ⟨105991357232731492056340759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141321809643641989408454345 105991357232731492056340759)
    ·
      refine ⟨158987035849097238084511139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105991357232731492056340759 158987035849097238084511139)
      ·
        refine ⟨238480553773645857126766709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158987035849097238084511139 238480553773645857126766709)
        ·
          refine ⟨22357551916279299105634379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238480553773645857126766709 22357551916279299105634379)
          ·
            refine ⟨33536327874418948658451569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22357551916279299105634379 33536327874418948658451569)
            ·
              refine ⟨25152245905814211493838677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33536327874418948658451569 25152245905814211493838677)
              ·
                refine ⟨147376440854380145471711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25152245905814211493838677 147376440854380145471711)
                ·
                  rfl

theorem cell22_3874697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 9].length) (baseStart_3874697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874697 prefixEnd_3874697 := by exact prefixLift 3874697
  have htrace : WordTrace (prefixWord ++ tailWord_3874697) baseStart_3874697 baseEnd_3874697 := by
    simpa [prefixWord, tailWord_3874697, baseEnd_3874697] using wordTrace_append hprefix tailTrace_3874697
  have hstable : (prefixWord ++ tailWord_3874697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874697).length < 2 ^ (prefixWord ++ tailWord_3874697).sum := by decide
  have hdescent : baseEnd_3874697 < baseStart_3874697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874714 : List Nat := [3, 1, 1, 4, 2, 2, 1, 8]
def baseStart_3874714 : Nat := 118140960795 + 3874714 * 2 ^ 59
def prefixEnd_3874714 : Nat := 4983230072969 + 3 ^ 40 * 3874714 * 2
def baseEnd_3874714 : Nat := 147377087459648770174483

theorem tailTrace_3874714 : CollatzResearch.WordTrace tailWord_3874714 prefixEnd_3874714 147377087459648770174483 := by
  unfold tailWord_3874714
  simp only [CollatzResearch.WordTrace]
  refine ⟨35330607421145100327955799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94214953123053600874548797 35330607421145100327955799)
  ·
    refine ⟨52995911131717650491933699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35330607421145100327955799 52995911131717650491933699)
    ·
      refine ⟨79493866697576475737900549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52995911131717650491933699 79493866697576475737900549)
      ·
        refine ⟨14905100005795589200856353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79493866697576475737900549 14905100005795589200856353)
        ·
          refine ⟨11178825004346691900642265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14905100005795589200856353 11178825004346691900642265)
          ·
            refine ⟨8384118753260018925481699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11178825004346691900642265 8384118753260018925481699)
            ·
              refine ⟨12576178129890028388222549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8384118753260018925481699 12576178129890028388222549)
              ·
                refine ⟨147377087459648770174483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12576178129890028388222549 147377087459648770174483)
                ·
                  rfl

theorem cell22_3874714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_3874714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874714 prefixEnd_3874714 := by exact prefixLift 3874714
  have htrace : WordTrace (prefixWord ++ tailWord_3874714) baseStart_3874714 baseEnd_3874714 := by
    simpa [prefixWord, tailWord_3874714, baseEnd_3874714] using wordTrace_append hprefix tailTrace_3874714
  have hstable : (prefixWord ++ tailWord_3874714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874714).length < 2 ^ (prefixWord ++ tailWord_3874714).sum := by decide
  have hdescent : baseEnd_3874714 < baseStart_3874714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874797 : List Nat := [1, 5, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_3874797 : Nat := 118140960795 + 3874797 * 2 ^ 59
def prefixEnd_3874797 : Nat := 4983230072969 + 3 ^ 40 * 3874797 * 2
def baseEnd_3874797 : Nat := 1326422199733054381745093

theorem tailTrace_3874797 : CollatzResearch.WordTrace tailWord_3874797 prefixEnd_3874797 1326422199733054381745093 := by
  unfold tailWord_3874797
  simp only [CollatzResearch.WordTrace]
  refine ⟨141325456943279706487094645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94216971295519804324729763 141325456943279706487094645)
  ·
    refine ⟨13249261588432472483165123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141325456943279706487094645 13249261588432472483165123)
    ·
      refine ⟨19873892382648708724747685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13249261588432472483165123 19873892382648708724747685)
      ·
        refine ⟨3726354821746632885890191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19873892382648708724747685 3726354821746632885890191)
        ·
          refine ⟨5589532232619949328835287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726354821746632885890191 5589532232619949328835287)
          ·
            refine ⟨8384298348929923993252931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589532232619949328835287 8384298348929923993252931)
            ·
              refine ⟨12576447523394885989879397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8384298348929923993252931 12576447523394885989879397)
              ·
                refine ⟨2358083910636541123102387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12576447523394885989879397 2358083910636541123102387)
                ·
                  refine ⟨3537125865954811684653581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358083910636541123102387 3537125865954811684653581)
                  ·
                    refine ⟨1326422199733054381745093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3537125865954811684653581 1326422199733054381745093)
                    ·
                      rfl

theorem cell22_3874797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_3874797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874797 prefixEnd_3874797 := by exact prefixLift 3874797
  have htrace : WordTrace (prefixWord ++ tailWord_3874797) baseStart_3874797 baseEnd_3874797 := by
    simpa [prefixWord, tailWord_3874797, baseEnd_3874797] using wordTrace_append hprefix tailTrace_3874797
  have hstable : (prefixWord ++ tailWord_3874797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874797).length < 2 ^ (prefixWord ++ tailWord_3874797).sum := by decide
  have hdescent : baseEnd_3874797 < baseStart_3874797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874853 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_3874853 : Nat := 118140960795 + 3874853 * 2 ^ 59
def prefixEnd_3874853 : Nat := 4983230072969 + 3 ^ 40 * 3874853 * 2
def baseEnd_3874853 : Nat := 1326441369677488902344921

theorem tailTrace_3874853 : CollatzResearch.WordTrace tailWord_3874853 prefixEnd_3874853 1326441369677488902344921 := by
  unfold tailWord_3874853
  simp only [CollatzResearch.WordTrace]
  refine ⟨141327499431076828051133213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94218332954051218700755475 141327499431076828051133213)
  ·
    refine ⟨52997812286653810519174955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141327499431076828051133213 52997812286653810519174955)
    ·
      refine ⟨79496718429980715778762433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52997812286653810519174955 79496718429980715778762433)
      ·
        refine ⟨59622538822485536834071825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79496718429980715778762433 59622538822485536834071825)
        ·
          refine ⟨44716904116864152625553869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59622538822485536834071825 44716904116864152625553869)
          ·
            refine ⟨16768839043824057234582701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44716904116864152625553869 16768839043824057234582701)
            ·
              refine ⟨6288314641434021462968513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16768839043824057234582701 6288314641434021462968513)
              ·
                refine ⟨4716235981075516097226385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6288314641434021462968513 4716235981075516097226385)
                ·
                  refine ⟨3537176985806637072919789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4716235981075516097226385 3537176985806637072919789)
                  ·
                    refine ⟨1326441369677488902344921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3537176985806637072919789 1326441369677488902344921)
                    ·
                      rfl

theorem cell22_3874853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_3874853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874853 prefixEnd_3874853 := by exact prefixLift 3874853
  have htrace : WordTrace (prefixWord ++ tailWord_3874853) baseStart_3874853 baseEnd_3874853 := by
    simpa [prefixWord, tailWord_3874853, baseEnd_3874853] using wordTrace_append hprefix tailTrace_3874853
  have hstable : (prefixWord ++ tailWord_3874853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874853).length < 2 ^ (prefixWord ++ tailWord_3874853).sum := by decide
  have hdescent : baseEnd_3874853 < baseStart_3874853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874879 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 2, 6]
def baseStart_3874879 : Nat := 118140960795 + 3874879 * 2 ^ 59
def prefixEnd_3874879 : Nat := 4983230072969 + 3 ^ 40 * 3874879 * 2
def baseEnd_3874879 : Nat := 1326450270008833501194841

theorem tailTrace_3874879 : CollatzResearch.WordTrace tailWord_3874879 prefixEnd_3874879 1326450270008833501194841 := by
  unfold tailWord_3874879
  simp only [CollatzResearch.WordTrace]
  refine ⟨141328447728982634491579691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94218965152655089661053127 141328447728982634491579691)
  ·
    refine ⟨211992671593473951737369537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141328447728982634491579691 211992671593473951737369537)
    ·
      refine ⟨158994503695105463803027153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211992671593473951737369537 158994503695105463803027153)
      ·
        refine ⟨119245877771329097852270365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158994503695105463803027153 119245877771329097852270365)
        ·
          refine ⟨44717204164248411694601387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119245877771329097852270365 44717204164248411694601387)
          ·
            refine ⟨67075806246372617541902081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44717204164248411694601387 67075806246372617541902081)
            ·
              refine ⟨50306854684779463156426561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67075806246372617541902081 50306854684779463156426561)
              ·
                refine ⟨37730141013584597367319921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50306854684779463156426561 37730141013584597367319921)
                ·
                  refine ⟨28297605760188448025489941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37730141013584597367319921 28297605760188448025489941)
                  ·
                    refine ⟨1326450270008833501194841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28297605760188448025489941 1326450270008833501194841)
                    ·
                      rfl

theorem cell22_3874879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_3874879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874879 prefixEnd_3874879 := by exact prefixLift 3874879
  have htrace : WordTrace (prefixWord ++ tailWord_3874879) baseStart_3874879 baseEnd_3874879 := by
    simpa [prefixWord, tailWord_3874879, baseEnd_3874879] using wordTrace_append hprefix tailTrace_3874879
  have hstable : (prefixWord ++ tailWord_3874879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874879).length < 2 ^ (prefixWord ++ tailWord_3874879).sum := by decide
  have hdescent : baseEnd_3874879 < baseStart_3874879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874926 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_3874926 : Nat := 118140960795 + 3874926 * 2 ^ 59
def prefixEnd_3874926 : Nat := 4983230072969 + 3 ^ 40 * 3874926 * 2
def baseEnd_3874926 : Nat := 1326466359069341045269697

theorem tailTrace_3874926 : CollatzResearch.WordTrace tailWord_3874926 prefixEnd_3874926 1326466359069341045269697 := by
  unfold tailWord_3874926
  simp only [CollatzResearch.WordTrace]
  refine ⟨17666270244976545189817579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94220107973208241012360421 17666270244976545189817579)
  ·
    refine ⟨26499405367464817784726369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17666270244976545189817579 26499405367464817784726369)
    ·
      refine ⟨19874554025598613338544777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26499405367464817784726369 19874554025598613338544777)
      ·
        refine ⟨14905915519198960003908583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19874554025598613338544777 14905915519198960003908583)
        ·
          refine ⟨22358873278798440005862875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14905915519198960003908583 22358873278798440005862875)
          ·
            refine ⟨33538309918197660008794313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22358873278798440005862875 33538309918197660008794313)
            ·
              refine ⟨25153732438648245006595735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33538309918197660008794313 25153732438648245006595735)
              ·
                refine ⟨37730598657972367509893603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25153732438648245006595735 37730598657972367509893603)
                ·
                  refine ⟨56595897986958551264840405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37730598657972367509893603 56595897986958551264840405)
                  ·
                    refine ⟨1326466359069341045269697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56595897986958551264840405 1326466359069341045269697)
                    ·
                      rfl

theorem cell22_3874926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_3874926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874926 prefixEnd_3874926 := by exact prefixLift 3874926
  have htrace : WordTrace (prefixWord ++ tailWord_3874926) baseStart_3874926 baseEnd_3874926 := by
    simpa [prefixWord, tailWord_3874926, baseEnd_3874926] using wordTrace_append hprefix tailTrace_3874926
  have hstable : (prefixWord ++ tailWord_3874926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874926).length < 2 ^ (prefixWord ++ tailWord_3874926).sum := by decide
  have hdescent : baseEnd_3874926 < baseStart_3874926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874928 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 5]
def baseStart_3874928 : Nat := 118140960795 + 3874928 * 2 ^ 59
def prefixEnd_3874928 : Nat := 4983230072969 + 3 ^ 40 * 3874928 * 2
def baseEnd_3874928 : Nat := 442155681236737902239897

theorem tailTrace_3874928 : CollatzResearch.WordTrace tailWord_3874928 prefixEnd_3874928 442155681236737902239897 := by
  unfold tailWord_3874928
  simp only [CollatzResearch.WordTrace]
  refine ⟨70665117452902557930056719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94220156603870077240075625 70665117452902557930056719)
  ·
    refine ⟨105997676179353836895085079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70665117452902557930056719 105997676179353836895085079)
    ·
      refine ⟨158996514269030755342627619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105997676179353836895085079 158996514269030755342627619)
      ·
        refine ⟨238494771403546133013941429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158996514269030755342627619 238494771403546133013941429)
        ·
          refine ⟨22358884819082449970057009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238494771403546133013941429 22358884819082449970057009)
          ·
            refine ⟨16769163614311837477542757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22358884819082449970057009 16769163614311837477542757)
            ·
              refine ⟨3144218177683469527039267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16769163614311837477542757 3144218177683469527039267)
              ·
                refine ⟨4716327266525204290558901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144218177683469527039267 4716327266525204290558901)
                ·
                  refine ⟨442155681236737902239897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4716327266525204290558901 442155681236737902239897)
                  ·
                    rfl

theorem cell22_3874928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 5].length) (baseStart_3874928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3874928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3874928 prefixEnd_3874928 := by exact prefixLift 3874928
  have htrace : WordTrace (prefixWord ++ tailWord_3874928) baseStart_3874928 baseEnd_3874928 := by
    simpa [prefixWord, tailWord_3874928, baseEnd_3874928] using wordTrace_append hprefix tailTrace_3874928
  have hstable : (prefixWord ++ tailWord_3874928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874928).length < 2 ^ (prefixWord ++ tailWord_3874928).sum := by decide
  have hdescent : baseEnd_3874928 < baseStart_3874928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875009 : List Nat := [1, 2, 6, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3875009 : Nat := 118140960795 + 3875009 * 2 ^ 59
def prefixEnd_3875009 : Nat := 4983230072969 + 3 ^ 40 * 3875009 * 2
def baseEnd_3875009 : Nat := 1326494771665556495444443

theorem tailTrace_3875009 : CollatzResearch.WordTrace tailWord_3875009 prefixEnd_3875009 1326494771665556495444443 := by
  unfold tailWord_3875009
  simp only [CollatzResearch.WordTrace]
  refine ⟨141333189218511666693812081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94222126145674444462541387 141333189218511666693812081)
  ·
    refine ⟨105999891913883750020359061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141333189218511666693812081 105999891913883750020359061)
    ·
      refine ⟨4968744933463300782204331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105999891913883750020359061 4968744933463300782204331)
      ·
        refine ⟨7453117400194951173306497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4968744933463300782204331 7453117400194951173306497)
        ·
          refine ⟨5589838050146213379979873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7453117400194951173306497 5589838050146213379979873)
          ·
            refine ⟨4192378537609660034984905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5589838050146213379979873 4192378537609660034984905)
            ·
              refine ⟨3144283903207245026238679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4192378537609660034984905 3144283903207245026238679)
              ·
                refine ⟨4716425854810867539358019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144283903207245026238679 4716425854810867539358019)
                ·
                  refine ⟨7074638782216301309037029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716425854810867539358019 7074638782216301309037029)
                  ·
                    refine ⟨1326494771665556495444443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7074638782216301309037029 1326494771665556495444443)
                    ·
                      rfl

theorem cell22_3875009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3875009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875009 prefixEnd_3875009 := by exact prefixLift 3875009
  have htrace : WordTrace (prefixWord ++ tailWord_3875009) baseStart_3875009 baseEnd_3875009 := by
    simpa [prefixWord, tailWord_3875009, baseEnd_3875009] using wordTrace_append hprefix tailTrace_3875009
  have hstable : (prefixWord ++ tailWord_3875009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875009).length < 2 ^ (prefixWord ++ tailWord_3875009).sum := by decide
  have hdescent : baseEnd_3875009 < baseStart_3875009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875022 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_3875022 : Nat := 118140960795 + 3875022 * 2 ^ 59
def prefixEnd_3875022 : Nat := 4983230072969 + 3 ^ 40 * 3875022 * 2
def baseEnd_3875022 : Nat := 1326499221831228794869403

theorem tailTrace_3875022 : CollatzResearch.WordTrace tailWord_3875022 prefixEnd_3875022 1326499221831228794869403 := by
  unfold tailWord_3875022
  simp only [CollatzResearch.WordTrace]
  refine ⟨17666707920933071239254415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94222442244976379942690213 17666707920933071239254415)
  ·
    refine ⟨26500061881399606858881623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17666707920933071239254415 26500061881399606858881623)
    ·
      refine ⟨39750092822099410288322435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26500061881399606858881623 39750092822099410288322435)
      ·
        refine ⟨59625139233149115432483653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39750092822099410288322435 59625139233149115432483653)
        ·
          refine ⟨11179713606215459143590685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59625139233149115432483653 11179713606215459143590685)
          ·
            refine ⟨4192392602330797178846507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11179713606215459143590685 4192392602330797178846507)
            ·
              refine ⟨6288588903496195768269761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192392602330797178846507 6288588903496195768269761)
              ·
                refine ⟨4716441677622146826202321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6288588903496195768269761 4716441677622146826202321)
                ·
                  refine ⟨3537331258216610119651741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4716441677622146826202321 3537331258216610119651741)
                  ·
                    refine ⟨1326499221831228794869403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3537331258216610119651741 1326499221831228794869403)
                    ·
                      rfl

theorem cell22_3875022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_3875022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875022 prefixEnd_3875022 := by exact prefixLift 3875022
  have htrace : WordTrace (prefixWord ++ tailWord_3875022) baseStart_3875022 baseEnd_3875022 := by
    simpa [prefixWord, tailWord_3875022, baseEnd_3875022] using wordTrace_append hprefix tailTrace_3875022
  have hstable : (prefixWord ++ tailWord_3875022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875022).length < 2 ^ (prefixWord ++ tailWord_3875022).sum := by decide
  have hdescent : baseEnd_3875022 < baseStart_3875022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875033 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 3, 3]
def baseStart_3875033 : Nat := 118140960795 + 3875033 * 2 ^ 59
def prefixEnd_3875033 : Nat := 4983230072969 + 3 ^ 40 * 3875033 * 2
def baseEnd_3875033 : Nat := 1326502987356028432844369

theorem tailTrace_3875033 : CollatzResearch.WordTrace tailWord_3875033 prefixEnd_3875033 1326502987356028432844369 := by
  unfold tailWord_3875033
  simp only [CollatzResearch.WordTrace]
  refine ⟨141334064570424718792685753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94222709713616479195123835 141334064570424718792685753)
  ·
    refine ⟨106000548427818539094514315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141334064570424718792685753 106000548427818539094514315)
    ·
      refine ⟨159000822641727808641771473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106000548427818539094514315 159000822641727808641771473)
      ·
        refine ⟨119250616981295856481328605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159000822641727808641771473 119250616981295856481328605)
        ·
          refine ⟨44718981367985946180498227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119250616981295856481328605 44718981367985946180498227)
          ·
            refine ⟨67078472051978919270747341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44718981367985946180498227 67078472051978919270747341)
            ·
              refine ⟨25154427019492094726530253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67078472051978919270747341 25154427019492094726530253)
              ·
                refine ⟨9432910132309535522448845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25154427019492094726530253 9432910132309535522448845)
                ·
                  refine ⟨3537341299616075820918317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9432910132309535522448845 3537341299616075820918317)
                  ·
                    refine ⟨1326502987356028432844369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3537341299616075820918317 1326502987356028432844369)
                    ·
                      rfl

theorem cell22_3875033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_3875033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875033 prefixEnd_3875033 := by exact prefixLift 3875033
  have htrace : WordTrace (prefixWord ++ tailWord_3875033) baseStart_3875033 baseEnd_3875033 := by
    simpa [prefixWord, tailWord_3875033, baseEnd_3875033] using wordTrace_append hprefix tailTrace_3875033
  have hstable : (prefixWord ++ tailWord_3875033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875033).length < 2 ^ (prefixWord ++ tailWord_3875033).sum := by decide
  have hdescent : baseEnd_3875033 < baseStart_3875033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875123 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 1, 5]
def baseStart_3875123 : Nat := 118140960795 + 3875123 * 2 ^ 59
def prefixEnd_3875123 : Nat := 4983230072969 + 3 ^ 40 * 3875123 * 2
def baseEnd_3875123 : Nat := 1326533796195298198094093

theorem tailTrace_3875123 : CollatzResearch.WordTrace tailWord_3875123 prefixEnd_3875123 1326533796195298198094093 := by
  unfold tailWord_3875123
  simp only [CollatzResearch.WordTrace]
  refine ⟨141337347140098664163462023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94224898093399109442308015 141337347140098664163462023)
  ·
    refine ⟨212006020710147996245193035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141337347140098664163462023 212006020710147996245193035)
    ·
      refine ⟨318009031065221994367789553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212006020710147996245193035 318009031065221994367789553)
      ·
        refine ⟨238506773298916495775842165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318009031065221994367789553 238506773298916495775842165)
        ·
          refine ⟨22360009996773421478985203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238506773298916495775842165 22360009996773421478985203)
          ·
            refine ⟨33540014995160132218477805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22360009996773421478985203 33540014995160132218477805)
            ·
              refine ⟨12577505623185049581929177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33540014995160132218477805 12577505623185049581929177)
              ·
                refine ⟨9433129217388787186446883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577505623185049581929177 9433129217388787186446883)
                ·
                  refine ⟨14149693826083180779670325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433129217388787186446883 14149693826083180779670325)
                  ·
                    refine ⟨1326533796195298198094093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14149693826083180779670325 1326533796195298198094093)
                    ·
                      rfl

theorem cell22_3875123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 5].length) (baseStart_3875123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875123 prefixEnd_3875123 := by exact prefixLift 3875123
  have htrace : WordTrace (prefixWord ++ tailWord_3875123) baseStart_3875123 baseEnd_3875123 := by
    simpa [prefixWord, tailWord_3875123, baseEnd_3875123] using wordTrace_append hprefix tailTrace_3875123
  have hstable : (prefixWord ++ tailWord_3875123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875123).length < 2 ^ (prefixWord ++ tailWord_3875123).sum := by decide
  have hdescent : baseEnd_3875123 < baseStart_3875123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875125 : List Nat := [1, 3, 3, 1, 2, 1, 2, 5, 4]
def baseStart_3875125 : Nat := 118140960795 + 3875125 * 2 ^ 59
def prefixEnd_3875125 : Nat := 4983230072969 + 3 ^ 40 * 3875125 * 2
def baseEnd_3875125 : Nat := 442178160278723619848029

theorem tailTrace_3875125 : CollatzResearch.WordTrace tailWord_3875125 prefixEnd_3875125 442178160278723619848029 := by
  unfold tailWord_3875125
  simp only [CollatzResearch.WordTrace]
  refine ⟨141337420086091418505034829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94224946724060945670023219 141337420086091418505034829)
  ·
    refine ⟨53001532532284281939388061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141337420086091418505034829 53001532532284281939388061)
    ·
      refine ⟨19875574699606605727270523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53001532532284281939388061 19875574699606605727270523)
      ·
        refine ⟨29813362049409908590905785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19875574699606605727270523 29813362049409908590905785)
        ·
          refine ⟨22360021537057431443179339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29813362049409908590905785 22360021537057431443179339)
          ·
            refine ⟨33540032305586147164769009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22360021537057431443179339 33540032305586147164769009)
            ·
              refine ⟨25155024229189610373576757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33540032305586147164769009 25155024229189610373576757)
              ·
                refine ⟨2358283521486525972522821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25155024229189610373576757 2358283521486525972522821)
                ·
                  refine ⟨442178160278723619848029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2358283521486525972522821 442178160278723619848029)
                  ·
                    rfl

theorem cell22_3875125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_3875125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875125 prefixEnd_3875125 := by exact prefixLift 3875125
  have htrace : WordTrace (prefixWord ++ tailWord_3875125) baseStart_3875125 baseEnd_3875125 := by
    simpa [prefixWord, tailWord_3875125, baseEnd_3875125] using wordTrace_append hprefix tailTrace_3875125
  have hstable : (prefixWord ++ tailWord_3875125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875125).length < 2 ^ (prefixWord ++ tailWord_3875125).sum := by decide
  have hdescent : baseEnd_3875125 < baseStart_3875125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875153 : List Nat := [1, 2, 2, 1, 4, 2, 3, 7]
def baseStart_3875153 : Nat := 118140960795 + 3875153 * 2 ^ 59
def prefixEnd_3875153 : Nat := 4983230072969 + 3 ^ 40 * 3875153 * 2
def baseEnd_3875153 : Nat := 147393785089820902204889

theorem tailTrace_3875153 : CollatzResearch.WordTrace tailWord_3875153 prefixEnd_3875153 147393785089820902204889 := by
  unfold tailWord_3875153
  simp only [CollatzResearch.WordTrace]
  refine ⟨141338441329989979287054113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94225627553326652858036075 141338441329989979287054113)
  ·
    refine ⟨106003830997492484465290585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141338441329989979287054113 106003830997492484465290585)
    ·
      refine ⟨79502873248119363348967939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106003830997492484465290585 79502873248119363348967939)
      ·
        refine ⟨119254309872179045023451909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79502873248119363348967939 119254309872179045023451909)
        ·
          refine ⟨22360183101033570941897233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119254309872179045023451909 22360183101033570941897233)
          ·
            refine ⟨16770137325775178206422925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22360183101033570941897233 16770137325775178206422925)
            ·
              refine ⟨6288801497165691827408597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16770137325775178206422925 6288801497165691827408597)
              ·
                refine ⟨147393785089820902204889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6288801497165691827408597 147393785089820902204889)
                ·
                  rfl

theorem cell22_3875153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 7].length) (baseStart_3875153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875153 prefixEnd_3875153 := by exact prefixLift 3875153
  have htrace : WordTrace (prefixWord ++ tailWord_3875153) baseStart_3875153 baseEnd_3875153 := by
    simpa [prefixWord, tailWord_3875153, baseEnd_3875153] using wordTrace_append hprefix tailTrace_3875153
  have hstable : (prefixWord ++ tailWord_3875153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875153).length < 2 ^ (prefixWord ++ tailWord_3875153).sum := by decide
  have hdescent : baseEnd_3875153 < baseStart_3875153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875273 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_3875273 : Nat := 118140960795 + 3875273 * 2 ^ 59
def prefixEnd_3875273 : Nat := 4983230072969 + 3 ^ 40 * 3875273 * 2
def baseEnd_3875273 : Nat := 1326585144260747806843633

theorem tailTrace_3875273 : CollatzResearch.WordTrace tailWord_3875273 prefixEnd_3875273 1326585144260747806843633 := by
  unfold tailWord_3875273
  simp only [CollatzResearch.WordTrace]
  refine ⟨141342818089555239781422473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94228545393036826520948315 141342818089555239781422473)
  ·
    refine ⟨106007113567166429836066855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141342818089555239781422473 106007113567166429836066855)
    ·
      refine ⟨159010670350749644754100283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106007113567166429836066855 159010670350749644754100283)
      ·
        refine ⟨238516005526124467131150425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159010670350749644754100283 238516005526124467131150425)
        ·
          refine ⟨178887004144593350348362819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238516005526124467131150425 178887004144593350348362819)
          ·
            refine ⟨268330506216890025522544229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178887004144593350348362819 268330506216890025522544229)
            ·
              refine ⟨50311969915666879785477043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 268330506216890025522544229 50311969915666879785477043)
              ·
                refine ⟨75467954873500319678215565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50311969915666879785477043 75467954873500319678215565)
                ·
                  refine ⟨28300483077562619879330837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75467954873500319678215565 28300483077562619879330837)
                  ·
                    refine ⟨1326585144260747806843633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28300483077562619879330837 1326585144260747806843633)
                    ·
                      rfl

theorem cell22_3875273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_3875273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875273 prefixEnd_3875273 := by exact prefixLift 3875273
  have htrace : WordTrace (prefixWord ++ tailWord_3875273) baseStart_3875273 baseEnd_3875273 := by
    simpa [prefixWord, tailWord_3875273, baseEnd_3875273] using wordTrace_append hprefix tailTrace_3875273
  have hstable : (prefixWord ++ tailWord_3875273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875273).length < 2 ^ (prefixWord ++ tailWord_3875273).sum := by decide
  have hdescent : baseEnd_3875273 < baseStart_3875273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875309 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_3875309 : Nat := 118140960795 + 3875309 * 2 ^ 59
def prefixEnd_3875309 : Nat := 4983230072969 + 3 ^ 40 * 3875309 * 2
def baseEnd_3875309 : Nat := 1326597467796455712943523

theorem tailTrace_3875309 : CollatzResearch.WordTrace tailWord_3875309 prefixEnd_3875309 1326597467796455712943523 := by
  unfold tailWord_3875309
  simp only [CollatzResearch.WordTrace]
  refine ⟨141344131117424817929732981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94229420744949878619821987 141344131117424817929732981)
  ·
    refine ⟨13251012292258576680912467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141344131117424817929732981 13251012292258576680912467)
    ·
      refine ⟨19876518438387865021368701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13251012292258576680912467 19876518438387865021368701)
      ·
        refine ⟨7453694414395449383013263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19876518438387865021368701 7453694414395449383013263)
        ·
          refine ⟨11180541621593174074519895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453694414395449383013263 11180541621593174074519895)
          ·
            refine ⟨16770812432389761111779843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180541621593174074519895 16770812432389761111779843)
            ·
              refine ⟨25156218648584641667669765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16770812432389761111779843 25156218648584641667669765)
              ·
                refine ⟨4716790996609620312688081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25156218648584641667669765 4716790996609620312688081)
                ·
                  refine ⟨3537593247457215234516061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4716790996609620312688081 3537593247457215234516061)
                  ·
                    refine ⟨1326597467796455712943523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3537593247457215234516061 1326597467796455712943523)
                    ·
                      rfl

theorem cell22_3875309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_3875309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875309 prefixEnd_3875309 := by exact prefixLift 3875309
  have htrace : WordTrace (prefixWord ++ tailWord_3875309) baseStart_3875309 baseEnd_3875309 := by
    simpa [prefixWord, tailWord_3875309, baseEnd_3875309] using wordTrace_append hprefix tailTrace_3875309
  have hstable : (prefixWord ++ tailWord_3875309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875309).length < 2 ^ (prefixWord ++ tailWord_3875309).sum := by decide
  have hdescent : baseEnd_3875309 < baseStart_3875309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875341 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3875341 : Nat := 118140960795 + 3875341 * 2 ^ 59
def prefixEnd_3875341 : Nat := 4983230072969 + 3 ^ 40 * 3875341 * 2
def baseEnd_3875341 : Nat := 1326608422050418296143425

theorem tailTrace_3875341 : CollatzResearch.WordTrace tailWord_3875341 prefixEnd_3875341 1326608422050418296143425 := by
  unfold tailWord_3875341
  simp only [CollatzResearch.WordTrace]
  refine ⟨141345298253308887394897877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94230198835539258263265251 141345298253308887394897877)
  ·
    refine ⟨3312780427811927048317919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 141345298253308887394897877 3312780427811927048317919)
    ·
      refine ⟨4969170641717890572476879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312780427811927048317919 4969170641717890572476879)
      ·
        refine ⟨7453755962576835858715319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969170641717890572476879 7453755962576835858715319)
        ·
          refine ⟨11180633943865253788072979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453755962576835858715319 11180633943865253788072979)
          ·
            refine ⟨16770950915797880682109469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180633943865253788072979 16770950915797880682109469)
            ·
              refine ⟨6289106593424205255791051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16770950915797880682109469 6289106593424205255791051)
              ·
                refine ⟨9433659890136307883686577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289106593424205255791051 9433659890136307883686577)
                ·
                  refine ⟨7075244917602230912764933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9433659890136307883686577 7075244917602230912764933)
                  ·
                    refine ⟨1326608422050418296143425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075244917602230912764933 1326608422050418296143425)
                    ·
                      rfl

theorem cell22_3875341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3875341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875341 prefixEnd_3875341 := by exact prefixLift 3875341
  have htrace : WordTrace (prefixWord ++ tailWord_3875341) baseStart_3875341 baseEnd_3875341 := by
    simpa [prefixWord, tailWord_3875341, baseEnd_3875341] using wordTrace_append hprefix tailTrace_3875341
  have hstable : (prefixWord ++ tailWord_3875341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875341).length < 2 ^ (prefixWord ++ tailWord_3875341).sum := by decide
  have hdescent : baseEnd_3875341 < baseStart_3875341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875354 : List Nat := [3, 1, 1, 3, 1, 1, 3, 5, 1, 3]
def baseStart_3875354 : Nat := 118140960795 + 3875354 * 2 ^ 59
def prefixEnd_3875354 : Nat := 4983230072969 + 3 ^ 40 * 3875354 * 2
def baseEnd_3875354 : Nat := 1326612872216090595568385

theorem tailTrace_3875354 : CollatzResearch.WordTrace tailWord_3875354 prefixEnd_3875354 1326612872216090595568385 := by
  unfold tailWord_3875354
  simp only [CollatzResearch.WordTrace]
  refine ⟨35336443100565447653780279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94230514934841193743414077 35336443100565447653780279)
  ·
    refine ⟨53004664650848171480670419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35336443100565447653780279 53004664650848171480670419)
    ·
      refine ⟨79506996976272257221005629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53004664650848171480670419 79506996976272257221005629)
      ·
        refine ⟨29815123866102096457877111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79506996976272257221005629 29815123866102096457877111)
        ·
          refine ⟨44722685799153144686815667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29815123866102096457877111 44722685799153144686815667)
          ·
            refine ⟨67084028698729717030223501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44722685799153144686815667 67084028698729717030223501)
            ·
              refine ⟨25156510762023643886333813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67084028698729717030223501 25156510762023643886333813)
              ·
                refine ⟨2358422883939716614343795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25156510762023643886333813 2358422883939716614343795)
                ·
                  refine ⟨3537634325909574921515693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358422883939716614343795 3537634325909574921515693)
                  ·
                    refine ⟨1326612872216090595568385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3537634325909574921515693 1326612872216090595568385)
                    ·
                      rfl

theorem cell22_3875354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_3875354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875354 prefixEnd_3875354 := by exact prefixLift 3875354
  have htrace : WordTrace (prefixWord ++ tailWord_3875354) baseStart_3875354 baseEnd_3875354 := by
    simpa [prefixWord, tailWord_3875354, baseEnd_3875354] using wordTrace_append hprefix tailTrace_3875354
  have hstable : (prefixWord ++ tailWord_3875354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875354).length < 2 ^ (prefixWord ++ tailWord_3875354).sum := by decide
  have hdescent : baseEnd_3875354 < baseStart_3875354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875365 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_3875365 : Nat := 118140960795 + 3875365 * 2 ^ 59
def prefixEnd_3875365 : Nat := 4983230072969 + 3 ^ 40 * 3875365 * 2
def baseEnd_3875365 : Nat := 1326616637740890233543351

theorem tailTrace_3875365 : CollatzResearch.WordTrace tailWord_3875365 prefixEnd_3875365 1326616637740890233543351 := by
  unfold tailWord_3875365
  simp only [CollatzResearch.WordTrace]
  refine ⟨141346173605221939493771549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94230782403481292995847699 141346173605221939493771549)
  ·
    refine ⟨53004815101958227310164331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141346173605221939493771549 53004815101958227310164331)
    ·
      refine ⟨79507222652937340965246497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53004815101958227310164331 79507222652937340965246497)
      ·
        refine ⟨59630416989703005723934873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79507222652937340965246497 59630416989703005723934873)
        ·
          refine ⟨44722812742277254292951155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59630416989703005723934873 44722812742277254292951155)
          ·
            refine ⟨67084219113415881439426733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44722812742277254292951155 67084219113415881439426733)
            ·
              refine ⟨25156582167530955539785025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67084219113415881439426733 25156582167530955539785025)
              ·
                refine ⟨18867436625648216654838769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25156582167530955539785025 18867436625648216654838769)
                ·
                  refine ⟨14150577469236162491129077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18867436625648216654838769 14150577469236162491129077)
                  ·
                    refine ⟨1326616637740890233543351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14150577469236162491129077 1326616637740890233543351)
                    ·
                      rfl

theorem cell22_3875365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_3875365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875365 prefixEnd_3875365 := by exact prefixLift 3875365
  have htrace : WordTrace (prefixWord ++ tailWord_3875365) baseStart_3875365 baseEnd_3875365 := by
    simpa [prefixWord, tailWord_3875365, baseEnd_3875365] using wordTrace_append hprefix tailTrace_3875365
  have hstable : (prefixWord ++ tailWord_3875365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875365).length < 2 ^ (prefixWord ++ tailWord_3875365).sum := by decide
  have hdescent : baseEnd_3875365 < baseStart_3875365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875397 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_3875397 : Nat := 118140960795 + 3875397 * 2 ^ 59
def prefixEnd_3875397 : Nat := 4983230072969 + 3 ^ 40 * 3875397 * 2
def baseEnd_3875397 : Nat := 1326627591994852816743253

theorem tailTrace_3875397 : CollatzResearch.WordTrace tailWord_3875397 prefixEnd_3875397 1326627591994852816743253 := by
  unfold tailWord_3875397
  simp only [CollatzResearch.WordTrace]
  refine ⟨141347340741106008958936445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94231560494070672639290963 141347340741106008958936445)
  ·
    refine ⟨53005252777914753359601167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141347340741106008958936445 53005252777914753359601167)
    ·
      refine ⟨79507879166872130039401751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53005252777914753359601167 79507879166872130039401751)
      ·
        refine ⟨119261818750308195059102627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79507879166872130039401751 119261818750308195059102627)
        ·
          refine ⟨178892728125462292588653941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119261818750308195059102627 178892728125462292588653941)
          ·
            refine ⟨16771193261762089930186307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178892728125462292588653941 16771193261762089930186307)
            ·
              refine ⟨25156789892643134895279461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16771193261762089930186307 25156789892643134895279461)
              ·
                refine ⟨4716898104870587792864899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25156789892643134895279461 4716898104870587792864899)
                ·
                  refine ⟨7075347157305881689297349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716898104870587792864899 7075347157305881689297349)
                  ·
                    refine ⟨1326627591994852816743253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075347157305881689297349 1326627591994852816743253)
                    ·
                      rfl

theorem cell22_3875397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_3875397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875397 prefixEnd_3875397 := by exact prefixLift 3875397
  have htrace : WordTrace (prefixWord ++ tailWord_3875397) baseStart_3875397 baseEnd_3875397 := by
    simpa [prefixWord, tailWord_3875397, baseEnd_3875397] using wordTrace_append hprefix tailTrace_3875397
  have hstable : (prefixWord ++ tailWord_3875397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875397).length < 2 ^ (prefixWord ++ tailWord_3875397).sum := by decide
  have hdescent : baseEnd_3875397 < baseStart_3875397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875422 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3875422 : Nat := 118140960795 + 3875422 * 2 ^ 59
def prefixEnd_3875422 : Nat := 4983230072969 + 3 ^ 40 * 3875422 * 2
def baseEnd_3875422 : Nat := 1326636150005761084868177

theorem tailTrace_3875422 : CollatzResearch.WordTrace tailWord_3875422 prefixEnd_3875422 1326636150005761084868177 := by
  unfold tailWord_3875422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668531570751929778574565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94232168377343625485731013 17668531570751929778574565)
  ·
    refine ⟨3312849669515986833482731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17668531570751929778574565 3312849669515986833482731)
    ·
      refine ⟨4969274504273980250224097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312849669515986833482731 4969274504273980250224097)
      ·
        refine ⟨3726955878205485187668073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4969274504273980250224097 3726955878205485187668073)
        ·
          refine ⟨2795216908654113890751055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726955878205485187668073 2795216908654113890751055)
          ·
            refine ⟨4192825362981170836126583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795216908654113890751055 4192825362981170836126583)
            ·
              refine ⟨6289238044471756254189875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192825362981170836126583 6289238044471756254189875)
              ·
                refine ⟨9433857066707634381284813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289238044471756254189875 9433857066707634381284813)
                ·
                  refine ⟨3537696400015362892981805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9433857066707634381284813 3537696400015362892981805)
                  ·
                    refine ⟨1326636150005761084868177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3537696400015362892981805 1326636150005761084868177)
                    ·
                      rfl

theorem cell22_3875422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3875422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875422 prefixEnd_3875422 := by exact prefixLift 3875422
  have htrace : WordTrace (prefixWord ++ tailWord_3875422) baseStart_3875422 baseEnd_3875422 := by
    simpa [prefixWord, tailWord_3875422, baseEnd_3875422] using wordTrace_append hprefix tailTrace_3875422
  have hstable : (prefixWord ++ tailWord_3875422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875422).length < 2 ^ (prefixWord ++ tailWord_3875422).sum := by decide
  have hdescent : baseEnd_3875422 < baseStart_3875422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875427 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 4, 3]
def baseStart_3875427 : Nat := 118140960795 + 3875427 * 2 ^ 59
def prefixEnd_3875427 : Nat := 4983230072969 + 3 ^ 40 * 3875427 * 2
def baseEnd_3875427 : Nat := 1326637861607942738493161

theorem tailTrace_3875427 : CollatzResearch.WordTrace tailWord_3875427 prefixEnd_3875427 1326637861607942738493161 := by
  unfold tailWord_3875427
  simp only [CollatzResearch.WordTrace]
  refine ⟨141348434930997324082528535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94232289953998216055019023 141348434930997324082528535)
  ·
    refine ⟨212022652396495986123792803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141348434930997324082528535 212022652396495986123792803)
    ·
      refine ⟨318033978594743979185689205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212022652396495986123792803 318033978594743979185689205)
      ·
        refine ⟨29815685493257248048658363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318033978594743979185689205 29815685493257248048658363)
        ·
          refine ⟨44723528239885872072987545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29815685493257248048658363 44723528239885872072987545)
          ·
            refine ⟨33542646179914404054740659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44723528239885872072987545 33542646179914404054740659)
            ·
              refine ⟨50313969269871606082110989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33542646179914404054740659 50313969269871606082110989)
              ·
                refine ⟨18867738476201852280791621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50313969269871606082110989 18867738476201852280791621)
                ·
                  refine ⟨3537700964287847302648429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18867738476201852280791621 3537700964287847302648429)
                  ·
                    refine ⟨1326637861607942738493161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3537700964287847302648429 1326637861607942738493161)
                    ·
                      rfl

theorem cell22_3875427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 3].length) (baseStart_3875427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875427 prefixEnd_3875427 := by exact prefixLift 3875427
  have htrace : WordTrace (prefixWord ++ tailWord_3875427) baseStart_3875427 baseEnd_3875427 := by
    simpa [prefixWord, tailWord_3875427, baseEnd_3875427] using wordTrace_append hprefix tailTrace_3875427
  have hstable : (prefixWord ++ tailWord_3875427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875427).length < 2 ^ (prefixWord ++ tailWord_3875427).sum := by decide
  have hdescent : baseEnd_3875427 < baseStart_3875427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875429 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 6]
def baseStart_3875429 : Nat := 118140960795 + 3875429 * 2 ^ 59
def prefixEnd_3875429 : Nat := 4983230072969 + 3 ^ 40 * 3875429 * 2
def baseEnd_3875429 : Nat := 442212848749605133314385

theorem tailTrace_3875429 : CollatzResearch.WordTrace tailWord_3875429 prefixEnd_3875429 442212848749605133314385 := by
  unfold tailWord_3875429
  simp only [CollatzResearch.WordTrace]
  refine ⟨141348507876990078424101341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94232338584660052282734227 141348507876990078424101341)
  ·
    refine ⟨53005690453871279409038003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141348507876990078424101341 53005690453871279409038003)
    ·
      refine ⟨79508535680806919113557005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53005690453871279409038003 79508535680806919113557005)
      ·
        refine ⟨29815700880302594667583877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79508535680806919113557005 29815700880302594667583877)
        ·
          refine ⟨5590443915056736500171977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29815700880302594667583877 5590443915056736500171977)
          ·
            refine ⟨4192832936292552375128983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5590443915056736500171977 4192832936292552375128983)
            ·
              refine ⟨6289249404438828562693475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192832936292552375128983 6289249404438828562693475)
              ·
                refine ⟨9433874106658242844040213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289249404438828562693475 9433874106658242844040213)
                ·
                  refine ⟨442212848749605133314385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9433874106658242844040213 442212848749605133314385)
                  ·
                    rfl

theorem cell22_3875429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_3875429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875429 prefixEnd_3875429 := by exact prefixLift 3875429
  have htrace : WordTrace (prefixWord ++ tailWord_3875429) baseStart_3875429 baseEnd_3875429 := by
    simpa [prefixWord, tailWord_3875429, baseEnd_3875429] using wordTrace_append hprefix tailTrace_3875429
  have hstable : (prefixWord ++ tailWord_3875429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875429).length < 2 ^ (prefixWord ++ tailWord_3875429).sum := by decide
  have hdescent : baseEnd_3875429 < baseStart_3875429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875510 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3875510 : Nat := 118140960795 + 3875510 * 2 ^ 59
def prefixEnd_3875510 : Nat := 4983230072969 + 3 ^ 40 * 3875510 * 2
def baseEnd_3875510 : Nat := 1326666274204158188667907

theorem tailTrace_3875510 : CollatzResearch.WordTrace tailWord_3875510 prefixEnd_3875510 1326666274204158188667907 := by
  unfold tailWord_3875510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834466386856039328612499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94234308126464419505199989 8834466386856039328612499)
  ·
    refine ⟨13251699580284058992918749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8834466386856039328612499 13251699580284058992918749)
    ·
      refine ⟨4969387342606522122344531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13251699580284058992918749 4969387342606522122344531)
      ·
        refine ⟨7454081013909783183516797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969387342606522122344531 7454081013909783183516797)
        ·
          refine ⟨2795280380216168693818799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7454081013909783183516797 2795280380216168693818799)
          ·
            refine ⟨4192920570324253040728199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795280380216168693818799 4192920570324253040728199)
            ·
              refine ⟨6289380855486379561092299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192920570324253040728199 6289380855486379561092299)
              ·
                refine ⟨9434071283229569341638449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289380855486379561092299 9434071283229569341638449)
                ·
                  refine ⟨7075553462422177006228837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9434071283229569341638449 7075553462422177006228837)
                  ·
                    refine ⟨1326666274204158188667907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075553462422177006228837 1326666274204158188667907)
                    ·
                      rfl

theorem cell22_3875510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3875510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875510 prefixEnd_3875510 := by exact prefixLift 3875510
  have htrace : WordTrace (prefixWord ++ tailWord_3875510) baseStart_3875510 baseEnd_3875510 := by
    simpa [prefixWord, tailWord_3875510, baseEnd_3875510] using wordTrace_append hprefix tailTrace_3875510
  have hstable : (prefixWord ++ tailWord_3875510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875510).length < 2 ^ (prefixWord ++ tailWord_3875510).sum := by decide
  have hdescent : baseEnd_3875510 < baseStart_3875510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875566 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_3875566 : Nat := 118140960795 + 3875566 * 2 ^ 59
def prefixEnd_3875566 : Nat := 4983230072969 + 3 ^ 40 * 3875566 * 2
def baseEnd_3875566 : Nat := 1326685444148592709267735

theorem tailTrace_3875566 : CollatzResearch.WordTrace tailWord_3875566 prefixEnd_3875566 1326685444148592709267735 := by
  unfold tailWord_3875566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17669188084686718852729819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94235669784995833881225701 17669188084686718852729819)
  ·
    refine ⟨26503782127030078279094729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17669188084686718852729819 26503782127030078279094729)
    ·
      refine ⟨19877836595272558709321047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26503782127030078279094729 19877836595272558709321047)
      ·
        refine ⟨29816754892908838063981571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19877836595272558709321047 29816754892908838063981571)
        ·
          refine ⟨44725132339363257095972357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29816754892908838063981571 44725132339363257095972357)
          ·
            refine ⟨8385962313630610705494817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44725132339363257095972357 8385962313630610705494817)
            ·
              refine ⟨6289471735222958029121113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8385962313630610705494817 6289471735222958029121113)
              ·
                refine ⟨4717103801417218521840835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6289471735222958029121113 4717103801417218521840835)
                ·
                  refine ⟨7075655702125827782761253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717103801417218521840835 7075655702125827782761253)
                  ·
                    refine ⟨1326685444148592709267735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075655702125827782761253 1326685444148592709267735)
                    ·
                      rfl

theorem cell22_3875566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_3875566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875566 prefixEnd_3875566 := by exact prefixLift 3875566
  have htrace : WordTrace (prefixWord ++ tailWord_3875566) baseStart_3875566 baseEnd_3875566 := by
    simpa [prefixWord, tailWord_3875566, baseEnd_3875566] using wordTrace_append hprefix tailTrace_3875566
  have hstable : (prefixWord ++ tailWord_3875566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875566).length < 2 ^ (prefixWord ++ tailWord_3875566).sum := by decide
  have hdescent : baseEnd_3875566 < baseStart_3875566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875577 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_3875577 : Nat := 118140960795 + 3875577 * 2 ^ 59
def prefixEnd_3875577 : Nat := 4983230072969 + 3 ^ 40 * 3875577 * 2
def baseEnd_3875577 : Nat := 1326689209673392347242701

theorem tailTrace_3875577 : CollatzResearch.WordTrace tailWord_3875577 prefixEnd_3875577 1326689209673392347242701 := by
  unfold tailWord_3875577
  simp only [CollatzResearch.WordTrace]
  refine ⟨141353905880453899700488985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94235937253635933133659323 141353905880453899700488985)
  ·
    refine ⟨106015429410340424775366739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141353905880453899700488985 106015429410340424775366739)
    ·
      refine ⟨159023144115510637163050109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106015429410340424775366739 159023144115510637163050109)
      ·
        refine ⟨59633679043316488936143791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159023144115510637163050109 59633679043316488936143791)
        ·
          refine ⟨89450518564974733404215687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59633679043316488936143791 89450518564974733404215687)
          ·
            refine ⟨134175777847462100106323531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89450518564974733404215687 134175777847462100106323531)
            ·
              refine ⟨201263666771193150159485297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134175777847462100106323531 201263666771193150159485297)
              ·
                refine ⟨150947750078394862619613973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201263666771193150159485297 150947750078394862619613973)
                ·
                  refine ⟨7075675784924759185294405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150947750078394862619613973 7075675784924759185294405)
                  ·
                    refine ⟨1326689209673392347242701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075675784924759185294405 1326689209673392347242701)
                    ·
                      rfl

theorem cell22_3875577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_3875577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875577 prefixEnd_3875577 := by exact prefixLift 3875577
  have htrace : WordTrace (prefixWord ++ tailWord_3875577) baseStart_3875577 baseEnd_3875577 := by
    simpa [prefixWord, tailWord_3875577, baseEnd_3875577] using wordTrace_append hprefix tailTrace_3875577
  have hstable : (prefixWord ++ tailWord_3875577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875577).length < 2 ^ (prefixWord ++ tailWord_3875577).sum := by decide
  have hdescent : baseEnd_3875577 < baseStart_3875577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875592 : List Nat := [2, 1, 3, 2, 2, 2, 10]
def baseStart_3875592 : Nat := 118140960795 + 3875592 * 2 ^ 59
def prefixEnd_3875592 : Nat := 4983230072969 + 3 ^ 40 * 3875592 * 2
def baseEnd_3875592 : Nat := 49136827573331011411765

theorem tailTrace_3875592 : CollatzResearch.WordTrace tailWord_3875592 prefixEnd_3875592 49136827573331011411765 := by
  unfold tailWord_3875592
  simp only [CollatzResearch.WordTrace]
  refine ⟨70677226487699778631142515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94236301983599704841523353 70677226487699778631142515)
  ·
    refine ⟨106015839731549667946713773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70677226487699778631142515 106015839731549667946713773)
    ·
      refine ⟨39755939899331125480017665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106015839731549667946713773 39755939899331125480017665)
      ·
        refine ⟨29816954924498344110013249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39755939899331125480017665 29816954924498344110013249)
        ·
          refine ⟨22362716193373758082509937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29816954924498344110013249 22362716193373758082509937)
          ·
            refine ⟨16772037145030318561882453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22362716193373758082509937 16772037145030318561882453)
            ·
              refine ⟨49136827573331011411765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16772037145030318561882453 49136827573331011411765)
              ·
                rfl

theorem cell22_3875592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 10].length) (baseStart_3875592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875592 prefixEnd_3875592 := by exact prefixLift 3875592
  have htrace : WordTrace (prefixWord ++ tailWord_3875592) baseStart_3875592 baseEnd_3875592 := by
    simpa [prefixWord, tailWord_3875592, baseEnd_3875592] using wordTrace_append hprefix tailTrace_3875592
  have hstable : (prefixWord ++ tailWord_3875592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875592).length < 2 ^ (prefixWord ++ tailWord_3875592).sum := by decide
  have hdescent : baseEnd_3875592 < baseStart_3875592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875594 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_3875594 : Nat := 118140960795 + 3875594 * 2 ^ 59
def prefixEnd_3875594 : Nat := 4983230072969 + 3 ^ 40 * 3875594 * 2
def baseEnd_3875594 : Nat := 1326695029120809969567649

theorem tailTrace_3875594 : CollatzResearch.WordTrace tailWord_3875594 prefixEnd_3875594 1326695029120809969567649 := by
  unfold tailWord_3875594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35338631480348077900964459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94236350614261541069238557 35338631480348077900964459)
  ·
    refine ⟨53007947220522116851446689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35338631480348077900964459 53007947220522116851446689)
    ·
      refine ⟨39755960415391587638585017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53007947220522116851446689 39755960415391587638585017)
      ·
        refine ⟨29816970311543690728938763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39755960415391587638585017 29816970311543690728938763)
        ·
          refine ⟨44725455467315536093408145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29816970311543690728938763 44725455467315536093408145)
          ·
            refine ⟨33544091600486652070056109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44725455467315536093408145 33544091600486652070056109)
            ·
              refine ⟨12579034350182494526271041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33544091600486652070056109 12579034350182494526271041)
              ·
                refine ⟨9434275762636870894703281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12579034350182494526271041 9434275762636870894703281)
                ·
                  refine ⟨7075706821977653171027461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9434275762636870894703281 7075706821977653171027461)
                  ·
                    refine ⟨1326695029120809969567649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7075706821977653171027461 1326695029120809969567649)
                    ·
                      rfl

theorem cell22_3875594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_3875594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875594 prefixEnd_3875594 := by exact prefixLift 3875594
  have htrace : WordTrace (prefixWord ++ tailWord_3875594) baseStart_3875594 baseEnd_3875594 := by
    simpa [prefixWord, tailWord_3875594, baseEnd_3875594] using wordTrace_append hprefix tailTrace_3875594
  have hstable : (prefixWord ++ tailWord_3875594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875594).length < 2 ^ (prefixWord ++ tailWord_3875594).sum := by decide
  have hdescent : baseEnd_3875594 < baseStart_3875594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875669 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_3875669 : Nat := 118140960795 + 3875669 * 2 ^ 59
def prefixEnd_3875669 : Nat := 4983230072969 + 3 ^ 40 * 3875669 * 2
def baseEnd_3875669 : Nat := 1326720703153534773942419

theorem tailTrace_3875669 : CollatzResearch.WordTrace tailWord_3875669 prefixEnd_3875669 1326720703153534773942419 := by
  unfold tailWord_3875669
  simp only [CollatzResearch.WordTrace]
  refine ⟨141357261396120599412838061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94238174264080399608558707 141357261396120599412838061)
  ·
    refine ⟨53008973023545224779814273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141357261396120599412838061 53008973023545224779814273)
    ·
      refine ⟨39756729767658918584860705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53008973023545224779814273 39756729767658918584860705)
      ·
        refine ⟨29817547325744188938645529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39756729767658918584860705 29817547325744188938645529)
        ·
          refine ⟨22363160494308141703984147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29817547325744188938645529 22363160494308141703984147)
          ·
            refine ⟨33544740741462212555976221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22363160494308141703984147 33544740741462212555976221)
            ·
              refine ⟨12579277778048329708491083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33544740741462212555976221 12579277778048329708491083)
              ·
                refine ⟨18868916667072494562736625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12579277778048329708491083 18868916667072494562736625)
                ·
                  refine ⟨14151687500304370922052469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18868916667072494562736625 14151687500304370922052469)
                  ·
                    refine ⟨1326720703153534773942419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14151687500304370922052469 1326720703153534773942419)
                    ·
                      rfl

theorem cell22_3875669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_3875669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875669 prefixEnd_3875669 := by exact prefixLift 3875669
  have htrace : WordTrace (prefixWord ++ tailWord_3875669) baseStart_3875669 baseEnd_3875669 := by
    simpa [prefixWord, tailWord_3875669, baseEnd_3875669] using wordTrace_append hprefix tailTrace_3875669
  have hstable : (prefixWord ++ tailWord_3875669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875669).length < 2 ^ (prefixWord ++ tailWord_3875669).sum := by decide
  have hdescent : baseEnd_3875669 < baseStart_3875669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875746 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_3875746 : Nat := 118140960795 + 3875746 * 2 ^ 59
def prefixEnd_3875746 : Nat := 4983230072969 + 3 ^ 40 * 3875746 * 2
def baseEnd_3875746 : Nat := 1326747061827132239767183

theorem tailTrace_3875746 : CollatzResearch.WordTrace tailWord_3875746 prefixEnd_3875746 1326747061827132239767183 := by
  unfold tailWord_3875746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35340017454210410390847773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94240046544561094375594061 35340017454210410390847773)
  ·
    refine ⟨13252506545328903896567915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35340017454210410390847773 13252506545328903896567915)
    ·
      refine ⟨19878759817993355844851873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13252506545328903896567915 19878759817993355844851873)
      ·
        refine ⟨14909069863495016883638905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19878759817993355844851873 14909069863495016883638905)
        ·
          refine ⟨11181802397621262662729179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14909069863495016883638905 11181802397621262662729179)
          ·
            refine ⟨16772703596431893994093769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11181802397621262662729179 16772703596431893994093769)
            ·
              refine ⟨12579527697323920495570327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16772703596431893994093769 12579527697323920495570327)
              ·
                refine ⟨18869291545985880743355491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12579527697323920495570327 18869291545985880743355491)
                ·
                  refine ⟨28303937318978821115033237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18869291545985880743355491 28303937318978821115033237)
                  ·
                    refine ⟨1326747061827132239767183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28303937318978821115033237 1326747061827132239767183)
                    ·
                      rfl

theorem cell22_3875746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_3875746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875746 prefixEnd_3875746 := by exact prefixLift 3875746
  have htrace : WordTrace (prefixWord ++ tailWord_3875746) baseStart_3875746 baseEnd_3875746 := by
    simpa [prefixWord, tailWord_3875746, baseEnd_3875746] using wordTrace_append hprefix tailTrace_3875746
  have hstable : (prefixWord ++ tailWord_3875746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875746).length < 2 ^ (prefixWord ++ tailWord_3875746).sum := by decide
  have hdescent : baseEnd_3875746 < baseStart_3875746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875761 : List Nat := [1, 2, 2, 4, 3, 2, 8]
def baseStart_3875761 : Nat := 118140960795 + 3875761 * 2 ^ 59
def prefixEnd_3875761 : Nat := 4983230072969 + 3 ^ 40 * 3875761 * 2
def baseEnd_3875761 : Nat := 49138970245691748171931

theorem tailTrace_3875761 : CollatzResearch.WordTrace tailWord_3875761 prefixEnd_3875761 49138970245691748171931 := by
  unfold tailWord_3875761
  simp only [CollatzResearch.WordTrace]
  refine ⟨141360616911787299125187137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94240411274524866083458091 141360616911787299125187137)
  ·
    refine ⟨106020462683840474343890353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141360616911787299125187137 106020462683840474343890353)
    ·
      refine ⟨79515347012880355757917765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106020462683840474343890353 79515347012880355757917765)
      ·
        refine ⟨14909127564915066704609581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79515347012880355757917765 14909127564915066704609581)
        ·
          refine ⟨5590922836843150014228593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14909127564915066704609581 5590922836843150014228593)
          ·
            refine ⟨4193192127632362510671445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5590922836843150014228593 4193192127632362510671445)
            ·
              refine ⟨49138970245691748171931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4193192127632362510671445 49138970245691748171931)
              ·
                rfl

theorem cell22_3875761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 8].length) (baseStart_3875761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875761 prefixEnd_3875761 := by exact prefixLift 3875761
  have htrace : WordTrace (prefixWord ++ tailWord_3875761) baseStart_3875761 baseEnd_3875761 := by
    simpa [prefixWord, tailWord_3875761, baseEnd_3875761] using wordTrace_append hprefix tailTrace_3875761
  have hstable : (prefixWord ++ tailWord_3875761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875761).length < 2 ^ (prefixWord ++ tailWord_3875761).sum := by decide
  have hdescent : baseEnd_3875761 < baseStart_3875761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875834 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_3875834 : Nat := 118140960795 + 3875834 * 2 ^ 59
def prefixEnd_3875834 : Nat := 4983230072969 + 3 ^ 40 * 3875834 * 2
def baseEnd_3875834 : Nat := 442259062008509781188971

theorem tailTrace_3875834 : CollatzResearch.WordTrace tailWord_3875834 prefixEnd_3875834 442259062008509781188971 := by
  unfold tailWord_3875834
  simp only [CollatzResearch.WordTrace]
  refine ⟨35340819860130708148148639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94242186293681888395063037 35340819860130708148148639)
  ·
    refine ⟨53011229790196062222222959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35340819860130708148148639 53011229790196062222222959)
    ·
      refine ⟨79516844685294093333334439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53011229790196062222222959 79516844685294093333334439)
      ·
        refine ⟨119275267027941140000001659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79516844685294093333334439 119275267027941140000001659)
        ·
          refine ⟨178912900541911710000002489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119275267027941140000001659 178912900541911710000002489)
          ·
            refine ⟨134184675406433782500001867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178912900541911710000002489 134184675406433782500001867)
            ·
              refine ⟨201277013109650673750002801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134184675406433782500001867 201277013109650673750002801)
              ·
                refine ⟨150957759832238005312502101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201277013109650673750002801 150957759832238005312502101)
                ·
                  refine ⟨442259062008509781188971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 150957759832238005312502101 442259062008509781188971)
                  ·
                    rfl

theorem cell22_3875834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_3875834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875834 prefixEnd_3875834 := by exact prefixLift 3875834
  have htrace : WordTrace (prefixWord ++ tailWord_3875834) baseStart_3875834 baseEnd_3875834 := by
    simpa [prefixWord, tailWord_3875834, baseEnd_3875834] using wordTrace_append hprefix tailTrace_3875834
  have hstable : (prefixWord ++ tailWord_3875834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875834).length < 2 ^ (prefixWord ++ tailWord_3875834).sum := by decide
  have hdescent : baseEnd_3875834 < baseStart_3875834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875836 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_3875836 : Nat := 118140960795 + 3875836 * 2 ^ 59
def prefixEnd_3875836 : Nat := 4983230072969 + 3 ^ 40 * 3875836 * 2
def baseEnd_3875836 : Nat := 1326777870666402005016907

theorem tailTrace_3875836 : CollatzResearch.WordTrace tailWord_3875836 prefixEnd_3875836 1326777870666402005016907 := by
  unfold tailWord_3875836
  simp only [CollatzResearch.WordTrace]
  refine ⟨70681676193257793467083681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94242234924343724622778241 70681676193257793467083681)
  ·
    refine ⟨53011257144943345100312761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70681676193257793467083681 53011257144943345100312761)
    ·
      refine ⟨39758442858707508825234571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53011257144943345100312761 39758442858707508825234571)
      ·
        refine ⟨59637664288061263237851857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39758442858707508825234571 59637664288061263237851857)
        ·
          refine ⟨44728248216045947428388893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59637664288061263237851857 44728248216045947428388893)
          ·
            refine ⟨16773093081017230285645835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44728248216045947428388893 16773093081017230285645835)
            ·
              refine ⟨25159639621525845428468753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16773093081017230285645835 25159639621525845428468753)
              ·
                refine ⟨18869729716144384071351565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25159639621525845428468753 18869729716144384071351565)
                ·
                  refine ⟨7076148643554144026756837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18869729716144384071351565 7076148643554144026756837)
                  ·
                    refine ⟨1326777870666402005016907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7076148643554144026756837 1326777870666402005016907)
                    ·
                      rfl

theorem cell22_3875836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_3875836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875836 prefixEnd_3875836 := by exact prefixLift 3875836
  have htrace : WordTrace (prefixWord ++ tailWord_3875836) baseStart_3875836 baseEnd_3875836 := by
    simpa [prefixWord, tailWord_3875836, baseEnd_3875836] using wordTrace_append hprefix tailTrace_3875836
  have hstable : (prefixWord ++ tailWord_3875836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875836).length < 2 ^ (prefixWord ++ tailWord_3875836).sum := by decide
  have hdescent : baseEnd_3875836 < baseStart_3875836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875851 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 6]
def baseStart_3875851 : Nat := 118140960795 + 3875851 * 2 ^ 59
def prefixEnd_3875851 : Nat := 4983230072969 + 3 ^ 40 * 3875851 * 2
def baseEnd_3875851 : Nat := 442261001824315655297287

theorem tailTrace_3875851 : CollatzResearch.WordTrace tailWord_3875851 prefixEnd_3875851 442261001824315655297287 := by
  unfold tailWord_3875851
  simp only [CollatzResearch.WordTrace]
  refine ⟨141363899481461244495963407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94242599654307496330642271 141363899481461244495963407)
  ·
    refine ⟨212045849222191866743945111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141363899481461244495963407 212045849222191866743945111)
    ·
      refine ⟨318068773833287800115917667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212045849222191866743945111 318068773833287800115917667)
      ·
        refine ⟨477103160749931700173876501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318068773833287800115917667 477103160749931700173876501)
        ·
          refine ⟨22364210660153048445650461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 477103160749931700173876501 22364210660153048445650461)
          ·
            refine ⟨8386578997557393167118923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22364210660153048445650461 8386578997557393167118923)
            ·
              refine ⟨12579868496336089750678385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386578997557393167118923 12579868496336089750678385)
              ·
                refine ⟨9434901372252067313008789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12579868496336089750678385 9434901372252067313008789)
                ·
                  refine ⟨442261001824315655297287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9434901372252067313008789 442261001824315655297287)
                  ·
                    rfl

theorem cell22_3875851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 6].length) (baseStart_3875851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875851 prefixEnd_3875851 := by exact prefixLift 3875851
  have htrace : WordTrace (prefixWord ++ tailWord_3875851) baseStart_3875851 baseEnd_3875851 := by
    simpa [prefixWord, tailWord_3875851, baseEnd_3875851] using wordTrace_append hprefix tailTrace_3875851
  have hstable : (prefixWord ++ tailWord_3875851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875851).length < 2 ^ (prefixWord ++ tailWord_3875851).sum := by decide
  have hdescent : baseEnd_3875851 < baseStart_3875851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875866 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_3875866 : Nat := 118140960795 + 3875866 * 2 ^ 59
def prefixEnd_3875866 : Nat := 4983230072969 + 3 ^ 40 * 3875866 * 2
def baseEnd_3875866 : Nat := 1326788140279491926766815

theorem tailTrace_3875866 : CollatzResearch.WordTrace tailWord_3875866 prefixEnd_3875866 1326788140279491926766815 := by
  unfold tailWord_3875866
  simp only [CollatzResearch.WordTrace]
  refine ⟨35341111644101725514439863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94242964384271268038506301 35341111644101725514439863)
  ·
    refine ⟨53011667466152588271659795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35341111644101725514439863 53011667466152588271659795)
    ·
      refine ⟨79517501199228882407489693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53011667466152588271659795 79517501199228882407489693)
      ·
        refine ⟨29819062949710830902808635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79517501199228882407489693 29819062949710830902808635)
        ·
          refine ⟨44728594424566246354212953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29819062949710830902808635 44728594424566246354212953)
          ·
            refine ⟨33546445818424684765659715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44728594424566246354212953 33546445818424684765659715)
            ·
              refine ⟨50319668727637027148489573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33546445818424684765659715 50319668727637027148489573)
              ·
                refine ⟨9434937886431942590341795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50319668727637027148489573 9434937886431942590341795)
                ·
                  refine ⟨14152406829647913885512693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9434937886431942590341795 14152406829647913885512693)
                  ·
                    refine ⟨1326788140279491926766815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14152406829647913885512693 1326788140279491926766815)
                    ·
                      rfl

theorem cell22_3875866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_3875866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875866 prefixEnd_3875866 := by exact prefixLift 3875866
  have htrace : WordTrace (prefixWord ++ tailWord_3875866) baseStart_3875866 baseEnd_3875866 := by
    simpa [prefixWord, tailWord_3875866, baseEnd_3875866] using wordTrace_append hprefix tailTrace_3875866
  have hstable : (prefixWord ++ tailWord_3875866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875866).length < 2 ^ (prefixWord ++ tailWord_3875866).sum := by decide
  have hdescent : baseEnd_3875866 < baseStart_3875866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875941 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 7]
def baseStart_3875941 : Nat := 118140960795 + 3875941 * 2 ^ 59
def prefixEnd_3875941 : Nat := 4983230072969 + 3 ^ 40 * 3875941 * 2
def baseEnd_3875941 : Nat := 442271271437405577047195

theorem tailTrace_3875941 : CollatzResearch.WordTrace tailWord_3875941 prefixEnd_3875941 442271271437405577047195 := by
  unfold tailWord_3875941
  simp only [CollatzResearch.WordTrace]
  refine ⟨141367182051135189866739677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94244788034090126577826451 141367182051135189866739677)
  ·
    refine ⟨53012693269175696200027379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141367182051135189866739677 53012693269175696200027379)
    ·
      refine ⟨79519039903763544300041069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53012693269175696200027379 79519039903763544300041069)
      ·
        refine ⟨29819639963911329112515401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79519039903763544300041069 29819639963911329112515401)
        ·
          refine ⟨22364729972933496834386551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29819639963911329112515401 22364729972933496834386551)
          ·
            refine ⟨33547094959400245251579827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22364729972933496834386551 33547094959400245251579827)
            ·
              refine ⟨50320642439100367877369741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33547094959400245251579827 50320642439100367877369741)
              ·
                refine ⟨18870240914662637954013653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50320642439100367877369741 18870240914662637954013653)
                ·
                  refine ⟨442271271437405577047195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18870240914662637954013653 442271271437405577047195)
                  ·
                    rfl

theorem cell22_3875941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_3875941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875941 prefixEnd_3875941 := by exact prefixLift 3875941
  have htrace : WordTrace (prefixWord ++ tailWord_3875941) baseStart_3875941 baseEnd_3875941 := by
    simpa [prefixWord, tailWord_3875941, baseEnd_3875941] using wordTrace_append hprefix tailTrace_3875941
  have hstable : (prefixWord ++ tailWord_3875941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875941).length < 2 ^ (prefixWord ++ tailWord_3875941).sum := by decide
  have hdescent : baseEnd_3875941 < baseStart_3875941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875945 : List Nat := [1, 2, 1, 1, 1, 8, 1, 1, 3, 3]
def baseStart_3875945 : Nat := 118140960795 + 3875945 * 2 ^ 59
def prefixEnd_3875945 : Nat := 4983230072969 + 3 ^ 40 * 3875945 * 2
def baseEnd_3875945 : Nat := 1326815183593962054041573

theorem tailTrace_3875945 : CollatzResearch.WordTrace tailWord_3875945 prefixEnd_3875945 1326815183593962054041573 := by
  unfold tailWord_3875945
  simp only [CollatzResearch.WordTrace]
  refine ⟨141367327943120698549885289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94244885295413799033256859 141367327943120698549885289)
  ·
    refine ⟨106025495957340523912413967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141367327943120698549885289 106025495957340523912413967)
    ·
      refine ⟨159038243936010785868620951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106025495957340523912413967 159038243936010785868620951)
      ·
        refine ⟨238557365904016178802931427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159038243936010785868620951 238557365904016178802931427)
        ·
          refine ⟨357836048856024268204397141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238557365904016178802931427 357836048856024268204397141)
          ·
            refine ⟨4193391197531534393020279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 357836048856024268204397141 4193391197531534393020279)
            ·
              refine ⟨6290086796297301589530419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193391197531534393020279 6290086796297301589530419)
              ·
                refine ⟨9435130194445952384295629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290086796297301589530419 9435130194445952384295629)
                ·
                  refine ⟨3538173822917232144110861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9435130194445952384295629 3538173822917232144110861)
                  ·
                    refine ⟨1326815183593962054041573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538173822917232144110861 1326815183593962054041573)
                    ·
                      rfl

theorem cell22_3875945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_3875945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3875945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3875945 prefixEnd_3875945 := by exact prefixLift 3875945
  have htrace : WordTrace (prefixWord ++ tailWord_3875945) baseStart_3875945 baseEnd_3875945 := by
    simpa [prefixWord, tailWord_3875945, baseEnd_3875945] using wordTrace_append hprefix tailTrace_3875945
  have hstable : (prefixWord ++ tailWord_3875945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875945).length < 2 ^ (prefixWord ++ tailWord_3875945).sum := by decide
  have hdescent : baseEnd_3875945 < baseStart_3875945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876016 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_3876016 : Nat := 118140960795 + 3876016 * 2 ^ 59
def prefixEnd_3876016 : Nat := 4983230072969 + 3 ^ 40 * 3876016 * 2
def baseEnd_3876016 : Nat := 1326839488344941535516355

theorem tailTrace_3876016 : CollatzResearch.WordTrace tailWord_3876016 prefixEnd_3876016 1326839488344941535516355 := by
  unfold tailWord_3876016
  simp only [CollatzResearch.WordTrace]
  refine ⟨70684958762931738837859951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94246611683908985117146601 70684958762931738837859951)
  ·
    refine ⟨106027438144397608256789927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70684958762931738837859951 106027438144397608256789927)
    ·
      refine ⟨159041157216596412385184891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106027438144397608256789927 159041157216596412385184891)
      ·
        refine ⟨238561735824894618577777337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159041157216596412385184891 238561735824894618577777337)
        ·
          refine ⟨178921301868670963933333003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238561735824894618577777337 178921301868670963933333003)
          ·
            refine ⟨268381952803006445899999505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178921301868670963933333003 268381952803006445899999505)
            ·
              refine ⟨201286464602254834424999629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268381952803006445899999505 201286464602254834424999629)
              ·
                refine ⟨75482424225845562909374861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201286464602254834424999629 75482424225845562909374861)
                ·
                  refine ⟨28305909084692086091015573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75482424225845562909374861 28305909084692086091015573)
                  ·
                    refine ⟨1326839488344941535516355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28305909084692086091015573 1326839488344941535516355)
                    ·
                      rfl

theorem cell22_3876016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_3876016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876016 prefixEnd_3876016 := by exact prefixLift 3876016
  have htrace : WordTrace (prefixWord ++ tailWord_3876016) baseStart_3876016 baseEnd_3876016 := by
    simpa [prefixWord, tailWord_3876016, baseEnd_3876016] using wordTrace_append hprefix tailTrace_3876016
  have hstable : (prefixWord ++ tailWord_3876016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876016).length < 2 ^ (prefixWord ++ tailWord_3876016).sum := by decide
  have hdescent : baseEnd_3876016 < baseStart_3876016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876018 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_3876018 : Nat := 118140960795 + 3876018 * 2 ^ 59
def prefixEnd_3876018 : Nat := 4983230072969 + 3 ^ 40 * 3876018 * 2
def baseEnd_3876018 : Nat := 1326840172985814196966349

theorem tailTrace_3876018 : CollatzResearch.WordTrace tailWord_3876018 prefixEnd_3876018 1326840172985814196966349 := by
  unfold tailWord_3876018
  simp only [CollatzResearch.WordTrace]
  refine ⟨35342497617964058004323177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94246660314570821344861805 35342497617964058004323177)
  ·
    refine ⟨26506873213473043503242383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35342497617964058004323177 26506873213473043503242383)
    ·
      refine ⟨39760309820209565254863575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26506873213473043503242383 39760309820209565254863575)
      ·
        refine ⟨59640464730314347882295363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39760309820209565254863575 59640464730314347882295363)
        ·
          refine ⟨89460697095471521823443045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59640464730314347882295363 89460697095471521823443045)
          ·
            refine ⟨16773880705400910341895571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89460697095471521823443045 16773880705400910341895571)
            ·
              refine ⟨25160821058101365512843357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16773880705400910341895571 25160821058101365512843357)
              ·
                refine ⟨9435307896788012067316259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25160821058101365512843357 9435307896788012067316259)
                ·
                  refine ⟨14152961845182018100974389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9435307896788012067316259 14152961845182018100974389)
                  ·
                    refine ⟨1326840172985814196966349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14152961845182018100974389 1326840172985814196966349)
                    ·
                      rfl

theorem cell22_3876018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_3876018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876018 prefixEnd_3876018 := by exact prefixLift 3876018
  have htrace : WordTrace (prefixWord ++ tailWord_3876018) baseStart_3876018 baseEnd_3876018 := by
    simpa [prefixWord, tailWord_3876018, baseEnd_3876018] using wordTrace_append hprefix tailTrace_3876018
  have hstable : (prefixWord ++ tailWord_3876018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876018).length < 2 ^ (prefixWord ++ tailWord_3876018).sum := by decide
  have hdescent : baseEnd_3876018 < baseStart_3876018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876031 : List Nat := [1, 1, 2, 2, 2, 2, 2, 10]
def baseStart_3876031 : Nat := 118140960795 + 3876031 * 2 ^ 59
def prefixEnd_3876031 : Nat := 4983230072969 + 3 ^ 40 * 3876031 * 2
def baseEnd_3876031 : Nat := 147427180350165166265701

theorem tailTrace_3876031 : CollatzResearch.WordTrace tailWord_3876031 prefixEnd_3876031 147427180350165166265701 := by
  unfold tailWord_3876031
  simp only [CollatzResearch.WordTrace]
  refine ⟨141370464620809135237515947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94246976413872756825010631 141370464620809135237515947)
  ·
    refine ⟨212055696931213702856273921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141370464620809135237515947 212055696931213702856273921)
    ·
      refine ⟨159041772698410277142205441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212055696931213702856273921 159041772698410277142205441)
      ·
        refine ⟨119281329523807707856654081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159041772698410277142205441 119281329523807707856654081)
        ·
          refine ⟨89460997142855780892490561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119281329523807707856654081 89460997142855780892490561)
          ·
            refine ⟨67095747857141835669367921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89460997142855780892490561 67095747857141835669367921)
            ·
              refine ⟨50321810892856376752025941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67095747857141835669367921 50321810892856376752025941)
              ·
                refine ⟨147427180350165166265701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50321810892856376752025941 147427180350165166265701)
                ·
                  rfl

theorem cell22_3876031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 10].length) (baseStart_3876031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876031 prefixEnd_3876031 := by exact prefixLift 3876031
  have htrace : WordTrace (prefixWord ++ tailWord_3876031) baseStart_3876031 baseEnd_3876031 := by
    simpa [prefixWord, tailWord_3876031, baseEnd_3876031] using wordTrace_append hprefix tailTrace_3876031
  have hstable : (prefixWord ++ tailWord_3876031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876031).length < 2 ^ (prefixWord ++ tailWord_3876031).sum := by decide
  have hdescent : baseEnd_3876031 < baseStart_3876031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876069 : List Nat := [1, 3, 1, 4, 3, 1, 3, 1, 2, 3]
def baseStart_3876069 : Nat := 118140960795 + 3876069 * 2 ^ 59
def prefixEnd_3876069 : Nat := 4983230072969 + 3 ^ 40 * 3876069 * 2
def baseEnd_3876069 : Nat := 1326857631328067063941193

theorem tailTrace_3876069 : CollatzResearch.WordTrace tailWord_3876069 prefixEnd_3876069 1326857631328067063941193 := by
  unfold tailWord_3876069
  simp only [CollatzResearch.WordTrace]
  refine ⟨141371850594671467727399261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94247900396447645151599507 141371850594671467727399261)
  ·
    refine ⟨53014443973001800397774723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141371850594671467727399261 53014443973001800397774723)
    ·
      refine ⟨79521665959502700596662085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53014443973001800397774723 79521665959502700596662085)
      ·
        refine ⟨14910312367406756361874141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79521665959502700596662085 14910312367406756361874141)
        ·
          refine ⟨5591367137777533635702803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14910312367406756361874141 5591367137777533635702803)
          ·
            refine ⟨8387050706666300453554205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591367137777533635702803 8387050706666300453554205)
            ·
              refine ⟨3145144014999862670082827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8387050706666300453554205 3145144014999862670082827)
              ·
                refine ⟨4717716022499794005124241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145144014999862670082827 4717716022499794005124241)
                ·
                  refine ⟨3538287016874845503843181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4717716022499794005124241 3538287016874845503843181)
                  ·
                    refine ⟨1326857631328067063941193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538287016874845503843181 1326857631328067063941193)
                    ·
                      rfl

theorem cell22_3876069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_3876069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876069 prefixEnd_3876069 := by exact prefixLift 3876069
  have htrace : WordTrace (prefixWord ++ tailWord_3876069) baseStart_3876069 baseEnd_3876069 := by
    simpa [prefixWord, tailWord_3876069, baseEnd_3876069] using wordTrace_append hprefix tailTrace_3876069
  have hstable : (prefixWord ++ tailWord_3876069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876069).length < 2 ^ (prefixWord ++ tailWord_3876069).sum := by decide
  have hdescent : baseEnd_3876069 < baseStart_3876069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876078 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_3876078 : Nat := 118140960795 + 3876078 * 2 ^ 59
def prefixEnd_3876078 : Nat := 4983230072969 + 3 ^ 40 * 3876078 * 2
def baseEnd_3876078 : Nat := 1326860712211994040466165

theorem tailTrace_3876078 : CollatzResearch.WordTrace tailWord_3876078 prefixEnd_3876078 1326860712211994040466165 := by
  unfold tailWord_3876078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17671522356454857783059611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94248119234425908176317925 17671522356454857783059611)
  ·
    refine ⟨26507283534682286674589417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17671522356454857783059611 26507283534682286674589417)
    ·
      refine ⟨19880462651011715005942063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26507283534682286674589417 19880462651011715005942063)
      ·
        refine ⟨29820693976517572508913095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19880462651011715005942063 29820693976517572508913095)
        ·
          refine ⟨44731040964776358763369643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29820693976517572508913095 44731040964776358763369643)
          ·
            refine ⟨67096561447164538145054465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44731040964776358763369643 67096561447164538145054465)
            ·
              refine ⟨50322421085373403608790849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67096561447164538145054465 50322421085373403608790849)
              ·
                refine ⟨37741815814030052706593137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50322421085373403608790849 37741815814030052706593137)
                ·
                  refine ⟨28306361860522539529944853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37741815814030052706593137 28306361860522539529944853)
                  ·
                    refine ⟨1326860712211994040466165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28306361860522539529944853 1326860712211994040466165)
                    ·
                      rfl

theorem cell22_3876078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_3876078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876078 prefixEnd_3876078 := by exact prefixLift 3876078
  have htrace : WordTrace (prefixWord ++ tailWord_3876078) baseStart_3876078 baseEnd_3876078 := by
    simpa [prefixWord, tailWord_3876078, baseEnd_3876078] using wordTrace_append hprefix tailTrace_3876078
  have hstable : (prefixWord ++ tailWord_3876078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876078).length < 2 ^ (prefixWord ++ tailWord_3876078).sum := by decide
  have hdescent : baseEnd_3876078 < baseStart_3876078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876082 : List Nat := [3, 2, 1, 3, 3, 2, 2, 6]
def baseStart_3876082 : Nat := 118140960795 + 3876082 * 2 ^ 59
def prefixEnd_3876082 : Nat := 4983230072969 + 3 ^ 40 * 3876082 * 2
def baseEnd_3876082 : Nat := 147429120165971040374017

theorem tailTrace_3876082 : CollatzResearch.WordTrace tailWord_3876082 prefixEnd_3876082 147429120165971040374017 := by
  unfold tailWord_3876082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35343081185906092736905625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94248216495749580631748333 35343081185906092736905625)
  ·
    refine ⟨26507310889429569552679219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35343081185906092736905625 26507310889429569552679219)
    ·
      refine ⟨39760966334144354329018829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26507310889429569552679219 39760966334144354329018829)
      ·
        refine ⟨14910362375304132873382061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39760966334144354329018829 14910362375304132873382061)
        ·
          refine ⟨5591385890739049827518273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14910362375304132873382061 5591385890739049827518273)
          ·
            refine ⟨4193539418054287370638705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5591385890739049827518273 4193539418054287370638705)
            ·
              refine ⟨3145154563540715527979029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193539418054287370638705 3145154563540715527979029)
              ·
                refine ⟨147429120165971040374017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3145154563540715527979029 147429120165971040374017)
                ·
                  rfl

theorem cell22_3876082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_3876082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876082 prefixEnd_3876082 := by exact prefixLift 3876082
  have htrace : WordTrace (prefixWord ++ tailWord_3876082) baseStart_3876082 baseEnd_3876082 := by
    simpa [prefixWord, tailWord_3876082, baseEnd_3876082] using wordTrace_append hprefix tailTrace_3876082
  have hstable : (prefixWord ++ tailWord_3876082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876082).length < 2 ^ (prefixWord ++ tailWord_3876082).sum := by decide
  have hdescent : baseEnd_3876082 < baseStart_3876082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876123 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 3, 4]
def baseStart_3876123 : Nat := 118140960795 + 3876123 * 2 ^ 59
def prefixEnd_3876123 : Nat := 4983230072969 + 3 ^ 40 * 3876123 * 2
def baseEnd_3876123 : Nat := 1326876116631628923091027

theorem tailTrace_3876123 : CollatzResearch.WordTrace tailWord_3876123 prefixEnd_3876123 1326876116631628923091027 := by
  unfold tailWord_3876123
  simp only [CollatzResearch.WordTrace]
  refine ⟨141373820136475834949865023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94249213424317223299910015 141373820136475834949865023)
  ·
    refine ⟨212060730204713752424797535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141373820136475834949865023 212060730204713752424797535)
    ·
      refine ⟨318091095307070628637196303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212060730204713752424797535 318091095307070628637196303)
      ·
        refine ⟨477136642960605942955794455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318091095307070628637196303 477136642960605942955794455)
        ·
          refine ⟨715704964440908914433691683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477136642960605942955794455 715704964440908914433691683)
          ·
            refine ⟨1073557446661363371650537525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715704964440908914433691683 1073557446661363371650537525)
            ·
              refine ⟨100646010624502816092237893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1073557446661363371650537525 100646010624502816092237893)
              ·
                refine ⟨18871126992094278017294605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100646010624502816092237893 18871126992094278017294605)
                ·
                  refine ⟨7076672622035354256485477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18871126992094278017294605 7076672622035354256485477)
                  ·
                    refine ⟨1326876116631628923091027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7076672622035354256485477 1326876116631628923091027)
                    ·
                      rfl

theorem cell22_3876123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 4].length) (baseStart_3876123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876123 prefixEnd_3876123 := by exact prefixLift 3876123
  have htrace : WordTrace (prefixWord ++ tailWord_3876123) baseStart_3876123 baseEnd_3876123 := by
    simpa [prefixWord, tailWord_3876123, baseEnd_3876123] using wordTrace_append hprefix tailTrace_3876123
  have hstable : (prefixWord ++ tailWord_3876123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876123).length < 2 ^ (prefixWord ++ tailWord_3876123).sum := by decide
  have hdescent : baseEnd_3876123 < baseStart_3876123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876168 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_3876168 : Nat := 118140960795 + 3876168 * 2 ^ 59
def prefixEnd_3876168 : Nat := 4983230072969 + 3 ^ 40 * 3876168 * 2
def baseEnd_3876168 : Nat := 1326891521051263805715889

theorem tailTrace_3876168 : CollatzResearch.WordTrace tailWord_3876168 prefixEnd_3876168 1326891521051263805715889 := by
  unfold tailWord_3876168
  simp only [CollatzResearch.WordTrace]
  refine ⟨70687730710656403817626579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94250307614208538423502105 70687730710656403817626579)
  ·
    refine ⟨106031596065984605726439869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70687730710656403817626579 106031596065984605726439869)
    ·
      refine ⟨39761848524744227147414951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106031596065984605726439869 39761848524744227147414951)
      ·
        refine ⟨59642772787116340721122427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39761848524744227147414951 59642772787116340721122427)
        ·
          refine ⟨89464159180674511081683641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59642772787116340721122427 89464159180674511081683641)
          ·
            refine ⟨67098119385505883311262731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89464159180674511081683641 67098119385505883311262731)
            ·
              refine ⟨100647179078258824966894097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67098119385505883311262731 100647179078258824966894097)
              ·
                refine ⟨75485384308694118725170573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100647179078258824966894097 75485384308694118725170573)
                ·
                  refine ⟨28307019115760294521938965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75485384308694118725170573 28307019115760294521938965)
                  ·
                    refine ⟨1326891521051263805715889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28307019115760294521938965 1326891521051263805715889)
                    ·
                      rfl

theorem cell22_3876168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_3876168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876168 prefixEnd_3876168 := by exact prefixLift 3876168
  have htrace : WordTrace (prefixWord ++ tailWord_3876168) baseStart_3876168 baseEnd_3876168 := by
    simpa [prefixWord, tailWord_3876168, baseEnd_3876168] using wordTrace_append hprefix tailTrace_3876168
  have hstable : (prefixWord ++ tailWord_3876168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876168).length < 2 ^ (prefixWord ++ tailWord_3876168).sum := by decide
  have hdescent : baseEnd_3876168 < baseStart_3876168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876170 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_3876170 : Nat := 118140960795 + 3876170 * 2 ^ 59
def prefixEnd_3876170 : Nat := 4983230072969 + 3 ^ 40 * 3876170 * 2
def baseEnd_3876170 : Nat := 1326892205692136467165883

theorem tailTrace_3876170 : CollatzResearch.WordTrace tailWord_3876170 prefixEnd_3876170 1326892205692136467165883 := by
  unfold tailWord_3876170
  simp only [CollatzResearch.WordTrace]
  refine ⟨35343883591826390494206491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94250356244870374651217309 35343883591826390494206491)
  ·
    refine ⟨53015825387739585741309737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35343883591826390494206491 53015825387739585741309737)
    ·
      refine ⟨39761869040804689305982303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53015825387739585741309737 39761869040804689305982303)
      ·
        refine ⟨59642803561207033958973455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39761869040804689305982303 59642803561207033958973455)
        ·
          refine ⟨89464205341810550938460183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59642803561207033958973455 89464205341810550938460183)
          ·
            refine ⟨134196308012715826407690275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89464205341810550938460183 134196308012715826407690275)
            ·
              refine ⟨201294462019073739611535413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134196308012715826407690275 201294462019073739611535413)
              ·
                refine ⟨18871355814288163088581445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201294462019073739611535413 18871355814288163088581445)
                ·
                  refine ⟨3538379215179030579109021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18871355814288163088581445 3538379215179030579109021)
                  ·
                    refine ⟨1326892205692136467165883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538379215179030579109021 1326892205692136467165883)
                    ·
                      rfl

theorem cell22_3876170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_3876170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876170 prefixEnd_3876170 := by exact prefixLift 3876170
  have htrace : WordTrace (prefixWord ++ tailWord_3876170) baseStart_3876170 baseEnd_3876170 := by
    simpa [prefixWord, tailWord_3876170, baseEnd_3876170] using wordTrace_append hprefix tailTrace_3876170
  have hstable : (prefixWord ++ tailWord_3876170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876170).length < 2 ^ (prefixWord ++ tailWord_3876170).sum := by decide
  have hdescent : baseEnd_3876170 < baseStart_3876170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876172 : List Nat := [2, 2, 1, 3, 2, 3, 1, 4, 4]
def baseStart_3876172 : Nat := 118140960795 + 3876172 * 2 ^ 59
def prefixEnd_3876172 : Nat := 4983230072969 + 3 ^ 40 * 3876172 * 2
def baseEnd_3876172 : Nat := 442297630111003042871959

theorem tailTrace_3876172 : CollatzResearch.WordTrace tailWord_3876172 prefixEnd_3876172 442297630111003042871959 := by
  unfold tailWord_3876172
  simp only [CollatzResearch.WordTrace]
  refine ⟨70687803656649158159199385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94250404875532210878932513 70687803656649158159199385)
  ·
    refine ⟨53015852742486868619399539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70687803656649158159199385 53015852742486868619399539)
    ·
      refine ⟨79523779113730302929099309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53015852742486868619399539 79523779113730302929099309)
      ·
        refine ⟨29821417167648863598412241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79523779113730302929099309 29821417167648863598412241)
        ·
          refine ⟨22366062875736647698809181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29821417167648863598412241 22366062875736647698809181)
          ·
            refine ⟨8387273578401242887053443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22366062875736647698809181 8387273578401242887053443)
            ·
              refine ⟨12580910367601864330580165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387273578401242887053443 12580910367601864330580165)
              ·
                refine ⟨2358920693925349561983781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12580910367601864330580165 2358920693925349561983781)
                ·
                  refine ⟨442297630111003042871959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2358920693925349561983781 442297630111003042871959)
                  ·
                    rfl

theorem cell22_3876172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_3876172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876172 prefixEnd_3876172 := by exact prefixLift 3876172
  have htrace : WordTrace (prefixWord ++ tailWord_3876172) baseStart_3876172 baseEnd_3876172 := by
    simpa [prefixWord, tailWord_3876172, baseEnd_3876172] using wordTrace_append hprefix tailTrace_3876172
  have hstable : (prefixWord ++ tailWord_3876172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876172).length < 2 ^ (prefixWord ++ tailWord_3876172).sum := by decide
  have hdescent : baseEnd_3876172 < baseStart_3876172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876202 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_3876202 : Nat := 118140960795 + 3876202 * 2 ^ 59
def prefixEnd_3876202 : Nat := 4983230072969 + 3 ^ 40 * 3876202 * 2
def baseEnd_3876202 : Nat := 1326903159946099050365785

theorem tailTrace_3876202 : CollatzResearch.WordTrace tailWord_3876202 prefixEnd_3876202 1326903159946099050365785 := by
  unfold tailWord_3876202
  simp only [CollatzResearch.WordTrace]
  refine ⟨35344175375797407860497715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94251134335459754294660573 35344175375797407860497715)
  ·
    refine ⟨53016263063696111790746573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35344175375797407860497715 53016263063696111790746573)
    ·
      refine ⟨19881098648886041921529965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53016263063696111790746573 19881098648886041921529965)
      ·
        refine ⟨7455411993332265720573737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19881098648886041921529965 7455411993332265720573737)
        ·
          refine ⟨5591558994999199290430303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7455411993332265720573737 5591558994999199290430303)
          ·
            refine ⟨8387338492498798935645455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591558994999199290430303 8387338492498798935645455)
            ·
              refine ⟨12581007738748198403468183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387338492498798935645455 12581007738748198403468183)
              ·
                refine ⟨18871511608122297605202275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12581007738748198403468183 18871511608122297605202275)
                ·
                  refine ⟨28307267412183446407803413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18871511608122297605202275 28307267412183446407803413)
                  ·
                    refine ⟨1326903159946099050365785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28307267412183446407803413 1326903159946099050365785)
                    ·
                      rfl

theorem cell22_3876202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_3876202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876202 prefixEnd_3876202 := by exact prefixLift 3876202
  have htrace : WordTrace (prefixWord ++ tailWord_3876202) baseStart_3876202 baseEnd_3876202 := by
    simpa [prefixWord, tailWord_3876202, baseEnd_3876202] using wordTrace_append hprefix tailTrace_3876202
  have hstable : (prefixWord ++ tailWord_3876202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876202).length < 2 ^ (prefixWord ++ tailWord_3876202).sum := by decide
  have hdescent : baseEnd_3876202 < baseStart_3876202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876206 : List Nat := [4, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_3876206 : Nat := 118140960795 + 3876206 * 2 ^ 59
def prefixEnd_3876206 : Nat := 4983230072969 + 3 ^ 40 * 3876206 * 2
def baseEnd_3876206 : Nat := 442301509742614791088591

theorem tailTrace_3876206 : CollatzResearch.WordTrace tailWord_3876206 prefixEnd_3876206 442301509742614791088591 := by
  unfold tailWord_3876206
  simp only [CollatzResearch.WordTrace]
  refine ⟨17672105924396892515642059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94251231596783426750090981 17672105924396892515642059)
  ·
    refine ⟨26508158886595338773463089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17672105924396892515642059 26508158886595338773463089)
    ·
      refine ⟨19881119164946504080097317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26508158886595338773463089 19881119164946504080097317)
      ·
        refine ⟨3727709843427469515018247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19881119164946504080097317 3727709843427469515018247)
        ·
          refine ⟨5591564765141204272527371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727709843427469515018247 5591564765141204272527371)
          ·
            refine ⟨8387347147711806408791057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591564765141204272527371 8387347147711806408791057)
            ·
              refine ⟨6290510360783854806593293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8387347147711806408791057 6290510360783854806593293)
              ·
                refine ⟨2358941385293945552472485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6290510360783854806593293 2358941385293945552472485)
                ·
                  refine ⟨442301509742614791088591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2358941385293945552472485 442301509742614791088591)
                  ·
                    rfl

theorem cell22_3876206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_3876206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876206 prefixEnd_3876206 := by exact prefixLift 3876206
  have htrace : WordTrace (prefixWord ++ tailWord_3876206) baseStart_3876206 baseEnd_3876206 := by
    simpa [prefixWord, tailWord_3876206, baseEnd_3876206] using wordTrace_append hprefix tailTrace_3876206
  have hstable : (prefixWord ++ tailWord_3876206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876206).length < 2 ^ (prefixWord ++ tailWord_3876206).sum := by decide
  have hdescent : baseEnd_3876206 < baseStart_3876206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876215 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 5, 3]
def baseStart_3876215 : Nat := 118140960795 + 3876215 * 2 ^ 59
def prefixEnd_3876215 : Nat := 4983230072969 + 3 ^ 40 * 3876215 * 2
def baseEnd_3876215 : Nat := 1326907610111771349790745

theorem tailTrace_3876215 : CollatzResearch.WordTrace tailWord_3876215 prefixEnd_3876215 1326907610111771349790745 := by
  unfold tailWord_3876215
  simp only [CollatzResearch.WordTrace]
  refine ⟨141377175652142534662214099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94251450434761689774809399 141377175652142534662214099)
  ·
    refine ⟨212065763478213801993321149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141377175652142534662214099 212065763478213801993321149)
    ·
      refine ⟨79524661304330175747495431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212065763478213801993321149 79524661304330175747495431)
      ·
        refine ⟨119286991956495263621243147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79524661304330175747495431 119286991956495263621243147)
        ·
          refine ⟨178930487934742895431864721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119286991956495263621243147 178930487934742895431864721)
          ·
            refine ⟨134197865951057171573898541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178930487934742895431864721 134197865951057171573898541)
            ·
              refine ⟨50324199731646439340211953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134197865951057171573898541 50324199731646439340211953)
              ·
                refine ⟨37743149798734829505158965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50324199731646439340211953 37743149798734829505158965)
                ·
                  refine ⟨3538420293631390266108653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37743149798734829505158965 3538420293631390266108653)
                  ·
                    refine ⟨1326907610111771349790745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538420293631390266108653 1326907610111771349790745)
                    ·
                      rfl

theorem cell22_3876215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_3876215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876215 prefixEnd_3876215 := by exact prefixLift 3876215
  have htrace : WordTrace (prefixWord ++ tailWord_3876215) baseStart_3876215 baseEnd_3876215 := by
    simpa [prefixWord, tailWord_3876215, baseEnd_3876215] using wordTrace_append hprefix tailTrace_3876215
  have hstable : (prefixWord ++ tailWord_3876215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876215).length < 2 ^ (prefixWord ++ tailWord_3876215).sum := by decide
  have hdescent : baseEnd_3876215 < baseStart_3876215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876232 : List Nat := [2, 1, 3, 3, 1, 2, 1, 3, 3, 3]
def baseStart_3876232 : Nat := 118140960795 + 3876232 * 2 ^ 59
def prefixEnd_3876232 : Nat := 4983230072969 + 3 ^ 40 * 3876232 * 2
def baseEnd_3876232 : Nat := 1326913429559188972115693

theorem tailTrace_3876232 : CollatzResearch.WordTrace tailWord_3876232 prefixEnd_3876232 1326913429559188972115693 := by
  unfold tailWord_3876232
  simp only [CollatzResearch.WordTrace]
  refine ⟨70688897846540473282791475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94251863795387297710388633 70688897846540473282791475)
  ·
    refine ⟨106033346769810709924187213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70688897846540473282791475 106033346769810709924187213)
    ·
      refine ⟨39762505038679016221570205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106033346769810709924187213 39762505038679016221570205)
      ·
        refine ⟨14910939389504631083088827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39762505038679016221570205 14910939389504631083088827)
        ·
          refine ⟨22366409084256946624633241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14910939389504631083088827 22366409084256946624633241)
          ·
            refine ⟨16774806813192709968474931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22366409084256946624633241 16774806813192709968474931)
            ·
              refine ⟨25162210219789064952712397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16774806813192709968474931 25162210219789064952712397)
              ·
                refine ⟨9435828832420899357267149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25162210219789064952712397 9435828832420899357267149)
                ·
                  refine ⟨3538435812157837258975181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9435828832420899357267149 3538435812157837258975181)
                  ·
                    refine ⟨1326913429559188972115693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538435812157837258975181 1326913429559188972115693)
                    ·
                      rfl

theorem cell22_3876232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_3876232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876232 prefixEnd_3876232 := by exact prefixLift 3876232
  have htrace : WordTrace (prefixWord ++ tailWord_3876232) baseStart_3876232 baseEnd_3876232 := by
    simpa [prefixWord, tailWord_3876232, baseEnd_3876232] using wordTrace_append hprefix tailTrace_3876232
  have hstable : (prefixWord ++ tailWord_3876232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876232).length < 2 ^ (prefixWord ++ tailWord_3876232).sum := by decide
  have hdescent : baseEnd_3876232 < baseStart_3876232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876245 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 5]
def baseStart_3876245 : Nat := 118140960795 + 3876245 * 2 ^ 59
def prefixEnd_3876245 : Nat := 4983230072969 + 3 ^ 40 * 3876245 * 2
def baseEnd_3876245 : Nat := 442305959908287090513551

theorem tailTrace_3876245 : CollatzResearch.WordTrace tailWord_3876245 prefixEnd_3876245 442305959908287090513551 := by
  unfold tailWord_3876245
  simp only [CollatzResearch.WordTrace]
  refine ⟨141378269842033849785806189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94252179894689233190537459 141378269842033849785806189)
  ·
    refine ⟨53016851190762693669677321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141378269842033849785806189 53016851190762693669677321)
    ·
      refine ⟨39762638393072020252257991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53016851190762693669677321 39762638393072020252257991)
      ·
        refine ⟨59643957589608030378386987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39762638393072020252257991 59643957589608030378386987)
        ·
          refine ⟨89465936384412045567580481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59643957589608030378386987 89465936384412045567580481)
          ·
            refine ⟨67099452288309034175685361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89465936384412045567580481 67099452288309034175685361)
            ·
              refine ⟨50324589216231775631764021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67099452288309034175685361 50324589216231775631764021)
              ·
                refine ⟨4717930239021728965477877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50324589216231775631764021 4717930239021728965477877)
                ·
                  refine ⟨442305959908287090513551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4717930239021728965477877 442305959908287090513551)
                  ·
                    rfl

theorem cell22_3876245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_3876245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876245 prefixEnd_3876245 := by exact prefixLift 3876245
  have htrace : WordTrace (prefixWord ++ tailWord_3876245) baseStart_3876245 baseEnd_3876245 := by
    simpa [prefixWord, tailWord_3876245, baseEnd_3876245] using wordTrace_append hprefix tailTrace_3876245
  have hstable : (prefixWord ++ tailWord_3876245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876245).length < 2 ^ (prefixWord ++ tailWord_3876245).sum := by decide
  have hdescent : baseEnd_3876245 < baseStart_3876245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876337 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_3876337 : Nat := 118140960795 + 3876337 * 2 ^ 59
def prefixEnd_3876337 : Nat := 4983230072969 + 3 ^ 40 * 3876337 * 2
def baseEnd_3876337 : Nat := 1326949373205003698240371

theorem tailTrace_3876337 : CollatzResearch.WordTrace tailWord_3876337 prefixEnd_3876337 1326949373205003698240371 := by
  unfold tailWord_3876337
  simp only [CollatzResearch.WordTrace]
  refine ⟨141381625357700549498155265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94254416905133699665436843 141381625357700549498155265)
  ·
    refine ⟨106036219018275412123616449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141381625357700549498155265 106036219018275412123616449)
    ·
      refine ⟨79527164263706559092712337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106036219018275412123616449 79527164263706559092712337)
      ·
        refine ⟨59645373197779919319534253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79527164263706559092712337 59645373197779919319534253)
        ·
          refine ⟨22367014949167469744825345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59645373197779919319534253 22367014949167469744825345)
          ·
            refine ⟨16775261211875602308619009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22367014949167469744825345 16775261211875602308619009)
            ·
              refine ⟨12581445908906701731464257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16775261211875602308619009 12581445908906701731464257)
              ·
                refine ⟨9436084431680026298598193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12581445908906701731464257 9436084431680026298598193)
                ·
                  refine ⟨7077063323760019723948645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9436084431680026298598193 7077063323760019723948645)
                  ·
                    refine ⟨1326949373205003698240371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7077063323760019723948645 1326949373205003698240371)
                    ·
                      rfl

theorem cell22_3876337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_3876337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876337 prefixEnd_3876337 := by exact prefixLift 3876337
  have htrace : WordTrace (prefixWord ++ tailWord_3876337) baseStart_3876337 baseEnd_3876337 := by
    simpa [prefixWord, tailWord_3876337, baseEnd_3876337] using wordTrace_append hprefix tailTrace_3876337
  have hstable : (prefixWord ++ tailWord_3876337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876337).length < 2 ^ (prefixWord ++ tailWord_3876337).sum := by decide
  have hdescent : baseEnd_3876337 < baseStart_3876337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876341 : List Nat := [1, 3, 5, 1, 1, 2, 1, 4, 4]
def baseStart_3876341 : Nat := 118140960795 + 3876341 * 2 ^ 59
def prefixEnd_3876341 : Nat := 4983230072969 + 3 ^ 40 * 3876341 * 2
def baseEnd_3876341 : Nat := 442316914162249673713453

theorem tailTrace_3876341 : CollatzResearch.WordTrace tailWord_3876341 prefixEnd_3876341 442316914162249673713453 := by
  unfold tailWord_3876341
  simp only [CollatzResearch.WordTrace]
  refine ⟨141381771249686058181300877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94254514166457372120867251 141381771249686058181300877)
  ·
    refine ⟨53018164218632271817987829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141381771249686058181300877 53018164218632271817987829)
    ·
      refine ⟨4970452895496775482936359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53018164218632271817987829 4970452895496775482936359)
      ·
        refine ⟨7455679343245163224404539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970452895496775482936359 7455679343245163224404539)
        ·
          refine ⟨11183519014867744836606809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7455679343245163224404539 11183519014867744836606809)
          ·
            refine ⟨8387639261150808627455107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11183519014867744836606809 8387639261150808627455107)
            ·
              refine ⟨12581458891726212941182661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387639261150808627455107 12581458891726212941182661)
              ·
                refine ⟨2359023542198664926471749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12581458891726212941182661 2359023542198664926471749)
                ·
                  refine ⟨442316914162249673713453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359023542198664926471749 442316914162249673713453)
                  ·
                    rfl

theorem cell22_3876341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_3876341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876341 prefixEnd_3876341 := by exact prefixLift 3876341
  have htrace : WordTrace (prefixWord ++ tailWord_3876341) baseStart_3876341 baseEnd_3876341 := by
    simpa [prefixWord, tailWord_3876341, baseEnd_3876341] using wordTrace_append hprefix tailTrace_3876341
  have hstable : (prefixWord ++ tailWord_3876341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876341).length < 2 ^ (prefixWord ++ tailWord_3876341).sum := by decide
  have hdescent : baseEnd_3876341 < baseStart_3876341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876358 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3876358 : Nat := 118140960795 + 3876358 * 2 ^ 59
def prefixEnd_3876358 : Nat := 4983230072969 + 3 ^ 40 * 3876358 * 2
def baseEnd_3876358 : Nat := 442318853978055547821769

theorem tailTrace_3876358 : CollatzResearch.WordTrace tailWord_3876358 prefixEnd_3876358 442318853978055547821769 := by
  unfold tailWord_3876358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4418199727832014690145929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94254927527082980056446485 4418199727832014690145929)
  ·
    refine ⟨3313649795874011017609447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4418199727832014690145929 3313649795874011017609447)
    ·
      refine ⟨4970474693811016526414171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313649795874011017609447 4970474693811016526414171)
      ·
        refine ⟨7455712040716524789621257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970474693811016526414171 7455712040716524789621257)
        ·
          refine ⟨5591784030537393592215943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7455712040716524789621257 5591784030537393592215943)
          ·
            refine ⟨8387676045806090388323915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591784030537393592215943 8387676045806090388323915)
            ·
              refine ⟨12581514068709135582485873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387676045806090388323915 12581514068709135582485873)
              ·
                refine ⟨9436135551531851686864405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12581514068709135582485873 9436135551531851686864405)
                ·
                  refine ⟨442318853978055547821769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9436135551531851686864405 442318853978055547821769)
                  ·
                    rfl

theorem cell22_3876358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3876358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876358 prefixEnd_3876358 := by exact prefixLift 3876358
  have htrace : WordTrace (prefixWord ++ tailWord_3876358) baseStart_3876358 baseEnd_3876358 := by
    simpa [prefixWord, tailWord_3876358, baseEnd_3876358] using wordTrace_append hprefix tailTrace_3876358
  have hstable : (prefixWord ++ tailWord_3876358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876358).length < 2 ^ (prefixWord ++ tailWord_3876358).sum := by decide
  have hdescent : baseEnd_3876358 < baseStart_3876358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876487 : List Nat := [1, 1, 4, 2, 1, 3, 2, 8]
def baseStart_3876487 : Nat := 118140960795 + 3876487 * 2 ^ 59
def prefixEnd_3876487 : Nat := 4983230072969 + 3 ^ 40 * 3876487 * 2
def baseEnd_3876487 : Nat := 147444524585605922998879

theorem tailTrace_3876487 : CollatzResearch.WordTrace tailWord_3876487 prefixEnd_3876487 147444524585605922998879 := by
  unfold tailWord_3876487
  simp only [CollatzResearch.WordTrace]
  refine ⟨141387096307157125116115715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94258064204771416744077143 141387096307157125116115715)
  ·
    refine ⟨212080644460735687674173573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141387096307157125116115715 212080644460735687674173573)
    ·
      refine ⟨39765120836387941438907545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212080644460735687674173573 39765120836387941438907545)
      ·
        refine ⟨29823840627290956079180659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39765120836387941438907545 29823840627290956079180659)
        ·
          refine ⟨44735760940936434118770989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29823840627290956079180659 44735760940936434118770989)
          ·
            refine ⟨16775910352851162794539121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44735760940936434118770989 16775910352851162794539121)
            ·
              refine ⟨12581932764638372095904341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16775910352851162794539121 12581932764638372095904341)
              ·
                refine ⟨147444524585605922998879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12581932764638372095904341 147444524585605922998879)
                ·
                  rfl

theorem cell22_3876487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 8].length) (baseStart_3876487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876487 prefixEnd_3876487 := by exact prefixLift 3876487
  have htrace : WordTrace (prefixWord ++ tailWord_3876487) baseStart_3876487 baseEnd_3876487 := by
    simpa [prefixWord, tailWord_3876487, baseEnd_3876487] using wordTrace_append hprefix tailTrace_3876487
  have hstable : (prefixWord ++ tailWord_3876487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876487).length < 2 ^ (prefixWord ++ tailWord_3876487).sum := by decide
  have hdescent : baseEnd_3876487 < baseStart_3876487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876508 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_3876508 : Nat := 118140960795 + 3876508 * 2 ^ 59
def prefixEnd_3876508 : Nat := 4983230072969 + 3 ^ 40 * 3876508 * 2
def baseEnd_3876508 : Nat := 1327007909999616252214847

theorem tailTrace_3876508 : CollatzResearch.WordTrace tailWord_3876508 prefixEnd_3876508 1327007909999616252214847 := by
  unfold tailWord_3876508
  simp only [CollatzResearch.WordTrace]
  refine ⟨70693931120040522851315089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94258574826720697135086785 70693931120040522851315089)
  ·
    refine ⟨53020448340030392138486317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70693931120040522851315089 53020448340030392138486317)
    ·
      refine ⟨19882668127511397051932369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53020448340030392138486317 19882668127511397051932369)
      ·
        refine ⟨14912001095633547788949277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19882668127511397051932369 14912001095633547788949277)
        ·
          refine ⟨5592000410862580420855979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14912001095633547788949277 5592000410862580420855979)
          ·
            refine ⟨8388000616293870631283969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592000410862580420855979 8388000616293870631283969)
            ·
              refine ⟨6291000462220402973462977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8388000616293870631283969 6291000462220402973462977)
              ·
                refine ⟨4718250346665302230097233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6291000462220402973462977 4718250346665302230097233)
                ·
                  refine ⟨3538687759998976672572925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718250346665302230097233 3538687759998976672572925)
                  ·
                    refine ⟨1327007909999616252214847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538687759998976672572925 1327007909999616252214847)
                    ·
                      rfl

theorem cell22_3876508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_3876508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876508 prefixEnd_3876508 := by exact prefixLift 3876508
  have htrace : WordTrace (prefixWord ++ tailWord_3876508) baseStart_3876508 baseEnd_3876508 := by
    simpa [prefixWord, tailWord_3876508, baseEnd_3876508] using wordTrace_append hprefix tailTrace_3876508
  have hstable : (prefixWord ++ tailWord_3876508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876508).length < 2 ^ (prefixWord ++ tailWord_3876508).sum := by decide
  have hdescent : baseEnd_3876508 < baseStart_3876508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876510 : List Nat := [4, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_3876510 : Nat := 118140960795 + 3876510 * 2 ^ 59
def prefixEnd_3876510 : Nat := 4983230072969 + 3 ^ 40 * 3876510 * 2
def baseEnd_3876510 : Nat := 442336198213496304554947

theorem tailTrace_3876510 : CollatzResearch.WordTrace tailWord_3876510 prefixEnd_3876510 442336198213496304554947 := by
  unfold tailWord_3876510
  simp only [CollatzResearch.WordTrace]
  refine ⟨17673491898259225005525373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94258623457382533362801989 17673491898259225005525373)
  ·
    refine ⟨6627559461847209377072015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17673491898259225005525373 6627559461847209377072015)
    ·
      refine ⟨9941339192770814065608023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6627559461847209377072015 9941339192770814065608023)
      ·
        refine ⟨14912008789156221098412035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9941339192770814065608023 14912008789156221098412035)
        ·
          refine ⟨22368013183734331647618053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14912008789156221098412035 22368013183734331647618053)
          ·
            refine ⟨4194002471950187183928385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22368013183734331647618053 4194002471950187183928385)
            ·
              refine ⟨3145501853962640387946289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4194002471950187183928385 3145501853962640387946289)
              ·
                refine ⟨2359126390471980290959717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3145501853962640387946289 2359126390471980290959717)
                ·
                  refine ⟨442336198213496304554947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359126390471980290959717 442336198213496304554947)
                  ·
                    rfl

theorem cell22_3876510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_3876510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876510 prefixEnd_3876510 := by exact prefixLift 3876510
  have htrace : WordTrace (prefixWord ++ tailWord_3876510) baseStart_3876510 baseEnd_3876510 := by
    simpa [prefixWord, tailWord_3876510, baseEnd_3876510] using wordTrace_append hprefix tailTrace_3876510
  have hstable : (prefixWord ++ tailWord_3876510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876510).length < 2 ^ (prefixWord ++ tailWord_3876510).sum := by decide
  have hdescent : baseEnd_3876510 < baseStart_3876510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876517 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3876517 : Nat := 118140960795 + 3876517 * 2 ^ 59
def prefixEnd_3876517 : Nat := 4983230072969 + 3 ^ 40 * 3876517 * 2
def baseEnd_3876517 : Nat := 1327010990883543228739819

theorem tailTrace_3876517 : CollatzResearch.WordTrace tailWord_3876517 prefixEnd_3876517 1327010990883543228739819 := by
  unfold tailWord_3876517
  simp only [CollatzResearch.WordTrace]
  refine ⟨141388190497048440239707805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94258793664698960159805203 141388190497048440239707805)
  ·
    refine ⟨53020571436393165089890427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141388190497048440239707805 53020571436393165089890427)
    ·
      refine ⟨79530857154589747634835641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53020571436393165089890427 79530857154589747634835641)
      ·
        refine ⟨59648142865942310726126731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79530857154589747634835641 59648142865942310726126731)
        ·
          refine ⟨89472214298913466089190097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59648142865942310726126731 89472214298913466089190097)
          ·
            refine ⟨67104160724185099566892573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89472214298913466089190097 67104160724185099566892573)
            ·
              refine ⟨25164060271569412337584715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67104160724185099566892573 25164060271569412337584715)
              ·
                refine ⟨37746090407354118506377073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25164060271569412337584715 37746090407354118506377073)
                ·
                  refine ⟨28309567805515588879782805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37746090407354118506377073 28309567805515588879782805)
                  ·
                    refine ⟨1327010990883543228739819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28309567805515588879782805 1327010990883543228739819)
                    ·
                      rfl

theorem cell22_3876517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3876517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876517 prefixEnd_3876517 := by exact prefixLift 3876517
  have htrace : WordTrace (prefixWord ++ tailWord_3876517) baseStart_3876517 baseEnd_3876517 := by
    simpa [prefixWord, tailWord_3876517, baseEnd_3876517] using wordTrace_append hprefix tailTrace_3876517
  have hstable : (prefixWord ++ tailWord_3876517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876517).length < 2 ^ (prefixWord ++ tailWord_3876517).sum := by decide
  have hdescent : baseEnd_3876517 < baseStart_3876517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876594 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_3876594 : Nat := 118140960795 + 3876594 * 2 ^ 59
def prefixEnd_3876594 : Nat := 4983230072969 + 3 ^ 40 * 3876594 * 2
def baseEnd_3876594 : Nat := 442345783185713564854861

theorem tailTrace_3876594 : CollatzResearch.WordTrace tailWord_3876594 prefixEnd_3876594 442345783185713564854861 := by
  unfold tailWord_3876594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35347749729442370597565209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94260665945179654926840557 35347749729442370597565209)
  ·
    refine ⟨26510812297081777948173907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35347749729442370597565209 26510812297081777948173907)
    ·
      refine ⟨39766218445622666922260861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26510812297081777948173907 39766218445622666922260861)
      ·
        refine ⟨14912331917108500095847823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39766218445622666922260861 14912331917108500095847823)
        ·
          refine ⟨22368497875662750143771735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14912331917108500095847823 22368497875662750143771735)
          ·
            refine ⟨33552746813494125215657603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22368497875662750143771735 33552746813494125215657603)
            ·
              refine ⟨50329120220241187823486405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33552746813494125215657603 50329120220241187823486405)
              ·
                refine ⟨9436710041295222716903701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50329120220241187823486405 9436710041295222716903701)
                ·
                  refine ⟨442345783185713564854861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9436710041295222716903701 442345783185713564854861)
                  ·
                    rfl

theorem cell22_3876594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_3876594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876594 prefixEnd_3876594 := by exact prefixLift 3876594
  have htrace : WordTrace (prefixWord ++ tailWord_3876594) baseStart_3876594 baseEnd_3876594 := by
    simpa [prefixWord, tailWord_3876594, baseEnd_3876594] using wordTrace_append hprefix tailTrace_3876594
  have hstable : (prefixWord ++ tailWord_3876594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876594).length < 2 ^ (prefixWord ++ tailWord_3876594).sum := by decide
  have hdescent : baseEnd_3876594 < baseStart_3876594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876609 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3876609 : Nat := 118140960795 + 3876609 * 2 ^ 59
def prefixEnd_3876609 : Nat := 4983230072969 + 3 ^ 40 * 3876609 * 2
def baseEnd_3876609 : Nat := 1327042484363685655439537

theorem tailTrace_3876609 : CollatzResearch.WordTrace tailWord_3876609 prefixEnd_3876609 1327042484363685655439537 := by
  unfold tailWord_3876609
  simp only [CollatzResearch.WordTrace]
  refine ⟨141391546012715139952056881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94261030675143426634704587 141391546012715139952056881)
  ·
    refine ⟨106043659509536354964042661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141391546012715139952056881 106043659509536354964042661)
    ·
      refine ⟨19883186158038066555757999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106043659509536354964042661 19883186158038066555757999)
      ·
        refine ⟨29824779237057099833636999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19883186158038066555757999 29824779237057099833636999)
        ·
          refine ⟨44737168855585649750455499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29824779237057099833636999 44737168855585649750455499)
          ·
            refine ⟨67105753283378474625683249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44737168855585649750455499 67105753283378474625683249)
            ·
              refine ⟨50329314962533855969262437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67105753283378474625683249 50329314962533855969262437)
              ·
                refine ⟨9436746555475097994236707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50329314962533855969262437 9436746555475097994236707)
                ·
                  refine ⟨14155119833212646991355061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9436746555475097994236707 14155119833212646991355061)
                  ·
                    refine ⟨1327042484363685655439537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14155119833212646991355061 1327042484363685655439537)
                    ·
                      rfl

theorem cell22_3876609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3876609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876609 prefixEnd_3876609 := by exact prefixLift 3876609
  have htrace : WordTrace (prefixWord ++ tailWord_3876609) baseStart_3876609 baseEnd_3876609 := by
    simpa [prefixWord, tailWord_3876609, baseEnd_3876609] using wordTrace_append hprefix tailTrace_3876609
  have hstable : (prefixWord ++ tailWord_3876609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876609).length < 2 ^ (prefixWord ++ tailWord_3876609).sum := by decide
  have hdescent : baseEnd_3876609 < baseStart_3876609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876611 : List Nat := [1, 1, 1, 3, 2, 2, 5, 3, 4]
def baseStart_3876611 : Nat := 118140960795 + 3876611 * 2 ^ 59
def prefixEnd_3876611 : Nat := 4983230072969 + 3 ^ 40 * 3876611 * 2
def baseEnd_3876611 : Nat := 442347723001519438963177

theorem tailTrace_3876611 : CollatzResearch.WordTrace tailWord_3876611 prefixEnd_3876611 442347723001519438963177 := by
  unfold tailWord_3876611
  simp only [CollatzResearch.WordTrace]
  refine ⟨141391618958707894293629687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94261079305805262862419791 141391618958707894293629687)
  ·
    refine ⟨212087428438061841440444531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141391618958707894293629687 212087428438061841440444531)
    ·
      refine ⟨318131142657092762160666797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212087428438061841440444531 318131142657092762160666797)
      ·
        refine ⟨119299178496409785810250049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318131142657092762160666797 119299178496409785810250049)
        ·
          refine ⟨89474383872307339357687537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119299178496409785810250049 89474383872307339357687537)
          ·
            refine ⟨67105787904230504518265653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89474383872307339357687537 67105787904230504518265653)
            ·
              refine ⟨6291167616021609798587405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67105787904230504518265653 6291167616021609798587405)
              ·
                refine ⟨2359187856008103674470277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6291167616021609798587405 2359187856008103674470277)
                ·
                  refine ⟨442347723001519438963177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2359187856008103674470277 442347723001519438963177)
                  ·
                    rfl

theorem cell22_3876611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 4].length) (baseStart_3876611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876611 prefixEnd_3876611 := by exact prefixLift 3876611
  have htrace : WordTrace (prefixWord ++ tailWord_3876611) baseStart_3876611 baseEnd_3876611 := by
    simpa [prefixWord, tailWord_3876611, baseEnd_3876611] using wordTrace_append hprefix tailTrace_3876611
  have hstable : (prefixWord ++ tailWord_3876611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876611).length < 2 ^ (prefixWord ++ tailWord_3876611).sum := by decide
  have hdescent : baseEnd_3876611 < baseStart_3876611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876621 : List Nat := [1, 7, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3876621 : Nat := 118140960795 + 3876621 * 2 ^ 59
def prefixEnd_3876621 : Nat := 4983230072969 + 3 ^ 40 * 3876621 * 2
def baseEnd_3876621 : Nat := 1327046592208921624139501

theorem tailTrace_3876621 : CollatzResearch.WordTrace tailWord_3876621 prefixEnd_3876621 1327046592208921624139501 := by
  unfold tailWord_3876621
  simp only [CollatzResearch.WordTrace]
  refine ⟨141391983688671666001493717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94261322459114444000995811 141391983688671666001493717)
  ·
    refine ⟨3313874617703242171910009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 141391983688671666001493717 3313874617703242171910009)
    ·
      refine ⟨2485405963277431628932507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3313874617703242171910009 2485405963277431628932507)
      ·
        refine ⟨3728108944916147443398761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2485405963277431628932507 3728108944916147443398761)
        ·
          refine ⟨2796081708687110582549071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3728108944916147443398761 2796081708687110582549071)
          ·
            refine ⟨4194122563030665873823607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796081708687110582549071 4194122563030665873823607)
            ·
              refine ⟨6291183844545998810735411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194122563030665873823607 6291183844545998810735411)
              ·
                refine ⟨9436775766818998216103117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291183844545998810735411 9436775766818998216103117)
                ·
                  refine ⟨3538790912557124331038669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9436775766818998216103117 3538790912557124331038669)
                  ·
                    refine ⟨1327046592208921624139501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538790912557124331038669 1327046592208921624139501)
                    ·
                      rfl

theorem cell22_3876621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3876621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876621 prefixEnd_3876621 := by exact prefixLift 3876621
  have htrace : WordTrace (prefixWord ++ tailWord_3876621) baseStart_3876621 baseEnd_3876621 := by
    simpa [prefixWord, tailWord_3876621, baseEnd_3876621] using wordTrace_append hprefix tailTrace_3876621
  have hstable : (prefixWord ++ tailWord_3876621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876621).length < 2 ^ (prefixWord ++ tailWord_3876621).sum := by decide
  have hdescent : baseEnd_3876621 < baseStart_3876621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876639 : List Nat := [1, 1, 2, 4, 2, 1, 4, 7]
def baseStart_3876639 : Nat := 118140960795 + 3876639 * 2 ^ 59
def prefixEnd_3876639 : Nat := 4983230072969 + 3 ^ 40 * 3876639 * 2
def baseEnd_3876639 : Nat := 147450305997419508576605

theorem tailTrace_3876639 : CollatzResearch.WordTrace tailWord_3876639 prefixEnd_3876639 147450305997419508576605 := by
  unfold tailWord_3876639
  simp only [CollatzResearch.WordTrace]
  refine ⟨141392640202606455075648971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94261760135070970050432647 141392640202606455075648971)
  ·
    refine ⟨212088960303909682613473457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141392640202606455075648971 212088960303909682613473457)
    ·
      refine ⟨159066720227932261960105093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212088960303909682613473457 159066720227932261960105093)
      ·
        refine ⟨29825010042737299117519705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159066720227932261960105093 29825010042737299117519705)
        ·
          refine ⟨22368757532052974338139779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29825010042737299117519705 22368757532052974338139779)
          ·
            refine ⟨33553136298079461507209669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22368757532052974338139779 33553136298079461507209669)
            ·
              refine ⟨6291213055889899032601813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33553136298079461507209669 6291213055889899032601813)
              ·
                refine ⟨147450305997419508576605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6291213055889899032601813 147450305997419508576605)
                ·
                  rfl

theorem cell22_3876639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 7].length) (baseStart_3876639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876639 prefixEnd_3876639 := by exact prefixLift 3876639
  have htrace : WordTrace (prefixWord ++ tailWord_3876639) baseStart_3876639 baseEnd_3876639 := by
    simpa [prefixWord, tailWord_3876639, baseEnd_3876639] using wordTrace_append hprefix tailTrace_3876639
  have hstable : (prefixWord ++ tailWord_3876639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876639).length < 2 ^ (prefixWord ++ tailWord_3876639).sum := by decide
  have hdescent : baseEnd_3876639 < baseStart_3876639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876643 : List Nat := [1, 1, 1, 4, 2, 1, 6, 1, 2, 3]
def baseStart_3876643 : Nat := 118140960795 + 3876643 * 2 ^ 59
def prefixEnd_3876643 : Nat := 4983230072969 + 3 ^ 40 * 3876643 * 2
def baseEnd_3876643 : Nat := 1327054123258520900089433

theorem tailTrace_3876643 : CollatzResearch.WordTrace tailWord_3876643 prefixEnd_3876643 1327054123258520900089433 := by
  unfold tailWord_3876643
  simp only [CollatzResearch.WordTrace]
  refine ⟨141392786094591963758794583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94261857396394642505863055 141392786094591963758794583)
  ·
    refine ⟨212089179141887945638191875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141392786094591963758794583 212089179141887945638191875)
    ·
      refine ⟨318133768712831918457287813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212089179141887945638191875 318133768712831918457287813)
      ·
        refine ⟨59650081633655984710741465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318133768712831918457287813 59650081633655984710741465)
        ·
          refine ⟨44737561225241988533056099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59650081633655984710741465 44737561225241988533056099)
          ·
            refine ⟨67106341837862982799584149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44737561225241988533056099 67106341837862982799584149)
            ·
              refine ⟨3145609773649827318730507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67106341837862982799584149 3145609773649827318730507)
              ·
                refine ⟨4718414660474740978095761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145609773649827318730507 4718414660474740978095761)
                ·
                  refine ⟨3538810995356055733571821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718414660474740978095761 3538810995356055733571821)
                  ·
                    refine ⟨1327054123258520900089433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538810995356055733571821 1327054123258520900089433)
                    ·
                      rfl

theorem cell22_3876643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 3].length) (baseStart_3876643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876643 prefixEnd_3876643 := by exact prefixLift 3876643
  have htrace : WordTrace (prefixWord ++ tailWord_3876643) baseStart_3876643 baseEnd_3876643 := by
    simpa [prefixWord, tailWord_3876643, baseEnd_3876643] using wordTrace_append hprefix tailTrace_3876643
  have hstable : (prefixWord ++ tailWord_3876643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876643).length < 2 ^ (prefixWord ++ tailWord_3876643).sum := by decide
  have hdescent : baseEnd_3876643 < baseStart_3876643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876729 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 8]
def baseStart_3876729 : Nat := 118140960795 + 3876729 * 2 ^ 59
def prefixEnd_3876729 : Nat := 4983230072969 + 3 ^ 40 * 3876729 * 2
def baseEnd_3876729 : Nat := 442361187605348447479723

theorem tailTrace_3876729 : CollatzResearch.WordTrace tailWord_3876729 prefixEnd_3876729 442361187605348447479723 := by
  unfold tailWord_3876729
  simp only [CollatzResearch.WordTrace]
  refine ⟨141395922772280400446425241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94263948514853600297616827 141395922772280400446425241)
  ·
    refine ⟨106046942079210300334818931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141395922772280400446425241 106046942079210300334818931)
    ·
      refine ⟨159070413118815450502228397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106046942079210300334818931 159070413118815450502228397)
      ·
        refine ⟨59651404919555793938335649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159070413118815450502228397 59651404919555793938335649)
        ·
          refine ⟨44738553689666845453751737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59651404919555793938335649 44738553689666845453751737)
          ·
            refine ⟨33553915267250134090313803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44738553689666845453751737 33553915267250134090313803)
            ·
              refine ⟨50330872900875201135470705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33553915267250134090313803 50330872900875201135470705)
              ·
                refine ⟨37748154675656400851603029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50330872900875201135470705 37748154675656400851603029)
                ·
                  refine ⟨442361187605348447479723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37748154675656400851603029 442361187605348447479723)
                  ·
                    rfl

theorem cell22_3876729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_3876729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876729 prefixEnd_3876729 := by exact prefixLift 3876729
  have htrace : WordTrace (prefixWord ++ tailWord_3876729) baseStart_3876729 baseEnd_3876729 := by
    simpa [prefixWord, tailWord_3876729, baseEnd_3876729] using wordTrace_append hprefix tailTrace_3876729
  have hstable : (prefixWord ++ tailWord_3876729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876729).length < 2 ^ (prefixWord ++ tailWord_3876729).sum := by decide
  have hdescent : baseEnd_3876729 < baseStart_3876729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876761 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_3876761 : Nat := 118140960795 + 3876761 * 2 ^ 59
def prefixEnd_3876761 : Nat := 4983230072969 + 3 ^ 40 * 3876761 * 2
def baseEnd_3876761 : Nat := 1327094517070007925639071

theorem tailTrace_3876761 : CollatzResearch.WordTrace tailWord_3876761 prefixEnd_3876761 1327094517070007925639071 := by
  unfold tailWord_3876761
  simp only [CollatzResearch.WordTrace]
  refine ⟨141397089908164469911590137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94264726605442979941060091 141397089908164469911590137)
  ·
    refine ⟨106047817431123352433692603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141397089908164469911590137 106047817431123352433692603)
    ·
      refine ⟨159071726146685028650538905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106047817431123352433692603 159071726146685028650538905)
      ·
        refine ⟨119303794610013771487904179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159071726146685028650538905 119303794610013771487904179)
        ·
          refine ⟨178955691915020657231856269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119303794610013771487904179 178955691915020657231856269)
          ·
            refine ⟨67108384468132746461946101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178955691915020657231856269 67108384468132746461946101)
            ·
              refine ⟨6291411043887444980807447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67108384468132746461946101 6291411043887444980807447)
              ·
                refine ⟨9437116565831167471211171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291411043887444980807447 9437116565831167471211171)
                ·
                  refine ⟨14155674848746751206816757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9437116565831167471211171 14155674848746751206816757)
                  ·
                    refine ⟨1327094517070007925639071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14155674848746751206816757 1327094517070007925639071)
                    ·
                      rfl

theorem cell22_3876761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_3876761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876761 prefixEnd_3876761 := by exact prefixLift 3876761
  have htrace : WordTrace (prefixWord ++ tailWord_3876761) baseStart_3876761 baseEnd_3876761 := by
    simpa [prefixWord, tailWord_3876761, baseEnd_3876761] using wordTrace_append hprefix tailTrace_3876761
  have hstable : (prefixWord ++ tailWord_3876761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876761).length < 2 ^ (prefixWord ++ tailWord_3876761).sum := by decide
  have hdescent : baseEnd_3876761 < baseStart_3876761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876812 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 2, 3]
def baseStart_3876812 : Nat := 118140960795 + 3876812 * 2 ^ 59
def prefixEnd_3876812 : Nat := 4983230072969 + 3 ^ 40 * 3876812 * 2
def baseEnd_3876812 : Nat := 1327111975412260792613915

theorem tailTrace_3876812 : CollatzResearch.WordTrace tailWord_3876812 prefixEnd_3876812 1327111975412260792613915 := by
  unfold tailWord_3876812
  simp only [CollatzResearch.WordTrace]
  refine ⟨70699475015489852810848345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94265966687319803747797793 70699475015489852810848345)
  ·
    refine ⟨53024606261617389608136259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70699475015489852810848345 53024606261617389608136259)
    ·
      refine ⟨79536909392426084412204389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53024606261617389608136259 79536909392426084412204389)
      ·
        refine ⟨14913170511079890827288323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79536909392426084412204389 14913170511079890827288323)
        ·
          refine ⟨22369755766619836240932485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14913170511079890827288323 22369755766619836240932485)
          ·
            refine ⟨4194329206241219295174841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22369755766619836240932485 4194329206241219295174841)
            ·
              refine ⟨3145746904680914471381131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4194329206241219295174841 3145746904680914471381131)
              ·
                refine ⟨4718620357021371707071697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145746904680914471381131 4718620357021371707071697)
                ·
                  refine ⟨3538965267766028780303773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718620357021371707071697 3538965267766028780303773)
                  ·
                    refine ⟨1327111975412260792613915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538965267766028780303773 1327111975412260792613915)
                    ·
                      rfl

theorem cell22_3876812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_3876812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876812 prefixEnd_3876812 := by exact prefixLift 3876812
  have htrace : WordTrace (prefixWord ++ tailWord_3876812) baseStart_3876812 baseEnd_3876812 := by
    simpa [prefixWord, tailWord_3876812, baseEnd_3876812] using wordTrace_append hprefix tailTrace_3876812
  have hstable : (prefixWord ++ tailWord_3876812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876812).length < 2 ^ (prefixWord ++ tailWord_3876812).sum := by decide
  have hdescent : baseEnd_3876812 < baseStart_3876812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876840 : List Nat := [2, 1, 4, 1, 1, 1, 1, 7, 1, 3]
def baseStart_3876840 : Nat := 118140960795 + 3876840 * 2 ^ 59
def prefixEnd_3876840 : Nat := 4983230072969 + 3 ^ 40 * 3876840 * 2
def baseEnd_3876840 : Nat := 1327121560384478052913829

theorem tailTrace_3876840 : CollatzResearch.WordTrace tailWord_3876840 prefixEnd_3876840 1327121560384478052913829 := by
  unfold tailWord_3876840
  simp only [CollatzResearch.WordTrace]
  refine ⟨70699985637439133201857987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94266647516585510935810649 70699985637439133201857987)
  ·
    refine ⟨106049978456158699802786981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70699985637439133201857987 106049978456158699802786981)
    ·
      refine ⟨19884370960529756213022559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106049978456158699802786981 19884370960529756213022559)
      ·
        refine ⟨29826556440794634319533839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19884370960529756213022559 29826556440794634319533839)
        ·
          refine ⟨44739834661191951479300759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29826556440794634319533839 44739834661191951479300759)
          ·
            refine ⟨67109751991787927218951139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44739834661191951479300759 67109751991787927218951139)
            ·
              refine ⟨100664627987681890828426709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67109751991787927218951139 100664627987681890828426709)
              ·
                refine ⟨2359327218461294316291251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100664627987681890828426709 2359327218461294316291251)
                ·
                  refine ⟨3538990827691941474436877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359327218461294316291251 3538990827691941474436877)
                  ·
                    refine ⟨1327121560384478052913829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538990827691941474436877 1327121560384478052913829)
                    ·
                      rfl

theorem cell22_3876840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_3876840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876840 prefixEnd_3876840 := by exact prefixLift 3876840
  have htrace : WordTrace (prefixWord ++ tailWord_3876840) baseStart_3876840 baseEnd_3876840 := by
    simpa [prefixWord, tailWord_3876840, baseEnd_3876840] using wordTrace_append hprefix tailTrace_3876840
  have hstable : (prefixWord ++ tailWord_3876840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876840).length < 2 ^ (prefixWord ++ tailWord_3876840).sum := by decide
  have hdescent : baseEnd_3876840 < baseStart_3876840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876857 : List Nat := [1, 2, 1, 3, 1, 4, 4, 2, 1, 3]
def baseStart_3876857 : Nat := 118140960795 + 3876857 * 2 ^ 59
def prefixEnd_3876857 : Nat := 4983230072969 + 3 ^ 40 * 3876857 * 2
def baseEnd_3876857 : Nat := 1327127379831895675238777

theorem tailTrace_3876857 : CollatzResearch.WordTrace tailWord_3876857 prefixEnd_3876857 1327127379831895675238777 := by
  unfold tailWord_3876857
  simp only [CollatzResearch.WordTrace]
  refine ⟨141400591315816678307084825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94267060877211118871389883 141400591315816678307084825)
  ·
    refine ⟨106050443486862508730313619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141400591315816678307084825 106050443486862508730313619)
    ·
      refine ⟨159075665230293763095470429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106050443486862508730313619 159075665230293763095470429)
      ·
        refine ⟨59653374461360161160801411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159075665230293763095470429 59653374461360161160801411)
        ·
          refine ⟨89480061692040241741202117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59653374461360161160801411 89480061692040241741202117)
          ·
            refine ⟨16777511567257545326475397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89480061692040241741202117 16777511567257545326475397)
            ·
              refine ⟨3145783418860789748714137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16777511567257545326475397 3145783418860789748714137)
              ·
                refine ⟨2359337564145592311535603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3145783418860789748714137 2359337564145592311535603)
                ·
                  refine ⟨3539006346218388467303405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359337564145592311535603 3539006346218388467303405)
                  ·
                    refine ⟨1327127379831895675238777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539006346218388467303405 1327127379831895675238777)
                    ·
                      rfl

theorem cell22_3876857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 1, 3].length) (baseStart_3876857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876857 prefixEnd_3876857 := by exact prefixLift 3876857
  have htrace : WordTrace (prefixWord ++ tailWord_3876857) baseStart_3876857 baseEnd_3876857 := by
    simpa [prefixWord, tailWord_3876857, baseEnd_3876857] using wordTrace_append hprefix tailTrace_3876857
  have hstable : (prefixWord ++ tailWord_3876857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876857).length < 2 ^ (prefixWord ++ tailWord_3876857).sum := by decide
  have hdescent : baseEnd_3876857 < baseStart_3876857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876904 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 5]
def baseStart_3876904 : Nat := 118140960795 + 3876904 * 2 ^ 59
def prefixEnd_3876904 : Nat := 4983230072969 + 3 ^ 40 * 3876904 * 2
def baseEnd_3876904 : Nat := 442381156297467739771211

theorem tailTrace_3876904 : CollatzResearch.WordTrace tailWord_3876904 prefixEnd_3876904 442381156297467739771211 := by
  unfold tailWord_3876904
  simp only [CollatzResearch.WordTrace]
  refine ⟨70701152773323202667022883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94268203697764270222697177 70701152773323202667022883)
  ·
    refine ⟨106051729159984804000534325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70701152773323202667022883 106051729159984804000534325)
    ·
      refine ⟨9942349608748575375050093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106051729159984804000534325 9942349608748575375050093)
      ·
        refine ⟨3728381103280715765643785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9942349608748575375050093 3728381103280715765643785)
        ·
          refine ⟨2796285827460536824232839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3728381103280715765643785 2796285827460536824232839)
          ·
            refine ⟨4194428741190805236349259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796285827460536824232839 4194428741190805236349259)
            ·
              refine ⟨6291643111786207854523889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194428741190805236349259 6291643111786207854523889)
              ·
                refine ⟨4718732333839655890892917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6291643111786207854523889 4718732333839655890892917)
                ·
                  refine ⟨442381156297467739771211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4718732333839655890892917 442381156297467739771211)
                  ·
                    rfl

theorem cell22_3876904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 5].length) (baseStart_3876904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876904 prefixEnd_3876904 := by exact prefixLift 3876904
  have htrace : WordTrace (prefixWord ++ tailWord_3876904) baseStart_3876904 baseEnd_3876904 := by
    simpa [prefixWord, tailWord_3876904, baseEnd_3876904] using wordTrace_append hprefix tailTrace_3876904
  have hstable : (prefixWord ++ tailWord_3876904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876904).length < 2 ^ (prefixWord ++ tailWord_3876904).sum := by decide
  have hdescent : baseEnd_3876904 < baseStart_3876904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876962 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3876962 : Nat := 118140960795 + 3876962 * 2 ^ 59
def prefixEnd_3876962 : Nat := 4983230072969 + 3 ^ 40 * 3876962 * 2
def baseEnd_3876962 : Nat := 1327163323477710401363455

theorem tailTrace_3876962 : CollatzResearch.WordTrace tailWord_3876962 prefixEnd_3876962 1327163323477710401363455 := by
  unfold tailWord_3876962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35351105245109070309914285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94269613986957520826438093 35351105245109070309914285)
  ·
    refine ⟨13256664466915901366217857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35351105245109070309914285 13256664466915901366217857)
    ·
      refine ⟨9942498350186926024663393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13256664466915901366217857 9942498350186926024663393)
      ·
        refine ⟨7456873762640194518497545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9942498350186926024663393 7456873762640194518497545)
        ·
          refine ⟨5592655321980145888873159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7456873762640194518497545 5592655321980145888873159)
          ·
            refine ⟨8388982982970218833309739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592655321980145888873159 8388982982970218833309739)
            ·
              refine ⟨12583474474455328249964609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8388982982970218833309739 12583474474455328249964609)
              ·
                refine ⟨9437605855841496187473457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12583474474455328249964609 9437605855841496187473457)
                ·
                  refine ⟨7078204391881122140605093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9437605855841496187473457 7078204391881122140605093)
                  ·
                    refine ⟨1327163323477710401363455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7078204391881122140605093 1327163323477710401363455)
                    ·
                      rfl

theorem cell22_3876962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3876962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876962 prefixEnd_3876962 := by exact prefixLift 3876962
  have htrace : WordTrace (prefixWord ++ tailWord_3876962) baseStart_3876962 baseEnd_3876962 := by
    simpa [prefixWord, tailWord_3876962, baseEnd_3876962] using wordTrace_append hprefix tailTrace_3876962
  have hstable : (prefixWord ++ tailWord_3876962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876962).length < 2 ^ (prefixWord ++ tailWord_3876962).sum := by decide
  have hdescent : baseEnd_3876962 < baseStart_3876962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876973 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3876973 : Nat := 118140960795 + 3876973 * 2 ^ 59
def prefixEnd_3876973 : Nat := 4983230072969 + 3 ^ 40 * 3876973 * 2
def baseEnd_3876973 : Nat := 1327167089002510039338421

theorem tailTrace_3876973 : CollatzResearch.WordTrace tailWord_3876973 prefixEnd_3876973 1327167089002510039338421 := by
  unfold tailWord_3876973
  simp only [CollatzResearch.WordTrace]
  refine ⟨141404822183396430118307573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94269881455597620078871715 141404822183396430118307573)
  ·
    refine ⟨13256702079693415323591335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141404822183396430118307573 13256702079693415323591335)
    ·
      refine ⟨19885053119540122985387003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13256702079693415323591335 19885053119540122985387003)
      ·
        refine ⟨29827579679310184478080505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19885053119540122985387003 29827579679310184478080505)
        ·
          refine ⟨22370684759482638358560379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29827579679310184478080505 22370684759482638358560379)
          ·
            refine ⟨33556027139223957537840569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22370684759482638358560379 33556027139223957537840569)
            ·
              refine ⟨25167020354417968153380427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33556027139223957537840569 25167020354417968153380427)
              ·
                refine ⟨37750530531626952230070641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25167020354417968153380427 37750530531626952230070641)
                ·
                  refine ⟨28312897898720214172552981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37750530531626952230070641 28312897898720214172552981)
                  ·
                    refine ⟨1327167089002510039338421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28312897898720214172552981 1327167089002510039338421)
                    ·
                      rfl

theorem cell22_3876973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3876973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876973 prefixEnd_3876973 := by exact prefixLift 3876973
  have htrace : WordTrace (prefixWord ++ tailWord_3876973) baseStart_3876973 baseEnd_3876973 := by
    simpa [prefixWord, tailWord_3876973, baseEnd_3876973] using wordTrace_append hprefix tailTrace_3876973
  have hstable : (prefixWord ++ tailWord_3876973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876973).length < 2 ^ (prefixWord ++ tailWord_3876973).sum := by decide
  have hdescent : baseEnd_3876973 < baseStart_3876973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876975 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 3, 3]
def baseStart_3876975 : Nat := 118140960795 + 3876975 * 2 ^ 59
def prefixEnd_3876975 : Nat := 4983230072969 + 3 ^ 40 * 3876975 * 2
def baseEnd_3876975 : Nat := 1327167773643382700788415

theorem tailTrace_3876975 : CollatzResearch.WordTrace tailWord_3876975 prefixEnd_3876975 1327167773643382700788415 := by
  unfold tailWord_3876975
  simp only [CollatzResearch.WordTrace]
  refine ⟨141404895129389184459880379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94269930086259456306586919 141404895129389184459880379)
  ·
    refine ⟨212107342694083776689820569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141404895129389184459880379 212107342694083776689820569)
    ·
      refine ⟨159080507020562832517365427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212107342694083776689820569 159080507020562832517365427)
      ·
        refine ⟨238620760530844248776048141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159080507020562832517365427 238620760530844248776048141)
        ·
          refine ⟨89482785199066593291018053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238620760530844248776048141 89482785199066593291018053)
          ·
            refine ⟨16778022224824986242065885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89482785199066593291018053 16778022224824986242065885)
            ·
              refine ⟨6291758334309369840774707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16778022224824986242065885 6291758334309369840774707)
              ·
                refine ⟨9437637501464054761162061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291758334309369840774707 9437637501464054761162061)
                ·
                  refine ⟨3539114063049020535435773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9437637501464054761162061 3539114063049020535435773)
                  ·
                    refine ⟨1327167773643382700788415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539114063049020535435773 1327167773643382700788415)
                    ·
                      rfl

theorem cell22_3876975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_3876975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3876975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3876975 prefixEnd_3876975 := by exact prefixLift 3876975
  have htrace : WordTrace (prefixWord ++ tailWord_3876975) baseStart_3876975 baseEnd_3876975 := by
    simpa [prefixWord, tailWord_3876975, baseEnd_3876975] using wordTrace_append hprefix tailTrace_3876975
  have hstable : (prefixWord ++ tailWord_3876975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876975).length < 2 ^ (prefixWord ++ tailWord_3876975).sum := by decide
  have hdescent : baseEnd_3876975 < baseStart_3876975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877026 : List Nat := [3, 3, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_3877026 : Nat := 118140960795 + 3877026 * 2 ^ 59
def prefixEnd_3877026 : Nat := 4983230072969 + 3 ^ 40 * 3877026 * 2
def baseEnd_3877026 : Nat := 1327185231985635567763259

theorem tailTrace_3877026 : CollatzResearch.WordTrace tailWord_3877026 prefixEnd_3877026 1327185231985635567763259 := by
  unfold tailWord_3877026
  simp only [CollatzResearch.WordTrace]
  refine ⟨35351688813051105042496733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94271170168136280113324621 35351688813051105042496733)
  ·
    refine ⟨13256883304894164390936275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35351688813051105042496733 13256883304894164390936275)
    ·
      refine ⟨19885324957341246586404413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13256883304894164390936275 19885324957341246586404413)
      ·
        refine ⟨7456996859002967469901655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19885324957341246586404413 7456996859002967469901655)
        ·
          refine ⟨11185495288504451204852483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7456996859002967469901655 11185495288504451204852483)
          ·
            refine ⟨16778242932756676807278725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11185495288504451204852483 16778242932756676807278725)
            ·
              refine ⟨3145920549891876901364761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16778242932756676807278725 3145920549891876901364761)
              ·
                refine ⟨2359440412418907676023571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3145920549891876901364761 2359440412418907676023571)
                ·
                  refine ⟨3539160618628361514035357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359440412418907676023571 3539160618628361514035357)
                  ·
                    refine ⟨1327185231985635567763259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539160618628361514035357 1327185231985635567763259)
                    ·
                      rfl

theorem cell22_3877026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_3877026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877026 prefixEnd_3877026 := by exact prefixLift 3877026
  have htrace : WordTrace (prefixWord ++ tailWord_3877026) baseStart_3877026 baseEnd_3877026 := by
    simpa [prefixWord, tailWord_3877026, baseEnd_3877026] using wordTrace_append hprefix tailTrace_3877026
  have hstable : (prefixWord ++ tailWord_3877026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877026).length < 2 ^ (prefixWord ++ tailWord_3877026).sum := by decide
  have hdescent : baseEnd_3877026 < baseStart_3877026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877082 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_3877082 : Nat := 118140960795 + 3877082 * 2 ^ 59
def prefixEnd_3877082 : Nat := 4983230072969 + 3 ^ 40 * 3877082 * 2
def baseEnd_3877082 : Nat := 1327204401930070088363087

theorem tailTrace_3877082 : CollatzResearch.WordTrace tailWord_3877082 prefixEnd_3877082 1327204401930070088363087 := by
  unfold tailWord_3877082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35352199435000385433506375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94272531826667694489350333 35352199435000385433506375)
  ·
    refine ⟨53028299152500578150259563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35352199435000385433506375 53028299152500578150259563)
    ·
      refine ⟨79542448728750867225389345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53028299152500578150259563 79542448728750867225389345)
      ·
        refine ⟨59656836546563150419042009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79542448728750867225389345 59656836546563150419042009)
        ·
          refine ⟨44742627409922362814281507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59656836546563150419042009 44742627409922362814281507)
          ·
            refine ⟨67113941114883544221422261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44742627409922362814281507 67113941114883544221422261)
            ·
              refine ⟨6291931979520332270758337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67113941114883544221422261 6291931979520332270758337)
              ·
                refine ⟨4718948984640249203068753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6291931979520332270758337 4718948984640249203068753)
                ·
                  refine ⟨3539211738480186902301565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718948984640249203068753 3539211738480186902301565)
                  ·
                    refine ⟨1327204401930070088363087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539211738480186902301565 1327204401930070088363087)
                    ·
                      rfl

theorem cell22_3877082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_3877082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877082 prefixEnd_3877082 := by exact prefixLift 3877082
  have htrace : WordTrace (prefixWord ++ tailWord_3877082) baseStart_3877082 baseEnd_3877082 := by
    simpa [prefixWord, tailWord_3877082, baseEnd_3877082] using wordTrace_append hprefix tailTrace_3877082
  have hstable : (prefixWord ++ tailWord_3877082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877082).length < 2 ^ (prefixWord ++ tailWord_3877082).sum := by decide
  have hdescent : baseEnd_3877082 < baseStart_3877082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877084 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 6]
def baseStart_3877084 : Nat := 118140960795 + 3877084 * 2 ^ 59
def prefixEnd_3877084 : Nat := 4983230072969 + 3 ^ 40 * 3877084 * 2
def baseEnd_3877084 : Nat := 442401695523647583271027

theorem tailTrace_3877084 : CollatzResearch.WordTrace tailWord_3877084 prefixEnd_3877084 442401695523647583271027 := by
  unfold tailWord_3877084
  simp only [CollatzResearch.WordTrace]
  refine ⟨70704435342997148037799153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94272580457329530717065537 70704435342997148037799153)
  ·
    refine ⟨53028326507247861028349365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70704435342997148037799153 53028326507247861028349365)
    ·
      refine ⟨4971405610054486971407753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53028326507247861028349365 4971405610054486971407753)
      ·
        refine ⟨3728554207540865228555815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4971405610054486971407753 3728554207540865228555815)
        ·
          refine ⟨5592831311311297842833723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3728554207540865228555815 5592831311311297842833723)
          ·
            refine ⟨8389246966966946764250585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592831311311297842833723 8389246966966946764250585)
            ·
              refine ⟨6291935225225210073187939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8389246966966946764250585 6291935225225210073187939)
              ·
                refine ⟨9437902837837815109781909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291935225225210073187939 9437902837837815109781909)
                ·
                  refine ⟨442401695523647583271027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9437902837837815109781909 442401695523647583271027)
                  ·
                    rfl

theorem cell22_3877084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_3877084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877084 prefixEnd_3877084 := by exact prefixLift 3877084
  have htrace : WordTrace (prefixWord ++ tailWord_3877084) baseStart_3877084 baseEnd_3877084 := by
    simpa [prefixWord, tailWord_3877084, baseEnd_3877084] using wordTrace_append hprefix tailTrace_3877084
  have hstable : (prefixWord ++ tailWord_3877084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877084).length < 2 ^ (prefixWord ++ tailWord_3877084).sum := by decide
  have hdescent : baseEnd_3877084 < baseStart_3877084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877123 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 9]
def baseStart_3877123 : Nat := 118140960795 + 3877123 * 2 ^ 59
def prefixEnd_3877123 : Nat := 4983230072969 + 3 ^ 40 * 3877123 * 2
def baseEnd_3877123 : Nat := 442406145689319882695987

theorem tailTrace_3877123 : CollatzResearch.WordTrace tailWord_3877123 prefixEnd_3877123 442406145689319882695987 := by
  unfold tailWord_3877123
  simp only [CollatzResearch.WordTrace]
  refine ⟨141410293132853005736268023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94273528755235337157512015 141410293132853005736268023)
  ·
    refine ⟨212115439699279508604402035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141410293132853005736268023 212115439699279508604402035)
    ·
      refine ⟨318173159548919262906603053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212115439699279508604402035 318173159548919262906603053)
      ·
        refine ⟨119314934830844723589976145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318173159548919262906603053 119314934830844723589976145)
        ·
          refine ⟨89486201123133542692482109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119314934830844723589976145 89486201123133542692482109)
          ·
            refine ⟨33557325421175078509680791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89486201123133542692482109 33557325421175078509680791)
            ·
              refine ⟨50335988131762617764521187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33557325421175078509680791 50335988131762617764521187)
              ·
                refine ⟨75503982197643926646781781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50335988131762617764521187 75503982197643926646781781)
                ·
                  refine ⟨442406145689319882695987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75503982197643926646781781 442406145689319882695987)
                  ·
                    rfl

theorem cell22_3877123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 9].length) (baseStart_3877123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877123 prefixEnd_3877123 := by exact prefixLift 3877123
  have htrace : WordTrace (prefixWord ++ tailWord_3877123) baseStart_3877123 baseEnd_3877123 := by
    simpa [prefixWord, tailWord_3877123, baseEnd_3877123] using wordTrace_append hprefix tailTrace_3877123
  have hstable : (prefixWord ++ tailWord_3877123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877123).length < 2 ^ (prefixWord ++ tailWord_3877123).sum := by decide
  have hdescent : baseEnd_3877123 < baseStart_3877123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877157 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 5]
def baseStart_3877157 : Nat := 118140960795 + 3877157 * 2 ^ 59
def prefixEnd_3877157 : Nat := 4983230072969 + 3 ^ 40 * 3877157 * 2
def baseEnd_3877157 : Nat := 442410025320931630912619

theorem tailTrace_3877157 : CollatzResearch.WordTrace tailWord_3877157 prefixEnd_3877157 442410025320931630912619 := by
  unfold tailWord_3877157
  simp only [CollatzResearch.WordTrace]
  refine ⟨141411533214729829543005725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94274355476486553028670483 141411533214729829543005725)
  ·
    refine ⟨53029324955523686078627147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141411533214729829543005725 53029324955523686078627147)
    ·
      refine ⟨79543987433285529117940721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53029324955523686078627147 79543987433285529117940721)
      ·
        refine ⟨59657990574964146838455541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79543987433285529117940721 59657990574964146838455541)
        ·
          refine ⟨5592936616402888766105207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59657990574964146838455541 5592936616402888766105207)
          ·
            refine ⟨8389404924604333149157811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592936616402888766105207 8389404924604333149157811)
            ·
              refine ⟨12584107386906499723736717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8389404924604333149157811 12584107386906499723736717)
              ·
                refine ⟨4719040270089937396401269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12584107386906499723736717 4719040270089937396401269)
                ·
                  refine ⟨442410025320931630912619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4719040270089937396401269 442410025320931630912619)
                  ·
                    rfl

theorem cell22_3877157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_3877157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877157 prefixEnd_3877157 := by exact prefixLift 3877157
  have htrace : WordTrace (prefixWord ++ tailWord_3877157) baseStart_3877157 baseEnd_3877157 := by
    simpa [prefixWord, tailWord_3877157, baseEnd_3877157] using wordTrace_append hprefix tailTrace_3877157
  have hstable : (prefixWord ++ tailWord_3877157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877157).length < 2 ^ (prefixWord ++ tailWord_3877157).sum := by decide
  have hdescent : baseEnd_3877157 < baseStart_3877157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877215 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 4, 4]
def baseStart_3877215 : Nat := 118140960795 + 3877215 * 2 ^ 59
def prefixEnd_3877215 : Nat := 4983230072969 + 3 ^ 40 * 3877215 * 2
def baseEnd_3877215 : Nat := 1327249930548102074787679

theorem tailTrace_3877215 : CollatzResearch.WordTrace tailWord_3877215 prefixEnd_3877215 1327249930548102074787679 := by
  unfold tailWord_3877215
  simp only [CollatzResearch.WordTrace]
  refine ⟨141413648648519705448617099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94275765765679803632411399 141413648648519705448617099)
  ·
    refine ⟨212120472972779558172925649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141413648648519705448617099 212120472972779558172925649)
    ·
      refine ⟨159090354729584668629694237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212120472972779558172925649 159090354729584668629694237)
      ·
        refine ⟨59658883023594250736135339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159090354729584668629694237 59658883023594250736135339)
        ·
          refine ⟨89488324535391376104203009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59658883023594250736135339 89488324535391376104203009)
          ·
            refine ⟨67116243401543532078152257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89488324535391376104203009 67116243401543532078152257)
            ·
              refine ⟨50337182551157649058614193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67116243401543532078152257 50337182551157649058614193)
              ·
                refine ⟨37752886913368236793960645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50337182551157649058614193 37752886913368236793960645)
                ·
                  refine ⟨7078666296256544398867621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37752886913368236793960645 7078666296256544398867621)
                  ·
                    refine ⟨1327249930548102074787679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7078666296256544398867621 1327249930548102074787679)
                    ·
                      rfl

theorem cell22_3877215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_3877215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877215 prefixEnd_3877215 := by exact prefixLift 3877215
  have htrace : WordTrace (prefixWord ++ tailWord_3877215) baseStart_3877215 baseEnd_3877215 := by
    simpa [prefixWord, tailWord_3877215, baseEnd_3877215] using wordTrace_append hprefix tailTrace_3877215
  have hstable : (prefixWord ++ tailWord_3877215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877215).length < 2 ^ (prefixWord ++ tailWord_3877215).sum := by decide
  have hdescent : baseEnd_3877215 < baseStart_3877215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877232 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_3877232 : Nat := 118140960795 + 3877232 * 2 ^ 59
def prefixEnd_3877232 : Nat := 4983230072969 + 3 ^ 40 * 3877232 * 2
def baseEnd_3877232 : Nat := 1327255749995519697112627

theorem tailTrace_3877232 : CollatzResearch.WordTrace tailWord_3877232 prefixEnd_3877232 1327255749995519697112627 := by
  unfold tailWord_3877232
  simp only [CollatzResearch.WordTrace]
  refine ⟨70707134344729058675992975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94276179126305411567990633 70707134344729058675992975)
  ·
    refine ⟨106060701517093588013989463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70707134344729058675992975 106060701517093588013989463)
    ·
      refine ⟨159091052275640382020984195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106060701517093588013989463 159091052275640382020984195)
      ·
        refine ⟨238636578413460573031476293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159091052275640382020984195 238636578413460573031476293)
        ·
          refine ⟨44744358452523857443401805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238636578413460573031476293 44744358452523857443401805)
          ·
            refine ⟨16779134419696446541275677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44744358452523857443401805 16779134419696446541275677)
            ·
              refine ⟨6292175407386167452978379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16779134419696446541275677 6292175407386167452978379)
              ·
                refine ⟨9438263111079251179467569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292175407386167452978379 9438263111079251179467569)
                ·
                  refine ⟨7078697333309438384600677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9438263111079251179467569 7078697333309438384600677)
                  ·
                    refine ⟨1327255749995519697112627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7078697333309438384600677 1327255749995519697112627)
                    ·
                      rfl

theorem cell22_3877232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_3877232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877232 prefixEnd_3877232 := by exact prefixLift 3877232
  have htrace : WordTrace (prefixWord ++ tailWord_3877232) baseStart_3877232 baseEnd_3877232 := by
    simpa [prefixWord, tailWord_3877232, baseEnd_3877232] using wordTrace_append hprefix tailTrace_3877232
  have hstable : (prefixWord ++ tailWord_3877232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877232).length < 2 ^ (prefixWord ++ tailWord_3877232).sum := by decide
  have hdescent : baseEnd_3877232 < baseStart_3877232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877251 : List Nat := [1, 1, 1, 3, 6, 2, 1, 2, 2, 3]
def baseStart_3877251 : Nat := 118140960795 + 3877251 * 2 ^ 59
def prefixEnd_3877251 : Nat := 4983230072969 + 3 ^ 40 * 3877251 * 2
def baseEnd_3877251 : Nat := 1327262254083809980887569

theorem tailTrace_3877251 : CollatzResearch.WordTrace tailWord_3877251 prefixEnd_3877251 1327262254083809980887569 := by
  unfold tailWord_3877251
  simp only [CollatzResearch.WordTrace]
  refine ⟨141414961676389283596927607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94276641117592855731285071 141414961676389283596927607)
  ·
    refine ⟨212122442514583925395391411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141414961676389283596927607 212122442514583925395391411)
    ·
      refine ⟨318183663771875888093087117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212122442514583925395391411 318183663771875888093087117)
      ·
        refine ⟨119318873914453458034907669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318183663771875888093087117 119318873914453458034907669)
        ·
          refine ⟨5593072214740005845386297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119318873914453458034907669 5593072214740005845386297)
          ·
            refine ⟨4194804161055004384039723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5593072214740005845386297 4194804161055004384039723)
            ·
              refine ⟨6292206241582506576059585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194804161055004384039723 6292206241582506576059585)
              ·
                refine ⟨4719154681186879932044689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6292206241582506576059585 4719154681186879932044689)
                ·
                  refine ⟨3539366010890159949033517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4719154681186879932044689 3539366010890159949033517)
                  ·
                    refine ⟨1327262254083809980887569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539366010890159949033517 1327262254083809980887569)
                    ·
                      rfl

theorem cell22_3877251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 3].length) (baseStart_3877251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877251 prefixEnd_3877251 := by exact prefixLift 3877251
  have htrace : WordTrace (prefixWord ++ tailWord_3877251) baseStart_3877251 baseEnd_3877251 := by
    simpa [prefixWord, tailWord_3877251, baseEnd_3877251] using wordTrace_append hprefix tailTrace_3877251
  have hstable : (prefixWord ++ tailWord_3877251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877251).length < 2 ^ (prefixWord ++ tailWord_3877251).sum := by decide
  have hdescent : baseEnd_3877251 < baseStart_3877251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877268 : List Nat := [2, 4, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_3877268 : Nat := 118140960795 + 3877268 * 2 ^ 59
def prefixEnd_3877268 : Nat := 4983230072969 + 3 ^ 40 * 3877268 * 2
def baseEnd_3877268 : Nat := 1327268073531227603212517

theorem tailTrace_3877268 : CollatzResearch.WordTrace tailWord_3877268 prefixEnd_3877268 1327268073531227603212517 := by
  unfold tailWord_3877268
  simp only [CollatzResearch.WordTrace]
  refine ⟨70707790858663847750148229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94277054478218463666864305 70707790858663847750148229)
  ·
    refine ⟨13257710785999471453152793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70707790858663847750148229 13257710785999471453152793)
    ·
      refine ⟨9943283089499603589864595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13257710785999471453152793 9943283089499603589864595)
      ·
        refine ⟨14914924634249405384796893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9943283089499603589864595 14914924634249405384796893)
        ·
          refine ⟨5593096737843527019298835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14914924634249405384796893 5593096737843527019298835)
          ·
            refine ⟨8389645106765290528948253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5593096737843527019298835 8389645106765290528948253)
            ·
              refine ⟨3146116915036983948355595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8389645106765290528948253 3146116915036983948355595)
              ·
                refine ⟨4719175372555475922533393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146116915036983948355595 4719175372555475922533393)
                ·
                  refine ⟨3539381529416606941900045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4719175372555475922533393 3539381529416606941900045)
                  ·
                    refine ⟨1327268073531227603212517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539381529416606941900045 1327268073531227603212517)
                    ·
                      rfl

theorem cell22_3877268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_3877268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877268 prefixEnd_3877268 := by exact prefixLift 3877268
  have htrace : WordTrace (prefixWord ++ tailWord_3877268) baseStart_3877268 baseEnd_3877268 := by
    simpa [prefixWord, tailWord_3877268, baseEnd_3877268] using wordTrace_append hprefix tailTrace_3877268
  have hstable : (prefixWord ++ tailWord_3877268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877268).length < 2 ^ (prefixWord ++ tailWord_3877268).sum := by decide
  have hdescent : baseEnd_3877268 < baseStart_3877268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877281 : List Nat := [1, 2, 3, 5, 1, 2, 2, 6]
def baseStart_3877281 : Nat := 118140960795 + 3877281 * 2 ^ 59
def prefixEnd_3877281 : Nat := 4983230072969 + 3 ^ 40 * 3877281 * 2
def baseEnd_3877281 : Nat := 147474724855211100293053

theorem tailTrace_3877281 : CollatzResearch.WordTrace tailWord_3877281 prefixEnd_3877281 147474724855211100293053 := by
  unfold tailWord_3877281
  simp only [CollatzResearch.WordTrace]
  refine ⟨141416055866280598720519697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94277370577520399147013131 141416055866280598720519697)
  ·
    refine ⟨106062041899710449040389773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141416055866280598720519697 106062041899710449040389773)
    ·
      refine ⟨39773265712391418390146165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106062041899710449040389773 39773265712391418390146165)
      ·
        refine ⟨3728743660536695474076203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39773265712391418390146165 3728743660536695474076203)
        ·
          refine ⟨5593115490805043211114305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3728743660536695474076203 5593115490805043211114305)
          ·
            refine ⟨4194836618103782408335729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5593115490805043211114305 4194836618103782408335729)
            ·
              refine ⟨3146127463577836806251797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4194836618103782408335729 3146127463577836806251797)
              ·
                refine ⟨147474724855211100293053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3146127463577836806251797 147474724855211100293053)
                ·
                  rfl

theorem cell22_3877281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 6].length) (baseStart_3877281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877281 prefixEnd_3877281 := by exact prefixLift 3877281
  have htrace : WordTrace (prefixWord ++ tailWord_3877281) baseStart_3877281 baseEnd_3877281 := by
    simpa [prefixWord, tailWord_3877281, baseEnd_3877281] using wordTrace_append hprefix tailTrace_3877281
  have hstable : (prefixWord ++ tailWord_3877281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877281).length < 2 ^ (prefixWord ++ tailWord_3877281).sum := by decide
  have hdescent : baseEnd_3877281 < baseStart_3877281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877322 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_3877322 : Nat := 118140960795 + 3877322 * 2 ^ 59
def prefixEnd_3877322 : Nat := 4983230072969 + 3 ^ 40 * 3877322 * 2
def baseEnd_3877322 : Nat := 1327286558834789462362351

theorem tailTrace_3877322 : CollatzResearch.WordTrace tailWord_3877322 prefixEnd_3877322 1327286558834789462362351 := by
  unfold tailWord_3877322
  simp only [CollatzResearch.WordTrace]
  refine ⟨35354387814783015680690555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94278367506088041815174813 35354387814783015680690555)
  ·
    refine ⟨53031581722174523521035833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35354387814783015680690555 53031581722174523521035833)
    ·
      refine ⟨39773686291630892640776875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53031581722174523521035833 39773686291630892640776875)
      ·
        refine ⟨59660529437446338961165313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39773686291630892640776875 59660529437446338961165313)
        ·
          refine ⟨44745397078084754220873985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59660529437446338961165313 44745397078084754220873985)
          ·
            refine ⟨33559047808563565665655489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44745397078084754220873985 33559047808563565665655489)
            ·
              refine ⟨25169285856422674249241617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33559047808563565665655489 25169285856422674249241617)
              ·
                refine ⟨18876964392317005686931213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25169285856422674249241617 18876964392317005686931213)
                ·
                  refine ⟨7078861647118877132599205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18876964392317005686931213 7078861647118877132599205)
                  ·
                    refine ⟨1327286558834789462362351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7078861647118877132599205 1327286558834789462362351)
                    ·
                      rfl

theorem cell22_3877322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_3877322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3877322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3877322 prefixEnd_3877322 := by exact prefixLift 3877322
  have htrace : WordTrace (prefixWord ++ tailWord_3877322) baseStart_3877322 baseEnd_3877322 := by
    simpa [prefixWord, tailWord_3877322, baseEnd_3877322] using wordTrace_append hprefix tailTrace_3877322
  have hstable : (prefixWord ++ tailWord_3877322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877322).length < 2 ^ (prefixWord ++ tailWord_3877322).sum := by decide
  have hdescent : baseEnd_3877322 < baseStart_3877322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
