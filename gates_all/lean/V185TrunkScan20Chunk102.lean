import V185TrunkScan20Chunk101

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_620024 : List Nat := [2, 1, 2, 1, 1, 13]
def baseStart_620024 : Nat := 118140960795 + 620024 * 2 ^ 59
def prefixEnd_620024 : Nat := 4983230072969 + 3 ^ 40 * 620024 * 2
def baseEnd_620024 : Nat := 10481327714350202039459

theorem tailTrace_620024 : CollatzResearch.WordTrace tailWord_620024 prefixEnd_620024 10481327714350202039459 := by
  unfold tailWord_620024
  simp only [CollatzResearch.WordTrace]
  refine ⟨11307066552883207256921563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15076088737177609675895417 11307066552883207256921563)
  ·
    refine ⟨16960599829324810885382345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11307066552883207256921563 16960599829324810885382345)
    ·
      refine ⟨12720449871993608164036759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16960599829324810885382345 12720449871993608164036759)
      ·
        refine ⟨19080674807990412246055139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12720449871993608164036759 19080674807990412246055139)
        ·
          refine ⟨28621012211985618369082709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19080674807990412246055139 28621012211985618369082709)
          ·
            refine ⟨10481327714350202039459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 28621012211985618369082709 10481327714350202039459)
            ·
              rfl

theorem cell20_620024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 13].length) (baseStart_620024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620024 prefixEnd_620024 := by exact prefixLift 620024
  have htrace : WordTrace (prefixWord ++ tailWord_620024) baseStart_620024 baseEnd_620024 := by
    simpa [prefixWord, tailWord_620024, baseEnd_620024] using wordTrace_append hprefix tailTrace_620024
  have hstable : (prefixWord ++ tailWord_620024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620024).length < 2 ^ (prefixWord ++ tailWord_620024).sum := by decide
  have hdescent : baseEnd_620024 < baseStart_620024 := by decide
  rcases family_descends (prefixWord ++ tailWord_620024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620089 : List Nat := [1, 2, 1, 5, 1, 2, 2, 4, 2]
def baseStart_620089 : Nat := 118140960795 + 620089 * 2 ^ 59
def prefixEnd_620089 : Nat := 4983230072969 + 3 ^ 40 * 620089 * 2
def baseEnd_620089 : Nat := 283025516058604117898461

theorem tailTrace_620089 : CollatzResearch.WordTrace tailWord_620089 prefixEnd_620089 283025516058604117898461 := by
  unfold tailWord_620089
  simp only [CollatzResearch.WordTrace]
  refine ⟨22616503850530930614959321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15077669233687287076639547 22616503850530930614959321)
  ·
    refine ⟨16962377887898197961219491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22616503850530930614959321 16962377887898197961219491)
    ·
      refine ⟨25443566831847296941829237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16962377887898197961219491 25443566831847296941829237)
      ·
        refine ⟨2385334390485684088296491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25443566831847296941829237 2385334390485684088296491)
        ·
          refine ⟨3578001585728526132444737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385334390485684088296491 3578001585728526132444737)
          ·
            refine ⟨2683501189296394599333553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578001585728526132444737 2683501189296394599333553)
            ·
              refine ⟨2012625891972295949500165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683501189296394599333553 2012625891972295949500165)
              ·
                refine ⟨377367354744805490531281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2012625891972295949500165 377367354744805490531281)
                ·
                  refine ⟨283025516058604117898461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377367354744805490531281 283025516058604117898461)
                  ·
                    rfl

theorem cell20_620089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_620089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620089 prefixEnd_620089 := by exact prefixLift 620089
  have htrace : WordTrace (prefixWord ++ tailWord_620089) baseStart_620089 baseEnd_620089 := by
    simpa [prefixWord, tailWord_620089, baseEnd_620089] using wordTrace_append hprefix tailTrace_620089
  have hstable : (prefixWord ++ tailWord_620089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620089).length < 2 ^ (prefixWord ++ tailWord_620089).sum := by decide
  have hdescent : baseEnd_620089 < baseStart_620089 := by decide
  rcases family_descends (prefixWord ++ tailWord_620089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620144 : List Nat := [2, 1, 1, 1, 6, 2, 3, 2, 2]
def baseStart_620144 : Nat := 118140960795 + 620144 * 2 ^ 59
def prefixEnd_620144 : Nat := 4983230072969 + 3 ^ 40 * 620144 * 2
def baseEnd_620144 : Nat := 283050619557268371064903

theorem tailTrace_620144 : CollatzResearch.WordTrace tailWord_620144 prefixEnd_620144 283050619557268371064903 := by
  unfold tailWord_620144
  simp only [CollatzResearch.WordTrace]
  refine ⟨11309254932665837504105743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15079006576887783338807657 11309254932665837504105743)
  ·
    refine ⟨16963882398998756256158615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11309254932665837504105743 16963882398998756256158615)
    ·
      refine ⟨25445823598498134384237923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16963882398998756256158615 25445823598498134384237923)
      ·
        refine ⟨38168735397747201576356885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25445823598498134384237923 38168735397747201576356885)
        ·
          refine ⟨1789159471769400073891729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38168735397747201576356885 1789159471769400073891729)
          ·
            refine ⟨1341869603827050055418797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1789159471769400073891729 1341869603827050055418797)
            ·
              refine ⟨503201101435143770782049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1341869603827050055418797 503201101435143770782049)
              ·
                refine ⟨377400826076357828086537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503201101435143770782049 377400826076357828086537)
                ·
                  refine ⟨283050619557268371064903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377400826076357828086537 283050619557268371064903)
                  ·
                    rfl

theorem cell20_620144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_620144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620144 prefixEnd_620144 := by exact prefixLift 620144
  have htrace : WordTrace (prefixWord ++ tailWord_620144) baseStart_620144 baseEnd_620144 := by
    simpa [prefixWord, tailWord_620144, baseEnd_620144] using wordTrace_append hprefix tailTrace_620144
  have hstable : (prefixWord ++ tailWord_620144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620144).length < 2 ^ (prefixWord ++ tailWord_620144).sum := by decide
  have hdescent : baseEnd_620144 < baseStart_620144 := by decide
  rcases family_descends (prefixWord ++ tailWord_620144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620169 : List Nat := [1, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_620169 : Nat := 118140960795 + 620169 * 2 ^ 59
def prefixEnd_620169 : Nat := 4983230072969 + 3 ^ 40 * 620169 * 2
def baseEnd_620169 : Nat := 283062030238479395231467

theorem tailTrace_620169 : CollatzResearch.WordTrace tailWord_620169 prefixEnd_620169 283062030238479395231467 := by
  unfold tailWord_620169
  simp only [CollatzResearch.WordTrace]
  refine ⟨22619421690241104277871561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15079614460160736185247707 22619421690241104277871561)
  ·
    refine ⟨16964566267680828208403671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22619421690241104277871561 16964566267680828208403671)
    ·
      refine ⟨25446849401521242312605507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16964566267680828208403671 25446849401521242312605507)
      ·
        refine ⟨38170274102281863468908261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25446849401521242312605507 38170274102281863468908261)
        ·
          refine ⟨7156926394177849400420299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38170274102281863468908261 7156926394177849400420299)
          ·
            refine ⟨10735389591266774100630449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7156926394177849400420299 10735389591266774100630449)
            ·
              refine ⟨8051542193450080575472837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10735389591266774100630449 8051542193450080575472837)
              ·
                refine ⟨1509664161271890107901157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8051542193450080575472837 1509664161271890107901157)
                ·
                  refine ⟨283062030238479395231467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1509664161271890107901157 283062030238479395231467)
                  ·
                    rfl

theorem cell20_620169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_620169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620169 prefixEnd_620169 := by exact prefixLift 620169
  have htrace : WordTrace (prefixWord ++ tailWord_620169) baseStart_620169 baseEnd_620169 := by
    simpa [prefixWord, tailWord_620169, baseEnd_620169] using wordTrace_append hprefix tailTrace_620169
  have hstable : (prefixWord ++ tailWord_620169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620169).length < 2 ^ (prefixWord ++ tailWord_620169).sum := by decide
  have hdescent : baseEnd_620169 < baseStart_620169 := by decide
  rcases family_descends (prefixWord ++ tailWord_620169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620206 : List Nat := [4, 1, 4, 1, 3, 1, 1, 5]
def baseStart_620206 : Nat := 118140960795 + 620206 * 2 ^ 59
def prefixEnd_620206 : Nat := 4983230072969 + 3 ^ 40 * 620206 * 2
def baseEnd_620206 : Nat := 94359639348890570332661

theorem tailTrace_620206 : CollatzResearch.WordTrace tailWord_620206 prefixEnd_620206 94359639348890570332661 := by
  unfold tailWord_620206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827596398888382449621059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15080514127404706397978981 2827596398888382449621059)
  ·
    refine ⟨4241394598332573674431589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827596398888382449621059 4241394598332573674431589)
    ·
      refine ⟨795261487187357563955923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4241394598332573674431589 795261487187357563955923)
      ·
        refine ⟨1192892230781036345933885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795261487187357563955923 1192892230781036345933885)
        ·
          refine ⟨447334586542888629725207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1192892230781036345933885 447334586542888629725207)
          ·
            refine ⟨671001879814332944587811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447334586542888629725207 671001879814332944587811)
            ·
              refine ⟨1006502819721499416881717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671001879814332944587811 1006502819721499416881717)
              ·
                refine ⟨94359639348890570332661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1006502819721499416881717 94359639348890570332661)
                ·
                  rfl

theorem cell20_620206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_620206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620206 prefixEnd_620206 := by exact prefixLift 620206
  have htrace : WordTrace (prefixWord ++ tailWord_620206) baseStart_620206 baseEnd_620206 := by
    simpa [prefixWord, tailWord_620206, baseEnd_620206] using wordTrace_append hprefix tailTrace_620206
  have hstable : (prefixWord ++ tailWord_620206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620206).length < 2 ^ (prefixWord ++ tailWord_620206).sum := by decide
  have hdescent : baseEnd_620206 < baseStart_620206 := by decide
  rcases family_descends (prefixWord ++ tailWord_620206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620207 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_620207 : Nat := 118140960795 + 620207 * 2 ^ 59
def prefixEnd_620207 : Nat := 4983230072969 + 3 ^ 40 * 620207 * 2
def baseEnd_620207 : Nat := 283079374473920151964645

theorem tailTrace_620207 : CollatzResearch.WordTrace tailWord_620207 prefixEnd_620207 283079374473920151964645 := by
  unfold tailWord_620207
  simp only [CollatzResearch.WordTrace]
  refine ⟨22620807664103436767754875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15080538442735624511836583 22620807664103436767754875)
  ·
    refine ⟨33931211496155155151632313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22620807664103436767754875 33931211496155155151632313)
    ·
      refine ⟨25448408622116366363724235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33931211496155155151632313 25448408622116366363724235)
      ·
        refine ⟨38172612933174549545586353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25448408622116366363724235 38172612933174549545586353)
        ·
          refine ⟨28629459699880912159189765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38172612933174549545586353 28629459699880912159189765)
          ·
            refine ⟨5368023693727671029848081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28629459699880912159189765 5368023693727671029848081)
            ·
              refine ⟨4026017770295753272386061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5368023693727671029848081 4026017770295753272386061)
              ·
                refine ⟨1509756663860907477144773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4026017770295753272386061 1509756663860907477144773)
                ·
                  refine ⟨283079374473920151964645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1509756663860907477144773 283079374473920151964645)
                  ·
                    rfl

theorem cell20_620207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_620207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620207 prefixEnd_620207 := by exact prefixLift 620207
  have htrace : WordTrace (prefixWord ++ tailWord_620207) baseStart_620207 baseEnd_620207 := by
    simpa [prefixWord, tailWord_620207, baseEnd_620207] using wordTrace_append hprefix tailTrace_620207
  have hstable : (prefixWord ++ tailWord_620207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620207).length < 2 ^ (prefixWord ++ tailWord_620207).sum := by decide
  have hdescent : baseEnd_620207 < baseStart_620207 := by decide
  rcases family_descends (prefixWord ++ tailWord_620207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620231 : List Nat := [1, 1, 4, 1, 1, 1, 7, 4]
def baseStart_620231 : Nat := 118140960795 + 620231 * 2 ^ 59
def prefixEnd_620231 : Nat := 4983230072969 + 3 ^ 40 * 620231 * 2
def baseEnd_620231 : Nat := 94363442909294245054849

theorem tailTrace_620231 : CollatzResearch.WordTrace tailWord_620231 prefixEnd_620231 94363442909294245054849 := by
  unfold tailWord_620231
  simp only [CollatzResearch.WordTrace]
  refine ⟨22621683016016488866628547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15081122010677659244419031 22621683016016488866628547)
  ·
    refine ⟨33932524524024733299942821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22621683016016488866628547 33932524524024733299942821)
    ·
      refine ⟨6362348348254637493739279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33932524524024733299942821 6362348348254637493739279)
      ·
        refine ⟨9543522522381956240608919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6362348348254637493739279 9543522522381956240608919)
        ·
          refine ⟨14315283783572934360913379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9543522522381956240608919 14315283783572934360913379)
          ·
            refine ⟨21472925675359401541370069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14315283783572934360913379 21472925675359401541370069)
            ·
              refine ⟨503271695516235973625861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21472925675359401541370069 503271695516235973625861)
              ·
                refine ⟨94363442909294245054849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503271695516235973625861 94363442909294245054849)
                ·
                  rfl

theorem cell20_620231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 4].length) (baseStart_620231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620231 prefixEnd_620231 := by exact prefixLift 620231
  have htrace : WordTrace (prefixWord ++ tailWord_620231) baseStart_620231 baseEnd_620231 := by
    simpa [prefixWord, tailWord_620231, baseEnd_620231] using wordTrace_append hprefix tailTrace_620231
  have hstable : (prefixWord ++ tailWord_620231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620231).length < 2 ^ (prefixWord ++ tailWord_620231).sum := by decide
  have hdescent : baseEnd_620231 < baseStart_620231 := by decide
  rcases family_descends (prefixWord ++ tailWord_620231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620237 : List Nat := [1, 6, 2, 1, 1, 2, 2, 3, 2]
def baseStart_620237 : Nat := 118140960795 + 620237 * 2 ^ 59
def prefixEnd_620237 : Nat := 4983230072969 + 3 ^ 40 * 620237 * 2
def baseEnd_620237 : Nat := 283093067291373380964523

theorem tailTrace_620237 : CollatzResearch.WordTrace tailWord_620237 prefixEnd_620237 283093067291373380964523 := by
  unfold tailWord_620237
  simp only [CollatzResearch.WordTrace]
  refine ⟨22621901853994751891346965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15081267902663167927564643 22621901853994751891346965)
  ·
    refine ⟨1060401649406003994906889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22621901853994751891346965 1060401649406003994906889)
    ·
      refine ⟨795301237054502996180167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1060401649406003994906889 795301237054502996180167)
      ·
        refine ⟨1192951855581754494270251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795301237054502996180167 1192951855581754494270251)
        ·
          refine ⟨1789427783372631741405377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192951855581754494270251 1789427783372631741405377)
          ·
            refine ⟨1342070837529473806054033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1789427783372631741405377 1342070837529473806054033)
            ·
              refine ⟨1006553128147105354540525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342070837529473806054033 1006553128147105354540525)
              ·
                refine ⟨377457423055164507952697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006553128147105354540525 377457423055164507952697)
                ·
                  refine ⟨283093067291373380964523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377457423055164507952697 283093067291373380964523)
                  ·
                    rfl

theorem cell20_620237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_620237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620237 prefixEnd_620237 := by exact prefixLift 620237
  have htrace : WordTrace (prefixWord ++ tailWord_620237) baseStart_620237 baseEnd_620237 := by
    simpa [prefixWord, tailWord_620237, baseEnd_620237] using wordTrace_append hprefix tailTrace_620237
  have hstable : (prefixWord ++ tailWord_620237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620237).length < 2 ^ (prefixWord ++ tailWord_620237).sum := by decide
  have hdescent : baseEnd_620237 < baseStart_620237 := by decide
  rcases family_descends (prefixWord ++ tailWord_620237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620238 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_620238 : Nat := 118140960795 + 620238 * 2 ^ 59
def prefixEnd_620238 : Nat := 4983230072969 + 3 ^ 40 * 620238 * 2
def baseEnd_620238 : Nat := 283093523718621821931185

theorem tailTrace_620238 : CollatzResearch.WordTrace tailWord_620238 prefixEnd_620238 283093523718621821931185 := by
  unfold tailWord_620238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827742290873891132766671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15081292217994086041422245 2827742290873891132766671)
  ·
    refine ⟨4241613436310836699150007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827742290873891132766671 4241613436310836699150007)
    ·
      refine ⟨6362420154466255048725011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4241613436310836699150007 6362420154466255048725011)
      ·
        refine ⟨9543630231699382573087517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6362420154466255048725011 9543630231699382573087517)
        ·
          refine ⟨3578861336887268464907819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9543630231699382573087517 3578861336887268464907819)
          ·
            refine ⟨5368292005330902697361729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3578861336887268464907819 5368292005330902697361729)
            ·
              refine ⟨4026219003998177023021297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5368292005330902697361729 4026219003998177023021297)
              ·
                refine ⟨3019664252998632767265973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4026219003998177023021297 3019664252998632767265973)
                ·
                  refine ⟨283093523718621821931185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3019664252998632767265973 283093523718621821931185)
                  ·
                    rfl

theorem cell20_620238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_620238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620238 prefixEnd_620238 := by exact prefixLift 620238
  have htrace : WordTrace (prefixWord ++ tailWord_620238) baseStart_620238 baseEnd_620238 := by
    simpa [prefixWord, tailWord_620238, baseEnd_620238] using wordTrace_append hprefix tailTrace_620238
  have hstable : (prefixWord ++ tailWord_620238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620238).length < 2 ^ (prefixWord ++ tailWord_620238).sum := by decide
  have hdescent : baseEnd_620238 < baseStart_620238 := by decide
  rcases family_descends (prefixWord ++ tailWord_620238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620241 : List Nat := [1, 2, 2, 1, 2, 5, 2, 3, 2]
def baseStart_620241 : Nat := 118140960795 + 620241 * 2 ^ 59
def prefixEnd_620241 : Nat := 4983230072969 + 3 ^ 40 * 620241 * 2
def baseEnd_620241 : Nat := 283094893000367144831173

theorem tailTrace_620241 : CollatzResearch.WordTrace tailWord_620241 prefixEnd_620241 283094893000367144831173 := by
  unfold tailWord_620241
  simp only [CollatzResearch.WordTrace]
  refine ⟨22622047745980260574492577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15081365163986840382995051 22622047745980260574492577)
  ·
    refine ⟨16966535809485195430869433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22622047745980260574492577 16966535809485195430869433)
    ·
      refine ⟨12724901857113896573152075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16966535809485195430869433 12724901857113896573152075)
      ·
        refine ⟨19087352785670844859728113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12724901857113896573152075 19087352785670844859728113)
        ·
          refine ⟨14315514589253133644796085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19087352785670844859728113 14315514589253133644796085)
          ·
            refine ⟨1342079492742481279199633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14315514589253133644796085 1342079492742481279199633)
            ·
              refine ⟨1006559619556860959399725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342079492742481279199633 1006559619556860959399725)
              ·
                refine ⟨377459857333822859774897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006559619556860959399725 377459857333822859774897)
                ·
                  refine ⟨283094893000367144831173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377459857333822859774897 283094893000367144831173)
                  ·
                    rfl

theorem cell20_620241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_620241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620241 prefixEnd_620241 := by exact prefixLift 620241
  have htrace : WordTrace (prefixWord ++ tailWord_620241) baseStart_620241 baseEnd_620241 := by
    simpa [prefixWord, tailWord_620241, baseEnd_620241] using wordTrace_append hprefix tailTrace_620241
  have hstable : (prefixWord ++ tailWord_620241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620241).length < 2 ^ (prefixWord ++ tailWord_620241).sum := by decide
  have hdescent : baseEnd_620241 < baseStart_620241 := by decide
  rcases family_descends (prefixWord ++ tailWord_620241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620286 : List Nat := [4, 2, 2, 1, 3, 1, 1, 6]
def baseStart_620286 : Nat := 118140960795 + 620286 * 2 ^ 59
def prefixEnd_620286 : Nat := 4983230072969 + 3 ^ 40 * 620286 * 2
def baseEnd_620286 : Nat := 94371810742182329443663

theorem tailTrace_620286 : CollatzResearch.WordTrace tailWord_620286 prefixEnd_620286 94371810742182329443663 := by
  unfold tailWord_620286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827961128852154157485089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15082459353878155506587141 2827961128852154157485089)
  ·
    refine ⟨2120970846639115618113817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2827961128852154157485089 2120970846639115618113817)
    ·
      refine ⟨1590728134979336713585363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2120970846639115618113817 1590728134979336713585363)
      ·
        refine ⟨2386092202469005070378045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590728134979336713585363 2386092202469005070378045)
        ·
          refine ⟨894784575925876901391767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2386092202469005070378045 894784575925876901391767)
          ·
            refine ⟨1342176863888815352087651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894784575925876901391767 1342176863888815352087651)
            ·
              refine ⟨2013265295833223028131477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342176863888815352087651 2013265295833223028131477)
              ·
                refine ⟨94371810742182329443663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2013265295833223028131477 94371810742182329443663)
                ·
                  rfl

theorem cell20_620286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_620286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620286 prefixEnd_620286 := by exact prefixLift 620286
  have htrace : WordTrace (prefixWord ++ tailWord_620286) baseStart_620286 baseEnd_620286 := by
    simpa [prefixWord, tailWord_620286, baseEnd_620286] using wordTrace_append hprefix tailTrace_620286
  have hstable : (prefixWord ++ tailWord_620286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620286).length < 2 ^ (prefixWord ++ tailWord_620286).sum := by decide
  have hdescent : baseEnd_620286 < baseStart_620286 := by decide
  rcases family_descends (prefixWord ++ tailWord_620286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620314 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_620314 : Nat := 118140960795 + 620314 * 2 ^ 59
def prefixEnd_620314 : Nat := 4983230072969 + 3 ^ 40 * 620314 * 2
def baseEnd_620314 : Nat := 283128212189503335397541

theorem tailTrace_620314 : CollatzResearch.WordTrace tailWord_620314 prefixEnd_620314 283128212189503335397541 := by
  unfold tailWord_620314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5656177568678948510474999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15083140183143862694599997 5656177568678948510474999)
  ·
    refine ⟨8484266353018422765712499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5656177568678948510474999 8484266353018422765712499)
    ·
      refine ⟨12726399529527634148568749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8484266353018422765712499 12726399529527634148568749)
      ·
        refine ⟨4772399823572862805713281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12726399529527634148568749 4772399823572862805713281)
        ·
          refine ⟨3579299867679647104284961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4772399823572862805713281 3579299867679647104284961)
          ·
            refine ⟨2684474900759735328213721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3579299867679647104284961 2684474900759735328213721)
            ·
              refine ⟨2013356175569801496160291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2684474900759735328213721 2013356175569801496160291)
              ·
                refine ⟨3020034263354702244240437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013356175569801496160291 3020034263354702244240437)
                ·
                  refine ⟨283128212189503335397541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3020034263354702244240437 283128212189503335397541)
                  ·
                    rfl

theorem cell20_620314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_620314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620314 prefixEnd_620314 := by exact prefixLift 620314
  have htrace : WordTrace (prefixWord ++ tailWord_620314) baseStart_620314 baseEnd_620314 := by
    simpa [prefixWord, tailWord_620314, baseEnd_620314] using wordTrace_append hprefix tailTrace_620314
  have hstable : (prefixWord ++ tailWord_620314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620314).length < 2 ^ (prefixWord ++ tailWord_620314).sum := by decide
  have hdescent : baseEnd_620314 < baseStart_620314 := by decide
  rcases family_descends (prefixWord ++ tailWord_620314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620369 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 3]
def baseStart_620369 : Nat := 118140960795 + 620369 * 2 ^ 59
def prefixEnd_620369 : Nat := 4983230072969 + 3 ^ 40 * 620369 * 2
def baseEnd_620369 : Nat := 283153315688167588563983

theorem tailTrace_620369 : CollatzResearch.WordTrace tailWord_620369 prefixEnd_620369 283153315688167588563983 := by
  unfold tailWord_620369
  simp only [CollatzResearch.WordTrace]
  refine ⟨22626716289516538435152161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15084477526344358956768107 22626716289516538435152161)
  ·
    refine ⟨16970037217137403826364121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22626716289516538435152161 16970037217137403826364121)
    ·
      refine ⟨12727527912853052869773091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16970037217137403826364121 12727527912853052869773091)
      ·
        refine ⟨19091291869279579304659637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12727527912853052869773091 19091291869279579304659637)
        ·
          refine ⟨1789808612744960559811841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19091291869279579304659637 1789808612744960559811841)
          ·
            refine ⟨1342356459558720419858881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1789808612744960559811841 1342356459558720419858881)
            ·
              refine ⟨1006767344669040314894161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342356459558720419858881 1006767344669040314894161)
              ·
                refine ⟨755075508501780236170621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006767344669040314894161 755075508501780236170621)
                ·
                  refine ⟨283153315688167588563983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755075508501780236170621 283153315688167588563983)
                  ·
                    rfl

theorem cell20_620369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_620369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620369 prefixEnd_620369 := by exact prefixLift 620369
  have htrace : WordTrace (prefixWord ++ tailWord_620369) baseStart_620369 baseEnd_620369 := by
    simpa [prefixWord, tailWord_620369, baseEnd_620369] using wordTrace_append hprefix tailTrace_620369
  have hstable : (prefixWord ++ tailWord_620369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620369).length < 2 ^ (prefixWord ++ tailWord_620369).sum := by decide
  have hdescent : baseEnd_620369 < baseStart_620369 := by decide
  rcases family_descends (prefixWord ++ tailWord_620369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620372 : List Nat := [2, 4, 1, 1, 3, 1, 4, 2, 2]
def baseStart_620372 : Nat := 118140960795 + 620372 * 2 ^ 59
def prefixEnd_620372 : Nat := 4983230072969 + 3 ^ 40 * 620372 * 2
def baseEnd_620372 : Nat := 283154684969912911463971

theorem tailTrace_620372 : CollatzResearch.WordTrace tailWord_620372 prefixEnd_620372 283154684969912911463971 := by
  unfold tailWord_620372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11313412854252834973755685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15084550472337113298340913 11313412854252834973755685)
  ·
    refine ⟨2121264910172406557579191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11313412854252834973755685 2121264910172406557579191)
    ·
      refine ⟨3181897365258609836368787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2121264910172406557579191 3181897365258609836368787)
      ·
        refine ⟨4772846047887914754553181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3181897365258609836368787 4772846047887914754553181)
        ·
          refine ⟨1789817267957968032957443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4772846047887914754553181 1789817267957968032957443)
          ·
            refine ⟨2684725901936952049436165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789817267957968032957443 2684725901936952049436165)
            ·
              refine ⟨503386106613178509269281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2684725901936952049436165 503386106613178509269281)
              ·
                refine ⟨377539579959883881951961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503386106613178509269281 377539579959883881951961)
                ·
                  refine ⟨283154684969912911463971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377539579959883881951961 283154684969912911463971)
                  ·
                    rfl

theorem cell20_620372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_620372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620372 prefixEnd_620372 := by exact prefixLift 620372
  have htrace : WordTrace (prefixWord ++ tailWord_620372) baseStart_620372 baseEnd_620372 := by
    simpa [prefixWord, tailWord_620372, baseEnd_620372] using wordTrace_append hprefix tailTrace_620372
  have hstable : (prefixWord ++ tailWord_620372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620372).length < 2 ^ (prefixWord ++ tailWord_620372).sum := by decide
  have hdescent : baseEnd_620372 < baseStart_620372 := by decide
  rcases family_descends (prefixWord ++ tailWord_620372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620383 : List Nat := [1, 1, 2, 3, 1, 6, 1, 5]
def baseStart_620383 : Nat := 118140960795 + 620383 * 2 ^ 59
def prefixEnd_620383 : Nat := 4983230072969 + 3 ^ 40 * 620383 * 2
def baseEnd_620383 : Nat := 94386568556548587365753

theorem tailTrace_620383 : CollatzResearch.WordTrace tailWord_620383 prefixEnd_620383 94386568556548587365753 := by
  unfold tailWord_620383
  simp only [CollatzResearch.WordTrace]
  refine ⟨22627226911465818826161803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15084817940977212550774535 22627226911465818826161803)
  ·
    refine ⟨33940840367198728239242705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22627226911465818826161803 33940840367198728239242705)
    ·
      refine ⟨25455630275399046179432029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33940840367198728239242705 25455630275399046179432029)
      ·
        refine ⟨9545861353274642317287011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25455630275399046179432029 9545861353274642317287011)
        ·
          refine ⟨14318792029911963475930517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9545861353274642317287011 14318792029911963475930517)
          ·
            refine ⟨671193376402123287934243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14318792029911963475930517 671193376402123287934243)
            ·
              refine ⟨1006790064603184931901365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671193376402123287934243 1006790064603184931901365)
              ·
                refine ⟨94386568556548587365753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1006790064603184931901365 94386568556548587365753)
                ·
                  rfl

theorem cell20_620383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 5].length) (baseStart_620383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620383 prefixEnd_620383 := by exact prefixLift 620383
  have htrace : WordTrace (prefixWord ++ tailWord_620383) baseStart_620383 baseEnd_620383 := by
    simpa [prefixWord, tailWord_620383, baseEnd_620383] using wordTrace_append hprefix tailTrace_620383
  have hstable : (prefixWord ++ tailWord_620383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620383).length < 2 ^ (prefixWord ++ tailWord_620383).sum := by decide
  have hdescent : baseEnd_620383 < baseStart_620383 := by decide
  rcases family_descends (prefixWord ++ tailWord_620383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620397 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_620397 : Nat := 118140960795 + 620397 * 2 ^ 59
def prefixEnd_620397 : Nat := 4983230072969 + 3 ^ 40 * 620397 * 2
def baseEnd_620397 : Nat := 283166095651123935630535

theorem tailTrace_620397 : CollatzResearch.WordTrace tailWord_620397 prefixEnd_620397 283166095651123935630535 := by
  unfold tailWord_620397
  simp only [CollatzResearch.WordTrace]
  refine ⟨22627737533415099217171445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15085158355610066144780963 22627737533415099217171445)
  ·
    refine ⟨2121350393757665551609823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22627737533415099217171445 2121350393757665551609823)
    ·
      refine ⟨3182025590636498327414735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2121350393757665551609823 3182025590636498327414735)
      ·
        refine ⟨4773038385954747491122103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3182025590636498327414735 4773038385954747491122103)
        ·
          refine ⟨7159557578932121236683155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4773038385954747491122103 7159557578932121236683155)
          ·
            refine ⟨10739336368398181855024733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7159557578932121236683155 10739336368398181855024733)
            ·
              refine ⟨4027251138149318195634275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10739336368398181855024733 4027251138149318195634275)
              ·
                refine ⟨6040876707223977293451413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4027251138149318195634275 6040876707223977293451413)
                ·
                  refine ⟨283166095651123935630535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6040876707223977293451413 283166095651123935630535)
                  ·
                    rfl

theorem cell20_620397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_620397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620397 prefixEnd_620397 := by exact prefixLift 620397
  have htrace : WordTrace (prefixWord ++ tailWord_620397) baseStart_620397 baseEnd_620397 := by
    simpa [prefixWord, tailWord_620397, baseEnd_620397] using wordTrace_append hprefix tailTrace_620397
  have hstable : (prefixWord ++ tailWord_620397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620397).length < 2 ^ (prefixWord ++ tailWord_620397).sum := by decide
  have hdescent : baseEnd_620397 < baseStart_620397 := by decide
  rcases family_descends (prefixWord ++ tailWord_620397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620411 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_620411 : Nat := 118140960795 + 620411 * 2 ^ 59
def prefixEnd_620411 : Nat := 4983230072969 + 3 ^ 40 * 620411 * 2
def baseEnd_620411 : Nat := 283172485632602109163811

theorem tailTrace_620411 : CollatzResearch.WordTrace tailWord_620411 prefixEnd_620411 283172485632602109163811 := by
  unfold tailWord_620411
  simp only [CollatzResearch.WordTrace]
  refine ⟨22628248155364379608181087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15085498770242919738787391 22628248155364379608181087)
  ·
    refine ⟨33942372233046569412271631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22628248155364379608181087 33942372233046569412271631)
    ·
      refine ⟨50913558349569854118407447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33942372233046569412271631 50913558349569854118407447)
      ·
        refine ⟨76370337524354781177611171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50913558349569854118407447 76370337524354781177611171)
        ·
          refine ⟨114555506286532171766416757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76370337524354781177611171 114555506286532171766416757)
          ·
            refine ⟨10739578714362391103101571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114555506286532171766416757 10739578714362391103101571)
            ·
              refine ⟨16109368071543586654652357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10739578714362391103101571 16109368071543586654652357)
              ·
                refine ⟨3020506513414422497747317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16109368071543586654652357 3020506513414422497747317)
                ·
                  refine ⟨283172485632602109163811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3020506513414422497747317 283172485632602109163811)
                  ·
                    rfl

theorem cell20_620411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_620411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620411 prefixEnd_620411 := by exact prefixLift 620411
  have htrace : WordTrace (prefixWord ++ tailWord_620411) baseStart_620411 baseEnd_620411 := by
    simpa [prefixWord, tailWord_620411, baseEnd_620411] using wordTrace_append hprefix tailTrace_620411
  have hstable : (prefixWord ++ tailWord_620411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620411).length < 2 ^ (prefixWord ++ tailWord_620411).sum := by decide
  have hdescent : baseEnd_620411 < baseStart_620411 := by decide
  rcases family_descends (prefixWord ++ tailWord_620411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620424 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 3]
def baseStart_620424 : Nat := 118140960795 + 620424 * 2 ^ 59
def prefixEnd_620424 : Nat := 4983230072969 + 3 ^ 40 * 620424 * 2
def baseEnd_620424 : Nat := 283178419186831841730425

theorem tailTrace_620424 : CollatzResearch.WordTrace tailWord_620424 prefixEnd_620424 283178419186831841730425 := by
  unfold tailWord_620424
  simp only [CollatzResearch.WordTrace]
  refine ⟨11314361152158641414202163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15085814869544855218936217 11314361152158641414202163)
  ·
    refine ⟨16971541728237962121303245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11314361152158641414202163 16971541728237962121303245)
    ·
      refine ⟨6364328148089235795488717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16971541728237962121303245 6364328148089235795488717)
      ·
        refine ⟨2386623055533463423308269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6364328148089235795488717 2386623055533463423308269)
        ·
          refine ⟨894983645825048783740601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2386623055533463423308269 894983645825048783740601)
          ·
            refine ⟨671237734368786587805451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 894983645825048783740601 671237734368786587805451)
            ·
              refine ⟨1006856601553179881708177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671237734368786587805451 1006856601553179881708177)
              ·
                refine ⟨755142451164884911281133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006856601553179881708177 755142451164884911281133)
                ·
                  refine ⟨283178419186831841730425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755142451164884911281133 283178419186831841730425)
                  ·
                    rfl

theorem cell20_620424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_620424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620424 prefixEnd_620424 := by exact prefixLift 620424
  have htrace : WordTrace (prefixWord ++ tailWord_620424) baseStart_620424 baseEnd_620424 := by
    simpa [prefixWord, tailWord_620424, baseEnd_620424] using wordTrace_append hprefix tailTrace_620424
  have hstable : (prefixWord ++ tailWord_620424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620424).length < 2 ^ (prefixWord ++ tailWord_620424).sum := by decide
  have hdescent : baseEnd_620424 < baseStart_620424 := by decide
  rcases family_descends (prefixWord ++ tailWord_620424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620469 : List Nat := [1, 3, 3, 2, 1, 2, 3, 3, 2]
def baseStart_620469 : Nat := 118140960795 + 620469 * 2 ^ 59
def prefixEnd_620469 : Nat := 4983230072969 + 3 ^ 40 * 620469 * 2
def baseEnd_620469 : Nat := 283198958413011685230241

theorem tailTrace_620469 : CollatzResearch.WordTrace tailWord_620469 prefixEnd_620469 283198958413011685230241 := by
  unfold tailWord_620469
  simp only [CollatzResearch.WordTrace]
  refine ⟨22630363589154255513792461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15086909059436170342528307 22630363589154255513792461)
  ·
    refine ⟨8486386345932845817672173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22630363589154255513792461 8486386345932845817672173)
    ·
      refine ⟨3182394879724817181627065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8486386345932845817672173 3182394879724817181627065)
      ·
        refine ⟨2386796159793612886220299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3182394879724817181627065 2386796159793612886220299)
        ·
          refine ⟨3580194239690419329330449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386796159793612886220299 3580194239690419329330449)
          ·
            refine ⟨2685145679767814496997837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3580194239690419329330449 2685145679767814496997837)
            ·
              refine ⟨1006929629912930436374189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2685145679767814496997837 1006929629912930436374189)
              ·
                refine ⟨377598611217348913640321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006929629912930436374189 377598611217348913640321)
                ·
                  refine ⟨283198958413011685230241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377598611217348913640321 283198958413011685230241)
                  ·
                    rfl

theorem cell20_620469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_620469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620469 prefixEnd_620469 := by exact prefixLift 620469
  have htrace : WordTrace (prefixWord ++ tailWord_620469) baseStart_620469 baseEnd_620469 := by
    simpa [prefixWord, tailWord_620469, baseEnd_620469] using wordTrace_append hprefix tailTrace_620469
  have hstable : (prefixWord ++ tailWord_620469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620469).length < 2 ^ (prefixWord ++ tailWord_620469).sum := by decide
  have hdescent : baseEnd_620469 < baseStart_620469 := by decide
  rcases family_descends (prefixWord ++ tailWord_620469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620476 : List Nat := [2, 2, 2, 5, 1, 2, 6]
def baseStart_620476 : Nat := 118140960795 + 620476 * 2 ^ 59
def prefixEnd_620476 : Nat := 4983230072969 + 3 ^ 40 * 620476 * 2
def baseEnd_620476 : Nat := 31466905933750085777431

theorem tailTrace_620476 : CollatzResearch.WordTrace tailWord_620476 prefixEnd_620476 31466905933750085777431 := by
  unfold tailWord_620476
  simp only [CollatzResearch.WordTrace]
  refine ⟨11315309450064447854648641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15087079266752597139531521 11315309450064447854648641)
  ·
    refine ⟨8486482087548335890986481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11315309450064447854648641 8486482087548335890986481)
    ·
      refine ⟨6364861565661251918239861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8486482087548335890986481 6364861565661251918239861)
      ·
        refine ⟨596705771780742367334987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6364861565661251918239861 596705771780742367334987)
        ·
          refine ⟨895058657671113551002481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596705771780742367334987 895058657671113551002481)
          ·
            refine ⟨671293993253335163251861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895058657671113551002481 671293993253335163251861)
            ·
              refine ⟨31466905933750085777431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 671293993253335163251861 31466905933750085777431)
              ·
                rfl

theorem cell20_620476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 6].length) (baseStart_620476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620476 prefixEnd_620476 := by exact prefixLift 620476
  have htrace : WordTrace (prefixWord ++ tailWord_620476) baseStart_620476 baseEnd_620476 := by
    simpa [prefixWord, tailWord_620476, baseEnd_620476] using wordTrace_append hprefix tailTrace_620476
  have hstable : (prefixWord ++ tailWord_620476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620476).length < 2 ^ (prefixWord ++ tailWord_620476).sum := by decide
  have hdescent : baseEnd_620476 < baseStart_620476 := by decide
  rcases family_descends (prefixWord ++ tailWord_620476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620490 : List Nat := [3, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_620490 : Nat := 118140960795 + 620490 * 2 ^ 59
def prefixEnd_620490 : Nat := 4983230072969 + 3 ^ 40 * 620490 * 2
def baseEnd_620490 : Nat := 283208543385228945530155

theorem tailTrace_620490 : CollatzResearch.WordTrace tailWord_620490 prefixEnd_620490 283208543385228945530155 := by
  unfold tailWord_620490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657782380519544025076731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15087419681385450733537949 5657782380519544025076731)
  ·
    refine ⟨8486673570779316037615097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5657782380519544025076731 8486673570779316037615097)
    ·
      refine ⟨6365005178084487028211323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8486673570779316037615097 6365005178084487028211323)
      ·
        refine ⟨9547507767126730542316985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6365005178084487028211323 9547507767126730542316985)
        ·
          refine ⟨7160630825345047906737739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9547507767126730542316985 7160630825345047906737739)
          ·
            refine ⟨10740946238017571860106609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7160630825345047906737739 10740946238017571860106609)
            ·
              refine ⟨8055709678513178895079957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10740946238017571860106609 8055709678513178895079957)
              ·
                refine ⟨377611391180305260706873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8055709678513178895079957 377611391180305260706873)
                ·
                  refine ⟨283208543385228945530155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377611391180305260706873 283208543385228945530155)
                  ·
                    rfl

theorem cell20_620490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_620490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620490 prefixEnd_620490 := by exact prefixLift 620490
  have htrace : WordTrace (prefixWord ++ tailWord_620490) baseStart_620490 baseEnd_620490 := by
    simpa [prefixWord, tailWord_620490, baseEnd_620490] using wordTrace_append hprefix tailTrace_620490
  have hstable : (prefixWord ++ tailWord_620490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620490).length < 2 ^ (prefixWord ++ tailWord_620490).sum := by decide
  have hdescent : baseEnd_620490 < baseStart_620490 := by decide
  rcases family_descends (prefixWord ++ tailWord_620490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620504 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_620504 : Nat := 118140960795 + 620504 * 2 ^ 59
def prefixEnd_620504 : Nat := 4983230072969 + 3 ^ 40 * 620504 * 2
def baseEnd_620504 : Nat := 283214933366707119063431

theorem tailTrace_620504 : CollatzResearch.WordTrace tailWord_620504 prefixEnd_620504 283214933366707119063431 := by
  unfold tailWord_620504
  simp only [CollatzResearch.WordTrace]
  refine ⟨11315820072013728245658283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15087760096018304327544377 11315820072013728245658283)
  ·
    refine ⟨16973730108020592368487425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11315820072013728245658283 16973730108020592368487425)
    ·
      refine ⟨12730297581015444276365569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16973730108020592368487425 12730297581015444276365569)
      ·
        refine ⟨9547723185761583207274177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12730297581015444276365569 9547723185761583207274177)
        ·
          refine ⟨7160792389321187405455633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9547723185761583207274177 7160792389321187405455633)
          ·
            refine ⟨5370594291990890554091725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7160792389321187405455633 5370594291990890554091725)
            ·
              refine ⟨2013972859496583957784397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5370594291990890554091725 2013972859496583957784397)
              ·
                refine ⟨755239822311218984169149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2013972859496583957784397 755239822311218984169149)
                ·
                  refine ⟨283214933366707119063431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755239822311218984169149 283214933366707119063431)
                  ·
                    rfl

theorem cell20_620504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_620504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620504 prefixEnd_620504 := by exact prefixLift 620504
  have htrace : WordTrace (prefixWord ++ tailWord_620504) baseStart_620504 baseEnd_620504 := by
    simpa [prefixWord, tailWord_620504, baseEnd_620504] using wordTrace_append hprefix tailTrace_620504
  have hstable : (prefixWord ++ tailWord_620504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620504).length < 2 ^ (prefixWord ++ tailWord_620504).sum := by decide
  have hdescent : baseEnd_620504 < baseStart_620504 := by decide
  rcases family_descends (prefixWord ++ tailWord_620504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620594 : List Nat := [3, 2, 1, 1, 2, 4, 7]
def baseStart_620594 : Nat := 118140960795 + 620594 * 2 ^ 59
def prefixEnd_620594 : Nat := 4983230072969 + 3 ^ 40 * 620594 * 2
def baseEnd_620594 : Nat := 31472890202118534007007

theorem tailTrace_620594 : CollatzResearch.WordTrace tailWord_620594 prefixEnd_620594 31472890202118534007007 := by
  unfold tailWord_620594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5658730678425350465523209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15089948475800934574728557 5658730678425350465523209)
  ·
    refine ⟨4244048008819012849142407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5658730678425350465523209 4244048008819012849142407)
    ·
      refine ⟨6366072013228519273713611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4244048008819012849142407 6366072013228519273713611)
      ·
        refine ⟨9549108019842778910570417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6366072013228519273713611 9549108019842778910570417)
        ·
          refine ⟨7161831014882084182927813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9549108019842778910570417 7161831014882084182927813)
          ·
            refine ⟨1342843315290390784298965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7161831014882084182927813 1342843315290390784298965)
            ·
              refine ⟨31472890202118534007007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1342843315290390784298965 31472890202118534007007)
              ·
                rfl

theorem cell20_620594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 7].length) (baseStart_620594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620594 prefixEnd_620594 := by exact prefixLift 620594
  have htrace : WordTrace (prefixWord ++ tailWord_620594) baseStart_620594 baseEnd_620594 := by
    simpa [prefixWord, tailWord_620594, baseEnd_620594] using wordTrace_append hprefix tailTrace_620594
  have hstable : (prefixWord ++ tailWord_620594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620594).length < 2 ^ (prefixWord ++ tailWord_620594).sum := by decide
  have hdescent : baseEnd_620594 < baseStart_620594 := by decide
  rcases family_descends (prefixWord ++ tailWord_620594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620604 : List Nat := [2, 2, 2, 2, 2, 1, 1, 6, 2]
def baseStart_620604 : Nat := 118140960795 + 620604 * 2 ^ 59
def prefixEnd_620604 : Nat := 4983230072969 + 3 ^ 40 * 620604 * 2
def baseEnd_620604 : Nat := 283260576091551215729689

theorem tailTrace_620604 : CollatzResearch.WordTrace tailWord_620604 prefixEnd_620604 283260576091551215729689 := by
  unfold tailWord_620604
  simp only [CollatzResearch.WordTrace]
  refine ⟨11317643721832586784978433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15090191629110115713304577 11317643721832586784978433)
  ·
    refine ⟨8488232791374440088733825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11317643721832586784978433 8488232791374440088733825)
    ·
      refine ⟨6366174593530830066550369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8488232791374440088733825 6366174593530830066550369)
      ·
        refine ⟨4774630945148122549912777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6366174593530830066550369 4774630945148122549912777)
        ·
          refine ⟨3580973208861091912434583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4774630945148122549912777 3580973208861091912434583)
          ·
            refine ⟨5371459813291637868651875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580973208861091912434583 5371459813291637868651875)
            ·
              refine ⟨8057189719937456802977813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5371459813291637868651875 8057189719937456802977813)
              ·
                refine ⟨377680768122068287639585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8057189719937456802977813 377680768122068287639585)
                ·
                  refine ⟨283260576091551215729689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377680768122068287639585 283260576091551215729689)
                  ·
                    rfl

theorem cell20_620604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_620604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620604 prefixEnd_620604 := by exact prefixLift 620604
  have htrace : WordTrace (prefixWord ++ tailWord_620604) baseStart_620604 baseEnd_620604 := by
    simpa [prefixWord, tailWord_620604, baseEnd_620604] using wordTrace_append hprefix tailTrace_620604
  have hstable : (prefixWord ++ tailWord_620604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620604).length < 2 ^ (prefixWord ++ tailWord_620604).sum := by decide
  have hdescent : baseEnd_620604 < baseStart_620604 := by decide
  rcases family_descends (prefixWord ++ tailWord_620604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620632 : List Nat := [2, 1, 2, 2, 1, 5, 1, 6]
def baseStart_620632 : Nat := 118140960795 + 620632 * 2 ^ 59
def prefixEnd_620632 : Nat := 4983230072969 + 3 ^ 40 * 620632 * 2
def baseEnd_620632 : Nat := 94424452018169187598747

theorem tailTrace_620632 : CollatzResearch.WordTrace tailWord_620632 prefixEnd_620632 94424452018169187598747 := by
  unfold tailWord_620632
  simp only [CollatzResearch.WordTrace]
  refine ⟨11318154343781867175988075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15090872458375822901317433 11318154343781867175988075)
  ·
    refine ⟨16977231515672800763982113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11318154343781867175988075 16977231515672800763982113)
    ·
      refine ⟨12732923636754600572986585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16977231515672800763982113 12732923636754600572986585)
      ·
        refine ⟨9549692727565950429739939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12732923636754600572986585 9549692727565950429739939)
        ·
          refine ⟨14324539091348925644609909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9549692727565950429739939 14324539091348925644609909)
          ·
            refine ⟨1342925539813961779182179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14324539091348925644609909 1342925539813961779182179)
            ·
              refine ⟨2014388309720942668773269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342925539813961779182179 2014388309720942668773269)
              ·
                refine ⟨94424452018169187598747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2014388309720942668773269 94424452018169187598747)
                ·
                  rfl

theorem cell20_620632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_620632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620632 prefixEnd_620632 := by exact prefixLift 620632
  have htrace : WordTrace (prefixWord ++ tailWord_620632) baseStart_620632 baseEnd_620632 := by
    simpa [prefixWord, tailWord_620632, baseEnd_620632] using wordTrace_append hprefix tailTrace_620632
  have hstable : (prefixWord ++ tailWord_620632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620632).length < 2 ^ (prefixWord ++ tailWord_620632).sum := by decide
  have hdescent : baseEnd_620632 < baseStart_620632 := by decide
  rcases family_descends (prefixWord ++ tailWord_620632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620663 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_620663 : Nat := 118140960795 + 620663 * 2 ^ 59
def prefixEnd_620663 : Nat := 4983230072969 + 3 ^ 40 * 620663 * 2
def baseEnd_620663 : Nat := 283287505299209232762781

theorem tailTrace_620663 : CollatzResearch.WordTrace tailWord_620663 prefixEnd_620663 283287505299209232762781 := by
  unfold tailWord_620663
  simp only [CollatzResearch.WordTrace]
  refine ⟨22637439350451426646354643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15091626233634284430903095 22637439350451426646354643)
  ·
    refine ⟨33956159025677139969531965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22637439350451426646354643 33956159025677139969531965)
    ·
      refine ⟨12733559634628927488574487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33956159025677139969531965 12733559634628927488574487)
      ·
        refine ⟨19100339451943391232861731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12733559634628927488574487 19100339451943391232861731)
        ·
          refine ⟨28650509177915086849292597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19100339451943391232861731 28650509177915086849292597)
          ·
            refine ⟨2685985235429539392121181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28650509177915086849292597 2685985235429539392121181)
            ·
              refine ⟨1007244463286077272045443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2685985235429539392121181 1007244463286077272045443)
              ·
                refine ⟨1510866694929115908068165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007244463286077272045443 1510866694929115908068165)
                ·
                  refine ⟨283287505299209232762781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1510866694929115908068165 283287505299209232762781)
                  ·
                    rfl

theorem cell20_620663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_620663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620663 prefixEnd_620663 := by exact prefixLift 620663
  have htrace : WordTrace (prefixWord ++ tailWord_620663) baseStart_620663 baseEnd_620663 := by
    simpa [prefixWord, tailWord_620663, baseEnd_620663] using wordTrace_append hprefix tailTrace_620663
  have hstable : (prefixWord ++ tailWord_620663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620663).length < 2 ^ (prefixWord ++ tailWord_620663).sum := by decide
  have hdescent : baseEnd_620663 < baseStart_620663 := by decide
  rcases family_descends (prefixWord ++ tailWord_620663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620673 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 3]
def baseStart_620673 : Nat := 118140960795 + 620673 * 2 ^ 59
def prefixEnd_620673 : Nat := 4983230072969 + 3 ^ 40 * 620673 * 2
def baseEnd_620673 : Nat := 283292069571693642429407

theorem tailTrace_620673 : CollatzResearch.WordTrace tailWord_620673 prefixEnd_620673 283292069571693642429407 := by
  unfold tailWord_620673
  simp only [CollatzResearch.WordTrace]
  refine ⟨22637804080415198354218673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15091869386943465569479115 22637804080415198354218673)
  ·
    refine ⟨16978353060311398765664005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22637804080415198354218673 16978353060311398765664005)
    ·
      refine ⟨3183441198808387268562001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16978353060311398765664005 3183441198808387268562001)
      ·
        refine ⟨2387580899106290451421501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3183441198808387268562001 2387580899106290451421501)
        ·
          refine ⟨895342837164858919283063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2387580899106290451421501 895342837164858919283063)
          ·
            refine ⟨1343014255747288378924595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895342837164858919283063 1343014255747288378924595)
            ·
              refine ⟨2014521383620932568386893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343014255747288378924595 2014521383620932568386893)
              ·
                refine ⟨755445518857849713145085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2014521383620932568386893 755445518857849713145085)
                ·
                  refine ⟨283292069571693642429407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755445518857849713145085 283292069571693642429407)
                  ·
                    rfl

theorem cell20_620673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_620673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620673 prefixEnd_620673 := by exact prefixLift 620673
  have htrace : WordTrace (prefixWord ++ tailWord_620673) baseStart_620673 baseEnd_620673 := by
    simpa [prefixWord, tailWord_620673, baseEnd_620673] using wordTrace_append hprefix tailTrace_620673
  have hstable : (prefixWord ++ tailWord_620673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620673).length < 2 ^ (prefixWord ++ tailWord_620673).sum := by decide
  have hdescent : baseEnd_620673 < baseStart_620673 := by decide
  rcases family_descends (prefixWord ++ tailWord_620673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620708 : List Nat := [2, 3, 1, 2, 4, 8]
def baseStart_620708 : Nat := 118140960795 + 620708 * 2 ^ 59
def prefixEnd_620708 : Nat := 4983230072969 + 3 ^ 40 * 620708 * 2
def baseEnd_620708 : Nat := 10492890537977373194911

theorem tailTrace_620708 : CollatzResearch.WordTrace tailWord_620708 prefixEnd_620708 10492890537977373194911 := by
  unfold tailWord_620708
  simp only [CollatzResearch.WordTrace]
  refine ⟨11319540317644199665871389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15092720423525599554495185 11319540317644199665871389)
  ·
    refine ⟨4244827619116574874701771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11319540317644199665871389 4244827619116574874701771)
    ·
      refine ⟨6367241428674862312052657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4244827619116574874701771 6367241428674862312052657)
      ·
        refine ⟨4775431071506146734039493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6367241428674862312052657 4775431071506146734039493)
        ·
          refine ⟨895393325907402512632405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4775431071506146734039493 895393325907402512632405)
          ·
            refine ⟨10492890537977373194911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 895393325907402512632405 10492890537977373194911)
            ·
              rfl

theorem cell20_620708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 8].length) (baseStart_620708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620708 prefixEnd_620708 := by exact prefixLift 620708
  have htrace : WordTrace (prefixWord ++ tailWord_620708) baseStart_620708 baseEnd_620708 := by
    simpa [prefixWord, tailWord_620708, baseEnd_620708] using wordTrace_append hprefix tailTrace_620708
  have hstable : (prefixWord ++ tailWord_620708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620708).length < 2 ^ (prefixWord ++ tailWord_620708).sum := by decide
  have hdescent : baseEnd_620708 < baseStart_620708 := by decide
  rcases family_descends (prefixWord ++ tailWord_620708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620714 : List Nat := [3, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_620714 : Nat := 118140960795 + 620714 * 2 ^ 59
def prefixEnd_620714 : Nat := 4983230072969 + 3 ^ 40 * 620714 * 2
def baseEnd_620714 : Nat := 283310783088879722062573

theorem tailTrace_620714 : CollatzResearch.WordTrace tailWord_620714 prefixEnd_620714 283310783088879722062573 := by
  unfold tailWord_620714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5659824868316665589115299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15092866315511108237640797 5659824868316665589115299)
  ·
    refine ⟨8489737302474998383672949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5659824868316665589115299 8489737302474998383672949)
    ·
      refine ⟨795912872107031098469339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8489737302474998383672949 795912872107031098469339)
      ·
        refine ⟨1193869308160546647704009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795912872107031098469339 1193869308160546647704009)
        ·
          refine ⟨895401981120409985778007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1193869308160546647704009 895401981120409985778007)
          ·
            refine ⟨1343102971680614978667011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895401981120409985778007 1343102971680614978667011)
            ·
              refine ⟨2014654457520922468000517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343102971680614978667011 2014654457520922468000517)
              ·
                refine ⟨377747710785172962750097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2014654457520922468000517 377747710785172962750097)
                ·
                  refine ⟨283310783088879722062573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377747710785172962750097 283310783088879722062573)
                  ·
                    rfl

theorem cell20_620714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_620714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620714 prefixEnd_620714 := by exact prefixLift 620714
  have htrace : WordTrace (prefixWord ++ tailWord_620714) baseStart_620714 baseEnd_620714 := by
    simpa [prefixWord, tailWord_620714, baseEnd_620714] using wordTrace_append hprefix tailTrace_620714
  have hstable : (prefixWord ++ tailWord_620714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620714).length < 2 ^ (prefixWord ++ tailWord_620714).sum := by decide
  have hdescent : baseEnd_620714 < baseStart_620714 := by decide
  rcases family_descends (prefixWord ++ tailWord_620714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620807 : List Nat := [1, 1, 4, 5, 2, 1, 1, 3, 2]
def baseStart_620807 : Nat := 118140960795 + 620807 * 2 ^ 59
def prefixEnd_620807 : Nat := 4983230072969 + 3 ^ 40 * 620807 * 2
def baseEnd_620807 : Nat := 283353230822984731962193

theorem tailTrace_620807 : CollatzResearch.WordTrace tailWord_620807 prefixEnd_620807 283353230822984731962193 := by
  unfold tailWord_620807
  simp only [CollatzResearch.WordTrace]
  refine ⟨22642691461929739239596675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15095127641286492826397783 22642691461929739239596675)
  ·
    refine ⟨33964037192894608859395013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22642691461929739239596675 33964037192894608859395013)
    ·
      refine ⟨6368256973667739161136565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33964037192894608859395013 6368256973667739161136565)
      ·
        refine ⟨597024091281350546356553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6368256973667739161136565 597024091281350546356553)
        ·
          refine ⟨447768068461012909767415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597024091281350546356553 447768068461012909767415)
          ·
            refine ⟨671652102691519364651123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447768068461012909767415 671652102691519364651123)
            ·
              refine ⟨1007478154037279046976685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671652102691519364651123 1007478154037279046976685)
              ·
                refine ⟨377804307763979642616257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1007478154037279046976685 377804307763979642616257)
                ·
                  refine ⟨283353230822984731962193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377804307763979642616257 283353230822984731962193)
                  ·
                    rfl

theorem cell20_620807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 2].length) (baseStart_620807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620807 prefixEnd_620807 := by exact prefixLift 620807
  have htrace : WordTrace (prefixWord ++ tailWord_620807) baseStart_620807 baseEnd_620807 := by
    simpa [prefixWord, tailWord_620807, baseEnd_620807] using wordTrace_append hprefix tailTrace_620807
  have hstable : (prefixWord ++ tailWord_620807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620807).length < 2 ^ (prefixWord ++ tailWord_620807).sum := by decide
  have hdescent : baseEnd_620807 < baseStart_620807 := by decide
  rcases family_descends (prefixWord ++ tailWord_620807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620832 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 4]
def baseStart_620832 : Nat := 118140960795 + 620832 * 2 ^ 59
def prefixEnd_620832 : Nat := 4983230072969 + 3 ^ 40 * 620832 * 2
def baseEnd_620832 : Nat := 283364641504195756128757

theorem tailTrace_620832 : CollatzResearch.WordTrace tailWord_620832 prefixEnd_620832 283364641504195756128757 := by
  unfold tailWord_620832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321801643419584254628375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15095735524559445672837833 11321801643419584254628375)
  ·
    refine ⟨16982702465129376381942563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11321801643419584254628375 16982702465129376381942563)
    ·
      refine ⟨25474053697694064572913845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16982702465129376381942563 25474053697694064572913845)
      ·
        refine ⟨2388192534158818553710673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25474053697694064572913845 2388192534158818553710673)
        ·
          refine ⟨1791144400619113915283005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2388192534158818553710673 1791144400619113915283005)
          ·
            refine ⟨671679150232167718231127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1791144400619113915283005 671679150232167718231127)
            ·
              refine ⟨1007518725348251577346691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671679150232167718231127 1007518725348251577346691)
              ·
                refine ⟨1511278088022377366020037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007518725348251577346691 1511278088022377366020037)
                ·
                  refine ⟨283364641504195756128757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1511278088022377366020037 283364641504195756128757)
                  ·
                    rfl

theorem cell20_620832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 4].length) (baseStart_620832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620832 prefixEnd_620832 := by exact prefixLift 620832
  have htrace : WordTrace (prefixWord ++ tailWord_620832) baseStart_620832 baseEnd_620832 := by
    simpa [prefixWord, tailWord_620832, baseEnd_620832] using wordTrace_append hprefix tailTrace_620832
  have hstable : (prefixWord ++ tailWord_620832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620832).length < 2 ^ (prefixWord ++ tailWord_620832).sum := by decide
  have hdescent : baseEnd_620832 < baseStart_620832 := by decide
  rcases family_descends (prefixWord ++ tailWord_620832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620881 : List Nat := [1, 2, 2, 1, 4, 10]
def baseStart_620881 : Nat := 118140960795 + 620881 * 2 ^ 59
def prefixEnd_620881 : Nat := 4983230072969 + 3 ^ 40 * 620881 * 2
def baseEnd_620881 : Nat := 10495815053309976425749

theorem tailTrace_620881 : CollatzResearch.WordTrace tailWord_620881 prefixEnd_620881 10495815053309976425749 := by
  unfold tailWord_620881
  simp only [CollatzResearch.WordTrace]
  refine ⟨22645390463661649877790497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15096926975774433251860331 22645390463661649877790497)
  ·
    refine ⟨16984042847746237408342873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22645390463661649877790497 16984042847746237408342873)
    ·
      refine ⟨12738032135809678056257155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16984042847746237408342873 12738032135809678056257155)
      ·
        refine ⟨19107048203714517084385733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12738032135809678056257155 19107048203714517084385733)
        ·
          refine ⟨3582571538196471953322325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19107048203714517084385733 3582571538196471953322325)
          ·
            refine ⟨10495815053309976425749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3582571538196471953322325 10495815053309976425749)
            ·
              rfl

theorem cell20_620881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 10].length) (baseStart_620881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620881 prefixEnd_620881 := by exact prefixLift 620881
  have htrace : WordTrace (prefixWord ++ tailWord_620881) baseStart_620881 baseEnd_620881 := by
    simpa [prefixWord, tailWord_620881, baseEnd_620881] using wordTrace_append hprefix tailTrace_620881
  have hstable : (prefixWord ++ tailWord_620881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620881).length < 2 ^ (prefixWord ++ tailWord_620881).sum := by decide
  have hdescent : baseEnd_620881 < baseStart_620881 := by decide
  rcases family_descends (prefixWord ++ tailWord_620881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620884 : List Nat := [2, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_620884 : Nat := 118140960795 + 620884 * 2 ^ 59
def prefixEnd_620884 : Nat := 4983230072969 + 3 ^ 40 * 620884 * 2
def baseEnd_620884 : Nat := 283388375721114686395211

theorem tailTrace_620884 : CollatzResearch.WordTrace tailWord_620884 prefixEnd_620884 283388375721114686395211 := by
  unfold tailWord_620884
  simp only [CollatzResearch.WordTrace]
  refine ⟨11322749941325390695074853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15096999921767187593433137 11322749941325390695074853)
  ·
    refine ⟨2123015613998510755326535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11322749941325390695074853 2123015613998510755326535)
    ·
      refine ⟨3184523420997766132989803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2123015613998510755326535 3184523420997766132989803)
      ·
        refine ⟨4776785131496649199484705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184523420997766132989803 4776785131496649199484705)
        ·
          refine ⟨3582588848622486899613529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4776785131496649199484705 3582588848622486899613529)
          ·
            refine ⟨2686941636466865174710147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3582588848622486899613529 2686941636466865174710147)
            ·
              refine ⟨4030412454700297762065221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686941636466865174710147 4030412454700297762065221)
              ·
                refine ⟨755702335256305830387229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4030412454700297762065221 755702335256305830387229)
                ·
                  refine ⟨283388375721114686395211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755702335256305830387229 283388375721114686395211)
                  ·
                    rfl

theorem cell20_620884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_620884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620884 prefixEnd_620884 := by exact prefixLift 620884
  have htrace : WordTrace (prefixWord ++ tailWord_620884) baseStart_620884 baseEnd_620884 := by
    simpa [prefixWord, tailWord_620884, baseEnd_620884] using wordTrace_append hprefix tailTrace_620884
  have hstable : (prefixWord ++ tailWord_620884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620884).length < 2 ^ (prefixWord ++ tailWord_620884).sum := by decide
  have hdescent : baseEnd_620884 < baseStart_620884 := by decide
  rcases family_descends (prefixWord ++ tailWord_620884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620905 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 3]
def baseStart_620905 : Nat := 118140960795 + 620905 * 2 ^ 59
def prefixEnd_620905 : Nat := 4983230072969 + 3 ^ 40 * 620905 * 2
def baseEnd_620905 : Nat := 283397960693331946695125

theorem tailTrace_620905 : CollatzResearch.WordTrace tailWord_620905 prefixEnd_620905 283397960693331946695125 := by
  unfold tailWord_620905
  simp only [CollatzResearch.WordTrace]
  refine ⟨22646265815574701976664169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15097510543716467984442779 22646265815574701976664169)
  ·
    refine ⟨16984699361681026482498127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22646265815574701976664169 16984699361681026482498127)
    ·
      refine ⟨25477049042521539723747191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16984699361681026482498127 25477049042521539723747191)
      ·
        refine ⟨38215573563782309585620787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25477049042521539723747191 38215573563782309585620787)
        ·
          refine ⟨57323360345673464378431181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38215573563782309585620787 57323360345673464378431181)
          ·
            refine ⟨21496260129627549141911693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57323360345673464378431181 21496260129627549141911693)
            ·
              refine ⟨8061097548610330928216885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21496260129627549141911693 8061097548610330928216885)
              ·
                refine ⟨755727895182218524520333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8061097548610330928216885 755727895182218524520333)
                ·
                  refine ⟨283397960693331946695125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755727895182218524520333 283397960693331946695125)
                  ·
                    rfl

theorem cell20_620905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_620905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620905 prefixEnd_620905 := by exact prefixLift 620905
  have htrace : WordTrace (prefixWord ++ tailWord_620905) baseStart_620905 baseEnd_620905 := by
    simpa [prefixWord, tailWord_620905, baseEnd_620905] using wordTrace_append hprefix tailTrace_620905
  have hstable : (prefixWord ++ tailWord_620905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620905).length < 2 ^ (prefixWord ++ tailWord_620905).sum := by decide
  have hdescent : baseEnd_620905 < baseStart_620905 := by decide
  rcases family_descends (prefixWord ++ tailWord_620905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620912 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_620912 : Nat := 118140960795 + 620912 * 2 ^ 59
def prefixEnd_620912 : Nat := 4983230072969 + 3 ^ 40 * 620912 * 2
def baseEnd_620912 : Nat := 283401155684071033461763

theorem tailTrace_620912 : CollatzResearch.WordTrace tailWord_620912 prefixEnd_620912 283401155684071033461763 := by
  unfold tailWord_620912
  simp only [CollatzResearch.WordTrace]
  refine ⟨11323260563274671086084495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15097680751032894781445993 11323260563274671086084495)
  ·
    refine ⟨16984890844912006629126743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11323260563274671086084495 16984890844912006629126743)
    ·
      refine ⟨25477336267368009943690115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16984890844912006629126743 25477336267368009943690115)
      ·
        refine ⟨38216004401052014915535173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25477336267368009943690115 38216004401052014915535173)
        ·
          refine ⟨7165500825197252796662845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38216004401052014915535173 7165500825197252796662845)
          ·
            refine ⟨2687062809448969798748567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7165500825197252796662845 2687062809448969798748567)
            ·
              refine ⟨4030594214173454698122851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687062809448969798748567 4030594214173454698122851)
              ·
                refine ⟨6045891321260182047184277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030594214173454698122851 6045891321260182047184277)
                ·
                  refine ⟨283401155684071033461763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6045891321260182047184277 283401155684071033461763)
                  ·
                    rfl

theorem cell20_620912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_620912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620912 prefixEnd_620912 := by exact prefixLift 620912
  have htrace : WordTrace (prefixWord ++ tailWord_620912) baseStart_620912 baseEnd_620912 := by
    simpa [prefixWord, tailWord_620912, baseEnd_620912] using wordTrace_append hprefix tailTrace_620912
  have hstable : (prefixWord ++ tailWord_620912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620912).length < 2 ^ (prefixWord ++ tailWord_620912).sum := by decide
  have hdescent : baseEnd_620912 < baseStart_620912 := by decide
  rcases family_descends (prefixWord ++ tailWord_620912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620967 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_620967 : Nat := 118140960795 + 620967 * 2 ^ 59
def prefixEnd_620967 : Nat := 4983230072969 + 3 ^ 40 * 620967 * 2
def baseEnd_620967 : Nat := 283426259182735286628205

theorem tailTrace_620967 : CollatzResearch.WordTrace tailWord_620967 prefixEnd_620967 283426259182735286628205 := by
  unfold tailWord_620967
  simp only [CollatzResearch.WordTrace]
  refine ⟨22648527141350086565421155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15099018094233391043614103 22648527141350086565421155)
  ·
    refine ⟨33972790712025129848131733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22648527141350086565421155 33972790712025129848131733)
    ·
      refine ⟨1592474564626177961631175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33972790712025129848131733 1592474564626177961631175)
      ·
        refine ⟨2388711846939266942446763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592474564626177961631175 2388711846939266942446763)
        ·
          refine ⟨3583067770408900413670145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388711846939266942446763 3583067770408900413670145)
          ·
            refine ⟨2687300827806675310252609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3583067770408900413670145 2687300827806675310252609)
            ·
              refine ⟨2015475620855006482689457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687300827806675310252609 2015475620855006482689457)
              ·
                refine ⟨1511606715641254862017093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015475620855006482689457 1511606715641254862017093)
                ·
                  refine ⟨283426259182735286628205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1511606715641254862017093 283426259182735286628205)
                  ·
                    rfl

theorem cell20_620967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_620967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_620967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_620967 prefixEnd_620967 := by exact prefixLift 620967
  have htrace : WordTrace (prefixWord ++ tailWord_620967) baseStart_620967 baseEnd_620967 := by
    simpa [prefixWord, tailWord_620967, baseEnd_620967] using wordTrace_append hprefix tailTrace_620967
  have hstable : (prefixWord ++ tailWord_620967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620967).length < 2 ^ (prefixWord ++ tailWord_620967).sum := by decide
  have hdescent : baseEnd_620967 < baseStart_620967 := by decide
  rcases family_descends (prefixWord ++ tailWord_620967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621012 : List Nat := [2, 4, 1, 2, 2, 1, 1, 7]
def baseStart_621012 : Nat := 118140960795 + 621012 * 2 ^ 59
def prefixEnd_621012 : Nat := 4983230072969 + 3 ^ 40 * 621012 * 2
def baseEnd_621012 : Nat := 94482266136305043376007

theorem tailTrace_621012 : CollatzResearch.WordTrace tailWord_621012 prefixEnd_621012 94482266136305043376007 := by
  unfold tailWord_621012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11325084213093529625404645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15100112284124706167206193 11325084213093529625404645)
  ·
    refine ⟨2123453289955036804763371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11325084213093529625404645 2123453289955036804763371)
    ·
      refine ⟨3185179934932555207145057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2123453289955036804763371 3185179934932555207145057)
      ·
        refine ⟨2388884951199416405358793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3185179934932555207145057 2388884951199416405358793)
        ·
          refine ⟨1791663713399562304019095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2388884951199416405358793 1791663713399562304019095)
          ·
            refine ⟨2687495570099343456028643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791663713399562304019095 2687495570099343456028643)
            ·
              refine ⟨4031243355149015184042965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687495570099343456028643 4031243355149015184042965)
              ·
                refine ⟨94482266136305043376007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4031243355149015184042965 94482266136305043376007)
                ·
                  rfl

theorem cell20_621012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_621012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621012 prefixEnd_621012 := by exact prefixLift 621012
  have htrace : WordTrace (prefixWord ++ tailWord_621012) baseStart_621012 baseEnd_621012 := by
    simpa [prefixWord, tailWord_621012, baseEnd_621012] using wordTrace_append hprefix tailTrace_621012
  have hstable : (prefixWord ++ tailWord_621012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621012).length < 2 ^ (prefixWord ++ tailWord_621012).sum := by decide
  have hdescent : baseEnd_621012 < baseStart_621012 := by decide
  rcases family_descends (prefixWord ++ tailWord_621012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621043 : List Nat := [1, 1, 1, 2, 2, 2, 4, 5, 2]
def baseStart_621043 : Nat := 118140960795 + 621043 * 2 ^ 59
def prefixEnd_621043 : Nat := 4983230072969 + 3 ^ 40 * 621043 * 2
def baseEnd_621043 : Nat := 283460947653616800094561

theorem tailTrace_621043 : CollatzResearch.WordTrace tailWord_621043 prefixEnd_621043 283460947653616800094561 := by
  unfold tailWord_621043
  simp only [CollatzResearch.WordTrace]
  refine ⟨22651299089074751545187783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15100866059383167696791855 22651299089074751545187783)
  ·
    refine ⟨33976948633612127317781675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22651299089074751545187783 33976948633612127317781675)
    ·
      refine ⟨50965422950418190976672513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33976948633612127317781675 50965422950418190976672513)
      ·
        refine ⟨38224067212813643232504385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50965422950418190976672513 38224067212813643232504385)
        ·
          refine ⟨28668050409610232424378289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38224067212813643232504385 28668050409610232424378289)
          ·
            refine ⟨21501037807207674318283717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28668050409610232424378289 21501037807207674318283717)
            ·
              refine ⟨4031444588851438934678197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21501037807207674318283717 4031444588851438934678197)
              ·
                refine ⟨377947930204822400126081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4031444588851438934678197 377947930204822400126081)
                ·
                  refine ⟨283460947653616800094561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377947930204822400126081 283460947653616800094561)
                  ·
                    rfl

theorem cell20_621043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 2].length) (baseStart_621043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621043 prefixEnd_621043 := by exact prefixLift 621043
  have htrace : WordTrace (prefixWord ++ tailWord_621043) baseStart_621043 baseEnd_621043 := by
    simpa [prefixWord, tailWord_621043, baseEnd_621043] using wordTrace_append hprefix tailTrace_621043
  have hstable : (prefixWord ++ tailWord_621043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621043).length < 2 ^ (prefixWord ++ tailWord_621043).sum := by decide
  have hdescent : baseEnd_621043 < baseStart_621043 := by decide
  rcases family_descends (prefixWord ++ tailWord_621043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621064 : List Nat := [2, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_621064 : Nat := 118140960795 + 621064 * 2 ^ 59
def prefixEnd_621064 : Nat := 4983230072969 + 3 ^ 40 * 621064 * 2
def baseEnd_621064 : Nat := 283470532625834060394475

theorem tailTrace_621064 : CollatzResearch.WordTrace tailWord_621064 prefixEnd_621064 283470532625834060394475 := by
  unfold tailWord_621064
  simp only [CollatzResearch.WordTrace]
  refine ⟨11326032510999336065851123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15101376681332448087801497 11326032510999336065851123)
  ·
    refine ⟨16989048766499004098776685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11326032510999336065851123 16989048766499004098776685)
    ·
      refine ⟨6370893287437126537041257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16989048766499004098776685 6370893287437126537041257)
      ·
        refine ⟨4778169965577844902780943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6370893287437126537041257 4778169965577844902780943)
        ·
          refine ⟨7167254948366767354171415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778169965577844902780943 7167254948366767354171415)
          ·
            refine ⟨10750882422550151031257123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7167254948366767354171415 10750882422550151031257123)
            ·
              refine ⟨16126323633825226546885685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10750882422550151031257123 16126323633825226546885685)
              ·
                refine ⟨1511842840671114988770533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16126323633825226546885685 1511842840671114988770533)
                ·
                  refine ⟨283470532625834060394475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1511842840671114988770533 283470532625834060394475)
                  ·
                    rfl

theorem cell20_621064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_621064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621064 prefixEnd_621064 := by exact prefixLift 621064
  have htrace : WordTrace (prefixWord ++ tailWord_621064) baseStart_621064 baseEnd_621064 := by
    simpa [prefixWord, tailWord_621064, baseEnd_621064] using wordTrace_append hprefix tailTrace_621064
  have hstable : (prefixWord ++ tailWord_621064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621064).length < 2 ^ (prefixWord ++ tailWord_621064).sum := by decide
  have hdescent : baseEnd_621064 < baseStart_621064 := by decide
  rcases family_descends (prefixWord ++ tailWord_621064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621098 : List Nat := [3, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_621098 : Nat := 118140960795 + 621098 * 2 ^ 59
def prefixEnd_621098 : Nat := 4983230072969 + 3 ^ 40 * 621098 * 2
def baseEnd_621098 : Nat := 283486051152281053261003

theorem tailTrace_621098 : CollatzResearch.WordTrace tailWord_621098 prefixEnd_621098 283486051152281053261003 := by
  unfold tailWord_621098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663326275968873984609987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15102203402583663958959965 5663326275968873984609987)
  ·
    refine ⟨8494989413953310976914981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5663326275968873984609987 8494989413953310976914981)
    ·
      refine ⟨1592810515116245808171559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8494989413953310976914981 1592810515116245808171559)
      ·
        refine ⟨2389215772674368712257339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592810515116245808171559 2389215772674368712257339)
        ·
          refine ⟨3583823659011553068386009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389215772674368712257339 3583823659011553068386009)
          ·
            refine ⟨2687867744258664801289507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3583823659011553068386009 2687867744258664801289507)
            ·
              refine ⟨4031801616387997201934261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687867744258664801289507 4031801616387997201934261)
              ·
                refine ⟨377981401536374737681337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4031801616387997201934261 377981401536374737681337)
                ·
                  refine ⟨283486051152281053261003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377981401536374737681337 283486051152281053261003)
                  ·
                    rfl

theorem cell20_621098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_621098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621098 prefixEnd_621098 := by exact prefixLift 621098
  have htrace : WordTrace (prefixWord ++ tailWord_621098) baseStart_621098 baseEnd_621098 := by
    simpa [prefixWord, tailWord_621098, baseEnd_621098] using wordTrace_append hprefix tailTrace_621098
  have hstable : (prefixWord ++ tailWord_621098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621098).length < 2 ^ (prefixWord ++ tailWord_621098).sum := by decide
  have hdescent : baseEnd_621098 < baseStart_621098 := by decide
  rcases family_descends (prefixWord ++ tailWord_621098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621109 : List Nat := [1, 3, 3, 1, 1, 2, 9]
def baseStart_621109 : Nat := 118140960795 + 621109 * 2 ^ 59
def prefixEnd_621109 : Nat := 4983230072969 + 3 ^ 40 * 621109 * 2
def baseEnd_621109 : Nat := 31499007983557100432699

theorem tailTrace_621109 : CollatzResearch.WordTrace tailWord_621109 prefixEnd_621109 31499007983557100432699 := by
  unfold tailWord_621109
  simp only [CollatzResearch.WordTrace]
  refine ⟨22653706306835644817090381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15102470871223763211393587 22653706306835644817090381)
  ·
    refine ⟨8495139865063366806408893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22653706306835644817090381 8495139865063366806408893)
    ·
      refine ⟨3185677449398762552403335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8495139865063366806408893 3185677449398762552403335)
      ·
        refine ⟨4778516174098143828605003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3185677449398762552403335 4778516174098143828605003)
        ·
          refine ⟨7167774261147215742907505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778516174098143828605003 7167774261147215742907505)
          ·
            refine ⟨5375830695860411807180629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167774261147215742907505 5375830695860411807180629)
            ·
              refine ⟨31499007983557100432699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5375830695860411807180629 31499007983557100432699)
              ·
                rfl

theorem cell20_621109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 9].length) (baseStart_621109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621109 prefixEnd_621109 := by exact prefixLift 621109
  have htrace : WordTrace (prefixWord ++ tailWord_621109) baseStart_621109 baseEnd_621109 := by
    simpa [prefixWord, tailWord_621109, baseEnd_621109] using wordTrace_append hprefix tailTrace_621109
  have hstable : (prefixWord ++ tailWord_621109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621109).length < 2 ^ (prefixWord ++ tailWord_621109).sum := by decide
  have hdescent : baseEnd_621109 < baseStart_621109 := by decide
  rcases family_descends (prefixWord ++ tailWord_621109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621119 : List Nat := [1, 1, 2, 2, 3, 2, 1, 6, 2]
def baseStart_621119 : Nat := 118140960795 + 621119 * 2 ^ 59
def prefixEnd_621119 : Nat := 4983230072969 + 3 ^ 40 * 621119 * 2
def baseEnd_621119 : Nat := 283495636124498313560917

theorem tailTrace_621119 : CollatzResearch.WordTrace tailWord_621119 prefixEnd_621119 283495636124498313560917 := by
  unfold tailWord_621119
  simp only [CollatzResearch.WordTrace]
  refine ⟨22654071036799416524954411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15102714024532944349969607 22654071036799416524954411)
  ·
    refine ⟨33981106555199124787431617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22654071036799416524954411 33981106555199124787431617)
    ·
      refine ⟨25485829916399343590573713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33981106555199124787431617 25485829916399343590573713)
      ·
        refine ⟨19114372437299507692930285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25485829916399343590573713 19114372437299507692930285)
        ·
          refine ⟨7167889663987315384848857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19114372437299507692930285 7167889663987315384848857)
          ·
            refine ⟨5375917247990486538636643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167889663987315384848857 5375917247990486538636643)
            ·
              refine ⟨8063875871985729807954965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375917247990486538636643 8063875871985729807954965)
              ·
                refine ⟨377994181499331084747889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8063875871985729807954965 377994181499331084747889)
                ·
                  refine ⟨283495636124498313560917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377994181499331084747889 283495636124498313560917)
                  ·
                    rfl

theorem cell20_621119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 2].length) (baseStart_621119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621119 prefixEnd_621119 := by exact prefixLift 621119
  have htrace : WordTrace (prefixWord ++ tailWord_621119) baseStart_621119 baseEnd_621119 := by
    simpa [prefixWord, tailWord_621119, baseEnd_621119] using wordTrace_append hprefix tailTrace_621119
  have hstable : (prefixWord ++ tailWord_621119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621119).length < 2 ^ (prefixWord ++ tailWord_621119).sum := by decide
  have hdescent : baseEnd_621119 < baseStart_621119 := by decide
  rcases family_descends (prefixWord ++ tailWord_621119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621188 : List Nat := [2, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_621188 : Nat := 118140960795 + 621188 * 2 ^ 59
def prefixEnd_621188 : Nat := 4983230072969 + 3 ^ 40 * 621188 * 2
def baseEnd_621188 : Nat := 283527129604640740260635

theorem tailTrace_621188 : CollatzResearch.WordTrace tailWord_621188 prefixEnd_621188 283527129604640740260635 := by
  unfold tailWord_621188
  simp only [CollatzResearch.WordTrace]
  refine ⟨11328293836774720654608109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15104391782366294206144145 11328293836774720654608109)
  ·
    refine ⟨4248110188790520245478041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11328293836774720654608109 4248110188790520245478041)
    ·
      refine ⟨3186082641592890184108531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4248110188790520245478041 3186082641592890184108531)
      ·
        refine ⟨4779123962389335276162797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3186082641592890184108531 4779123962389335276162797)
        ·
          refine ⟨1792171485896000728561049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4779123962389335276162797 1792171485896000728561049)
          ·
            refine ⟨1344128614422000546420787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1792171485896000728561049 1344128614422000546420787)
            ·
              refine ⟨2016192921633000819631181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344128614422000546420787 2016192921633000819631181)
              ·
                refine ⟨756072345612375307361693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2016192921633000819631181 756072345612375307361693)
                ·
                  refine ⟨283527129604640740260635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756072345612375307361693 283527129604640740260635)
                  ·
                    rfl

theorem cell20_621188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_621188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621188 prefixEnd_621188 := by exact prefixLift 621188
  have htrace : WordTrace (prefixWord ++ tailWord_621188) baseStart_621188 baseEnd_621188 := by
    simpa [prefixWord, tailWord_621188, baseEnd_621188] using wordTrace_append hprefix tailTrace_621188
  have hstable : (prefixWord ++ tailWord_621188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621188).length < 2 ^ (prefixWord ++ tailWord_621188).sum := by decide
  have hdescent : baseEnd_621188 < baseStart_621188 := by decide
  rcases family_descends (prefixWord ++ tailWord_621188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621202 : List Nat := [3, 2, 3, 1, 2, 1, 2, 6]
def baseStart_621202 : Nat := 118140960795 + 621202 * 2 ^ 59
def prefixEnd_621202 : Nat := 4983230072969 + 3 ^ 40 * 621202 * 2
def baseEnd_621202 : Nat := 94511173195372971264637

theorem tailTrace_621202 : CollatzResearch.WordTrace tailWord_621202 prefixEnd_621202 94511173195372971264637 := by
  unfold tailWord_621202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5664274573874680425056465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15104732196999147800150573 5664274573874680425056465)
  ·
    refine ⟨4248205930406010318792349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5664274573874680425056465 4248205930406010318792349)
    ·
      refine ⟨1593077223902253869547131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4248205930406010318792349 1593077223902253869547131)
      ·
        refine ⟨2389615835853380804320697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593077223902253869547131 2389615835853380804320697)
        ·
          refine ⟨1792211876890035603240523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2389615835853380804320697 1792211876890035603240523)
          ·
            refine ⟨2688317815335053404860785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792211876890035603240523 2688317815335053404860785)
            ·
              refine ⟨2016238361501290053645589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2688317815335053404860785 2016238361501290053645589)
              ·
                refine ⟨94511173195372971264637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2016238361501290053645589 94511173195372971264637)
                ·
                  rfl

theorem cell20_621202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_621202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621202 prefixEnd_621202 := by exact prefixLift 621202
  have htrace : WordTrace (prefixWord ++ tailWord_621202) baseStart_621202 baseEnd_621202 := by
    simpa [prefixWord, tailWord_621202, baseEnd_621202] using wordTrace_append hprefix tailTrace_621202
  have hstable : (prefixWord ++ tailWord_621202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621202).length < 2 ^ (prefixWord ++ tailWord_621202).sum := by decide
  have hdescent : baseEnd_621202 < baseStart_621202 := by decide
  rcases family_descends (prefixWord ++ tailWord_621202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621229 : List Nat := [1, 5, 2, 1, 1, 2, 4, 2, 2]
def baseStart_621229 : Nat := 118140960795 + 621229 * 2 ^ 59
def prefixEnd_621229 : Nat := 4983230072969 + 3 ^ 40 * 621229 * 2
def baseEnd_621229 : Nat := 283545843121826819893801

theorem tailTrace_621229 : CollatzResearch.WordTrace tailWord_621229 prefixEnd_621229 283545843121826819893801 := by
  unfold tailWord_621229
  simp only [CollatzResearch.WordTrace]
  refine ⟨22658083066400905311458741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15105388710933936874305827 22658083066400905311458741)
  ·
    refine ⟨2124195287475084872949257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22658083066400905311458741 2124195287475084872949257)
    ·
      refine ⟨1593146465606313654711943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2124195287475084872949257 1593146465606313654711943)
      ·
        refine ⟨2389719698409470482067915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593146465606313654711943 2389719698409470482067915)
        ·
          refine ⟨3584579547614205723101873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389719698409470482067915 3584579547614205723101873)
          ·
            refine ⟨2688434660710654292326405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3584579547614205723101873 2688434660710654292326405)
            ·
              refine ⟨504081498883247679811201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2688434660710654292326405 504081498883247679811201)
              ·
                refine ⟨378061124162435759858401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504081498883247679811201 378061124162435759858401)
                ·
                  refine ⟨283545843121826819893801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378061124162435759858401 283545843121826819893801)
                  ·
                    rfl

theorem cell20_621229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_621229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621229 prefixEnd_621229 := by exact prefixLift 621229
  have htrace : WordTrace (prefixWord ++ tailWord_621229) baseStart_621229 baseEnd_621229 := by
    simpa [prefixWord, tailWord_621229, baseEnd_621229] using wordTrace_append hprefix tailTrace_621229
  have hstable : (prefixWord ++ tailWord_621229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621229).length < 2 ^ (prefixWord ++ tailWord_621229).sum := by decide
  have hdescent : baseEnd_621229 < baseStart_621229 := by decide
  rcases family_descends (prefixWord ++ tailWord_621229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621247 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 3]
def baseStart_621247 : Nat := 118140960795 + 621247 * 2 ^ 59
def prefixEnd_621247 : Nat := 4983230072969 + 3 ^ 40 * 621247 * 2
def baseEnd_621247 : Nat := 283554058812298757293727

theorem tailTrace_621247 : CollatzResearch.WordTrace tailWord_621247 prefixEnd_621247 283554058812298757293727 := by
  unfold tailWord_621247
  simp only [CollatzResearch.WordTrace]
  refine ⟨22658739580335694385613995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15105826386890462923742663 22658739580335694385613995)
  ·
    refine ⟨33988109370503541578420993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22658739580335694385613995 33988109370503541578420993)
    ·
      refine ⟨25491082027877656183815745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33988109370503541578420993 25491082027877656183815745)
      ·
        refine ⟨19118311520908242137861809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25491082027877656183815745 19118311520908242137861809)
        ·
          refine ⟨14338733640681181603396357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19118311520908242137861809 14338733640681181603396357)
          ·
            refine ⟨2688512557627721550636817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14338733640681181603396357 2688512557627721550636817)
            ·
              refine ⟨2016384418220791162977613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2688512557627721550636817 2016384418220791162977613)
              ·
                refine ⟨756144156832796686116605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2016384418220791162977613 756144156832796686116605)
                ·
                  refine ⟨283554058812298757293727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756144156832796686116605 283554058812298757293727)
                  ·
                    rfl

theorem cell20_621247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_621247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621247 prefixEnd_621247 := by exact prefixLift 621247
  have htrace : WordTrace (prefixWord ++ tailWord_621247) baseStart_621247 baseEnd_621247 := by
    simpa [prefixWord, tailWord_621247, baseEnd_621247] using wordTrace_append hprefix tailTrace_621247
  have hstable : (prefixWord ++ tailWord_621247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621247).length < 2 ^ (prefixWord ++ tailWord_621247).sum := by decide
  have hdescent : baseEnd_621247 < baseStart_621247 := by decide
  rcases family_descends (prefixWord ++ tailWord_621247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621271 : List Nat := [1, 1, 3, 2, 1, 4, 1, 5, 2]
def baseStart_621271 : Nat := 118140960795 + 621271 * 2 ^ 59
def prefixEnd_621271 : Nat := 4983230072969 + 3 ^ 40 * 621271 * 2
def baseEnd_621271 : Nat := 283565013066261340493629

theorem tailTrace_621271 : CollatzResearch.WordTrace tailWord_621271 prefixEnd_621271 283565013066261340493629 := by
  unfold tailWord_621271
  simp only [CollatzResearch.WordTrace]
  refine ⟨22659614932248746484487667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15106409954832497656325111 22659614932248746484487667)
  ·
    refine ⟨33989422398373119726731501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22659614932248746484487667 33989422398373119726731501)
    ·
      refine ⟨12746033399389919897524313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33989422398373119726731501 12746033399389919897524313)
      ·
        refine ⟨9559525049542439923143235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12746033399389919897524313 9559525049542439923143235)
        ·
          refine ⟨14339287574313659884714853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9559525049542439923143235 14339287574313659884714853)
          ·
            refine ⟨2688616420183811228384035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14339287574313659884714853 2688616420183811228384035)
            ·
              refine ⟨4032924630275716842576053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688616420183811228384035 4032924630275716842576053)
              ·
                refine ⟨378086684088348453991505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4032924630275716842576053 378086684088348453991505)
                ·
                  refine ⟨283565013066261340493629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378086684088348453991505 283565013066261340493629)
                  ·
                    rfl

theorem cell20_621271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 2].length) (baseStart_621271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621271 prefixEnd_621271 := by exact prefixLift 621271
  have htrace : WordTrace (prefixWord ++ tailWord_621271) baseStart_621271 baseEnd_621271 := by
    simpa [prefixWord, tailWord_621271, baseEnd_621271] using wordTrace_append hprefix tailTrace_621271
  have hstable : (prefixWord ++ tailWord_621271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621271).length < 2 ^ (prefixWord ++ tailWord_621271).sum := by decide
  have hdescent : baseEnd_621271 < baseStart_621271 := by decide
  rcases family_descends (prefixWord ++ tailWord_621271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621285 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_621285 : Nat := 118140960795 + 621285 * 2 ^ 59
def prefixEnd_621285 : Nat := 4983230072969 + 3 ^ 40 * 621285 * 2
def baseEnd_621285 : Nat := 283571403047739514026905

theorem tailTrace_621285 : CollatzResearch.WordTrace tailWord_621285 prefixEnd_621285 283571403047739514026905 := by
  unfold tailWord_621285
  simp only [CollatzResearch.WordTrace]
  refine ⟨22660125554198026875497309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15106750369465351250331539 22660125554198026875497309)
  ·
    refine ⟨8497547082824260078311491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22660125554198026875497309 8497547082824260078311491)
    ·
      refine ⟨12746320624236390117467237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8497547082824260078311491 12746320624236390117467237)
      ·
        refine ⟨2389935117044323147025107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12746320624236390117467237 2389935117044323147025107)
        ·
          refine ⟨3584902675566484720537661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389935117044323147025107 3584902675566484720537661)
          ·
            refine ⟨1344338503337431770201623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3584902675566484720537661 1344338503337431770201623)
            ·
              refine ⟨2016507755006147655302435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344338503337431770201623 2016507755006147655302435)
              ·
                refine ⟨3024761632509221482953653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016507755006147655302435 3024761632509221482953653)
                ·
                  refine ⟨283571403047739514026905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3024761632509221482953653 283571403047739514026905)
                  ·
                    rfl

theorem cell20_621285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_621285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621285 prefixEnd_621285 := by exact prefixLift 621285
  have htrace : WordTrace (prefixWord ++ tailWord_621285) baseStart_621285 baseEnd_621285 := by
    simpa [prefixWord, tailWord_621285, baseEnd_621285] using wordTrace_append hprefix tailTrace_621285
  have hstable : (prefixWord ++ tailWord_621285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621285).length < 2 ^ (prefixWord ++ tailWord_621285).sum := by decide
  have hdescent : baseEnd_621285 < baseStart_621285 := by decide
  rcases family_descends (prefixWord ++ tailWord_621285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621361 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 3]
def baseStart_621361 : Nat := 118140960795 + 621361 * 2 ^ 59
def prefixEnd_621361 : Nat := 4983230072969 + 3 ^ 40 * 621361 * 2
def baseEnd_621361 : Nat := 283606091518621027493261

theorem tailTrace_621361 : CollatzResearch.WordTrace tailWord_621361 prefixEnd_621361 283606091518621027493261 := by
  unfold tailWord_621361
  simp only [CollatzResearch.WordTrace]
  refine ⟨22662897501922691855263937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15108598334615127903509291 22662897501922691855263937)
  ·
    refine ⟨16997173126442018891447953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22662897501922691855263937 16997173126442018891447953)
    ·
      refine ⟨12747879844831514168585965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16997173126442018891447953 12747879844831514168585965)
      ·
        refine ⟨4780454941811817813219737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12747879844831514168585965 4780454941811817813219737)
        ·
          refine ⟨3585341206358863359914803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4780454941811817813219737 3585341206358863359914803)
          ·
            refine ⟨5378011809538295039872205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585341206358863359914803 5378011809538295039872205)
            ·
              refine ⟨2016754428576860639952077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5378011809538295039872205 2016754428576860639952077)
              ·
                refine ⟨756282910716322739982029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2016754428576860639952077 756282910716322739982029)
                ·
                  refine ⟨283606091518621027493261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756282910716322739982029 283606091518621027493261)
                  ·
                    rfl

theorem cell20_621361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_621361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621361 prefixEnd_621361 := by exact prefixLift 621361
  have htrace : WordTrace (prefixWord ++ tailWord_621361) baseStart_621361 baseEnd_621361 := by
    simpa [prefixWord, tailWord_621361, baseEnd_621361] using wordTrace_append hprefix tailTrace_621361
  have hstable : (prefixWord ++ tailWord_621361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621361).length < 2 ^ (prefixWord ++ tailWord_621361).sum := by decide
  have hdescent : baseEnd_621361 < baseStart_621361 := by decide
  rcases family_descends (prefixWord ++ tailWord_621361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621375 : List Nat := [1, 1, 2, 2, 5, 1, 2, 6]
def baseStart_621375 : Nat := 118140960795 + 621375 * 2 ^ 59
def prefixEnd_621375 : Nat := 4983230072969 + 3 ^ 40 * 621375 * 2
def baseEnd_621375 : Nat := 94537493833366400342179

theorem tailTrace_621375 : CollatzResearch.WordTrace tailWord_621375 prefixEnd_621375 94537493833366400342179 := by
  unfold tailWord_621375
  simp only [CollatzResearch.WordTrace]
  refine ⟨22663408123871972246273579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15108938749247981497515719 22663408123871972246273579)
  ·
    refine ⟨33995112185807958369410369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22663408123871972246273579 33995112185807958369410369)
    ·
      refine ⟨25496334139355968777057777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33995112185807958369410369 25496334139355968777057777)
      ·
        refine ⟨19122250604516976582793333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25496334139355968777057777 19122250604516976582793333)
        ·
          refine ⟨1792710994173466554636875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19122250604516976582793333 1792710994173466554636875)
          ·
            refine ⟨2689066491260199831955313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792710994173466554636875 2689066491260199831955313)
            ·
              refine ⟨2016799868445149873966485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689066491260199831955313 2016799868445149873966485)
              ·
                refine ⟨94537493833366400342179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2016799868445149873966485 94537493833366400342179)
                ·
                  rfl

theorem cell20_621375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_621375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621375 prefixEnd_621375 := by exact prefixLift 621375
  have htrace : WordTrace (prefixWord ++ tailWord_621375) baseStart_621375 baseEnd_621375 := by
    simpa [prefixWord, tailWord_621375, baseEnd_621375] using wordTrace_append hprefix tailTrace_621375
  have hstable : (prefixWord ++ tailWord_621375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621375).length < 2 ^ (prefixWord ++ tailWord_621375).sum := by decide
  have hdescent : baseEnd_621375 < baseStart_621375 := by decide
  rcases family_descends (prefixWord ++ tailWord_621375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621399 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 3]
def baseStart_621399 : Nat := 118140960795 + 621399 * 2 ^ 59
def prefixEnd_621399 : Nat := 4983230072969 + 3 ^ 40 * 621399 * 2
def baseEnd_621399 : Nat := 283623435754061784226439

theorem tailTrace_621399 : CollatzResearch.WordTrace tailWord_621399 prefixEnd_621399 283623435754061784226439 := by
  unfold tailWord_621399
  simp only [CollatzResearch.WordTrace]
  refine ⟨22664283475785024345147251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15109522317190016230098167 22664283475785024345147251)
  ·
    refine ⟨33996425213677536517720877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22664283475785024345147251 33996425213677536517720877)
    ·
      refine ⟨12748659455129076194145329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33996425213677536517720877 12748659455129076194145329)
      ·
        refine ⟨9561494591346807145608997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12748659455129076194145329 9561494591346807145608997)
        ·
          refine ⟨1792780235877526339801687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9561494591346807145608997 1792780235877526339801687)
          ·
            refine ⟨2689170353816289509702531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792780235877526339801687 2689170353816289509702531)
            ·
              refine ⟨4033755530724434264553797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689170353816289509702531 4033755530724434264553797)
              ·
                refine ⟨756329162010831424603837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4033755530724434264553797 756329162010831424603837)
                ·
                  refine ⟨283623435754061784226439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756329162010831424603837 283623435754061784226439)
                  ·
                    rfl

theorem cell20_621399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_621399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621399 prefixEnd_621399 := by exact prefixLift 621399
  have htrace : WordTrace (prefixWord ++ tailWord_621399) baseStart_621399 baseEnd_621399 := by
    simpa [prefixWord, tailWord_621399, baseEnd_621399] using wordTrace_append hprefix tailTrace_621399
  have hstable : (prefixWord ++ tailWord_621399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621399).length < 2 ^ (prefixWord ++ tailWord_621399).sum := by decide
  have hdescent : baseEnd_621399 < baseStart_621399 := by decide
  rcases family_descends (prefixWord ++ tailWord_621399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621402 : List Nat := [3, 1, 1, 2, 1, 4, 4, 2, 2]
def baseStart_621402 : Nat := 118140960795 + 621402 * 2 ^ 59
def prefixEnd_621402 : Nat := 4983230072969 + 3 ^ 40 * 621402 * 2
def baseEnd_621402 : Nat := 283624805035807107126427

theorem tailTrace_621402 : CollatzResearch.WordTrace tailWord_621402 prefixEnd_621402 283624805035807107126427 := by
  unfold tailWord_621402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5666098223693538964376615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15109595263182770571670973 5666098223693538964376615)
  ·
    refine ⟨8499147335540308446564923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5666098223693538964376615 8499147335540308446564923)
    ·
      refine ⟨12748721003310462669847385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8499147335540308446564923 12748721003310462669847385)
      ·
        refine ⟨9561540752482847002385539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12748721003310462669847385 9561540752482847002385539)
        ·
          refine ⟨14342311128724270503578309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9561540752482847002385539 14342311128724270503578309)
          ·
            refine ⟨2689183336635800719420933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14342311128724270503578309 2689183336635800719420933)
            ·
              refine ⟨504221875619212634891425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2689183336635800719420933 504221875619212634891425)
              ·
                refine ⟨378166406714409476168569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504221875619212634891425 378166406714409476168569)
                ·
                  refine ⟨283624805035807107126427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378166406714409476168569 283624805035807107126427)
                  ·
                    rfl

theorem cell20_621402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_621402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621402 prefixEnd_621402 := by exact prefixLift 621402
  have htrace : WordTrace (prefixWord ++ tailWord_621402) baseStart_621402 baseEnd_621402 := by
    simpa [prefixWord, tailWord_621402, baseEnd_621402] using wordTrace_append hprefix tailTrace_621402
  have hstable : (prefixWord ++ tailWord_621402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621402).length < 2 ^ (prefixWord ++ tailWord_621402).sum := by decide
  have hdescent : baseEnd_621402 < baseStart_621402 := by decide
  rcases family_descends (prefixWord ++ tailWord_621402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621413 : List Nat := [1, 3, 1, 3, 1, 1, 5, 5]
def baseStart_621413 : Nat := 118140960795 + 621413 * 2 ^ 59
def prefixEnd_621413 : Nat := 4983230072969 + 3 ^ 40 * 621413 * 2
def baseEnd_621413 : Nat := 94543275245179985919905

theorem tailTrace_621413 : CollatzResearch.WordTrace tailWord_621413 prefixEnd_621413 94543275245179985919905 := by
  unfold tailWord_621413
  simp only [CollatzResearch.WordTrace]
  refine ⟨22664794097734304736156893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15109862731822869824104595 22664794097734304736156893)
  ·
    refine ⟨8499297786650364276058835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22664794097734304736156893 8499297786650364276058835)
    ·
      refine ⟨12748946679975546414088253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8499297786650364276058835 12748946679975546414088253)
      ·
        refine ⟨4780855004990829905283095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12748946679975546414088253 4780855004990829905283095)
        ·
          refine ⟨7171282507486244857924643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780855004990829905283095 7171282507486244857924643)
          ·
            refine ⟨10756923761229367286886965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171282507486244857924643 10756923761229367286886965)
            ·
              refine ⟨1008461602615253183145653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10756923761229367286886965 1008461602615253183145653)
              ·
                refine ⟨94543275245179985919905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1008461602615253183145653 94543275245179985919905)
                ·
                  rfl

theorem cell20_621413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_621413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621413 prefixEnd_621413 := by exact prefixLift 621413
  have htrace : WordTrace (prefixWord ++ tailWord_621413) baseStart_621413 baseEnd_621413 := by
    simpa [prefixWord, tailWord_621413, baseEnd_621413] using wordTrace_append hprefix tailTrace_621413
  have hstable : (prefixWord ++ tailWord_621413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621413).length < 2 ^ (prefixWord ++ tailWord_621413).sum := by decide
  have hdescent : baseEnd_621413 < baseStart_621413 := by decide
  rcases family_descends (prefixWord ++ tailWord_621413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621427 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_621427 : Nat := 118140960795 + 621427 * 2 ^ 59
def prefixEnd_621427 : Nat := 4983230072969 + 3 ^ 40 * 621427 * 2
def baseEnd_621427 : Nat := 283636215717018131292991

theorem tailTrace_621427 : CollatzResearch.WordTrace tailWord_621427 prefixEnd_621427 283636215717018131292991 := by
  unfold tailWord_621427
  simp only [CollatzResearch.WordTrace]
  refine ⟨22665304719683585127166535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15110203146455723418111023 22665304719683585127166535)
  ·
    refine ⟨33997957079525377690749803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22665304719683585127166535 33997957079525377690749803)
    ·
      refine ⟨50996935619288066536124705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33997957079525377690749803 50996935619288066536124705)
      ·
        refine ⟨38247701714466049902093529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50996935619288066536124705 38247701714466049902093529)
        ·
          refine ⟨28685776285849537426570147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38247701714466049902093529 28685776285849537426570147)
          ·
            refine ⟨43028664428774306139855221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28685776285849537426570147 43028664428774306139855221)
            ·
              refine ⟨4033937290197591200611427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43028664428774306139855221 4033937290197591200611427)
              ·
                refine ⟨6050905935296386800917141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033937290197591200611427 6050905935296386800917141)
                ·
                  refine ⟨283636215717018131292991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6050905935296386800917141 283636215717018131292991)
                  ·
                    rfl

theorem cell20_621427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_621427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621427 prefixEnd_621427 := by exact prefixLift 621427
  have htrace : WordTrace (prefixWord ++ tailWord_621427) baseStart_621427 baseEnd_621427 := by
    simpa [prefixWord, tailWord_621427, baseEnd_621427] using wordTrace_append hprefix tailTrace_621427
  have hstable : (prefixWord ++ tailWord_621427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621427).length < 2 ^ (prefixWord ++ tailWord_621427).sum := by decide
  have hdescent : baseEnd_621427 < baseStart_621427 := by decide
  rcases family_descends (prefixWord ++ tailWord_621427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621461 : List Nat := [1, 3, 2, 1, 1, 4, 2, 4, 2]
def baseStart_621461 : Nat := 118140960795 + 621461 * 2 ^ 59
def prefixEnd_621461 : Nat := 4983230072969 + 3 ^ 40 * 621461 * 2
def baseEnd_621461 : Nat := 283651734243465124159519

theorem tailTrace_621461 : CollatzResearch.WordTrace tailWord_621461 prefixEnd_621461 283651734243465124159519 := by
  unfold tailWord_621461
  simp only [CollatzResearch.WordTrace]
  refine ⟨22666544801560408933904237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15111029867706939289269491 22666544801560408933904237)
  ·
    refine ⟨8499954300585153350214089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22666544801560408933904237 8499954300585153350214089)
    ·
      refine ⟨6374965725438865012660567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8499954300585153350214089 6374965725438865012660567)
      ·
        refine ⟨9562448588158297518990851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6374965725438865012660567 9562448588158297518990851)
        ·
          refine ⟨14343672882237446278486277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9562448588158297518990851 14343672882237446278486277)
          ·
            refine ⟨2689438665419521177216177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14343672882237446278486277 2689438665419521177216177)
            ·
              refine ⟨2017078999064640882912133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689438665419521177216177 2017078999064640882912133)
              ·
                refine ⟨378202312324620165546025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2017078999064640882912133 378202312324620165546025)
                ·
                  refine ⟨283651734243465124159519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378202312324620165546025 283651734243465124159519)
                  ·
                    rfl

theorem cell20_621461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_621461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621461 prefixEnd_621461 := by exact prefixLift 621461
  have htrace : WordTrace (prefixWord ++ tailWord_621461) baseStart_621461 baseEnd_621461 := by
    simpa [prefixWord, tailWord_621461, baseEnd_621461] using wordTrace_append hprefix tailTrace_621461
  have hstable : (prefixWord ++ tailWord_621461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621461).length < 2 ^ (prefixWord ++ tailWord_621461).sum := by decide
  have hdescent : baseEnd_621461 < baseStart_621461 := by decide
  rcases family_descends (prefixWord ++ tailWord_621461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621485 : List Nat := [1, 5, 2, 3, 1, 1, 1, 6]
def baseStart_621485 : Nat := 118140960795 + 621485 * 2 ^ 59
def prefixEnd_621485 : Nat := 4983230072969 + 3 ^ 40 * 621485 * 2
def baseEnd_621485 : Nat := 94554229499142569119807

theorem tailTrace_621485 : CollatzResearch.WordTrace tailWord_621485 prefixEnd_621485 94554229499142569119807 := by
  unfold tailWord_621485
  simp only [CollatzResearch.WordTrace]
  refine ⟨22667420153473461032777909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15111613435648974021851939 22667420153473461032777909)
  ·
    refine ⟨2125070639388136971822929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22667420153473461032777909 2125070639388136971822929)
    ·
      refine ⟨1593802979541102728867197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2125070639388136971822929 1593802979541102728867197)
      ·
        refine ⟨597676117327913523325199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1593802979541102728867197 597676117327913523325199)
        ·
          refine ⟨896514175991870284987799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597676117327913523325199 896514175991870284987799)
          ·
            refine ⟨1344771263987805427481699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896514175991870284987799 1344771263987805427481699)
            ·
              refine ⟨2017156895981708141222549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344771263987805427481699 2017156895981708141222549)
              ·
                refine ⟨94554229499142569119807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2017156895981708141222549 94554229499142569119807)
                ·
                  rfl

theorem cell20_621485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 6].length) (baseStart_621485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621485 prefixEnd_621485 := by exact prefixLift 621485
  have htrace : WordTrace (prefixWord ++ tailWord_621485) baseStart_621485 baseEnd_621485 := by
    simpa [prefixWord, tailWord_621485, baseEnd_621485] using wordTrace_append hprefix tailTrace_621485
  have hstable : (prefixWord ++ tailWord_621485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621485).length < 2 ^ (prefixWord ++ tailWord_621485).sum := by decide
  have hdescent : baseEnd_621485 < baseStart_621485 := by decide
  rcases family_descends (prefixWord ++ tailWord_621485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621492 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_621492 : Nat := 118140960795 + 621492 * 2 ^ 59
def prefixEnd_621492 : Nat := 4983230072969 + 3 ^ 40 * 621492 * 2
def baseEnd_621492 : Nat := 283665883488166794126059

theorem tailTrace_621492 : CollatzResearch.WordTrace tailWord_621492 prefixEnd_621492 283665883488166794126059 := by
  unfold tailWord_621492
  simp only [CollatzResearch.WordTrace]
  refine ⟨11333837732224050614141365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15111783642965400818855153 11333837732224050614141365)
  ·
    refine ⟨1062547287396004745075753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11333837732224050614141365 1062547287396004745075753)
    ·
      refine ⟨796910465547003558806815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1062547287396004745075753 796910465547003558806815)
      ·
        refine ⟨1195365698320505338210223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796910465547003558806815 1195365698320505338210223)
        ·
          refine ⟨1793048547480758007315335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195365698320505338210223 1793048547480758007315335)
          ·
            refine ⟨2689572821221137010973003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793048547480758007315335 2689572821221137010973003)
            ·
              refine ⟨4034359231831705516459505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689572821221137010973003 4034359231831705516459505)
              ·
                refine ⟨3025769423873779137344629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4034359231831705516459505 3025769423873779137344629)
                ·
                  refine ⟨283665883488166794126059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3025769423873779137344629 283665883488166794126059)
                  ·
                    rfl

theorem cell20_621492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_621492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621492 prefixEnd_621492 := by exact prefixLift 621492
  have htrace : WordTrace (prefixWord ++ tailWord_621492) baseStart_621492 baseEnd_621492 := by
    simpa [prefixWord, tailWord_621492, baseEnd_621492] using wordTrace_append hprefix tailTrace_621492
  have hstable : (prefixWord ++ tailWord_621492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621492).length < 2 ^ (prefixWord ++ tailWord_621492).sum := by decide
  have hdescent : baseEnd_621492 < baseStart_621492 := by decide
  rcases family_descends (prefixWord ++ tailWord_621492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621496 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_621496 : Nat := 118140960795 + 621496 * 2 ^ 59
def prefixEnd_621496 : Nat := 4983230072969 + 3 ^ 40 * 621496 * 2
def baseEnd_621496 : Nat := 283667709197160557992709

theorem tailTrace_621496 : CollatzResearch.WordTrace tailWord_621496 prefixEnd_621496 283667709197160557992709 := by
  unfold tailWord_621496
  simp only [CollatzResearch.WordTrace]
  refine ⟨11333910678216804955714171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15111880904289073274285561 11333910678216804955714171)
  ·
    refine ⟨17000866017325207433571257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11333910678216804955714171 17000866017325207433571257)
    ·
      refine ⟨12750649512993905575178443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17000866017325207433571257 12750649512993905575178443)
      ·
        refine ⟨19125974269490858362767665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12750649512993905575178443 19125974269490858362767665)
        ·
          refine ⟨14344480702118143772075749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19125974269490858362767665 14344480702118143772075749)
          ·
            refine ⟨2689590131647151957264203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14344480702118143772075749 2689590131647151957264203)
            ·
              refine ⟨4034385197470727935896305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689590131647151957264203 4034385197470727935896305)
              ·
                refine ⟨3025788898103045951922229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4034385197470727935896305 3025788898103045951922229)
                ·
                  refine ⟨283667709197160557992709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3025788898103045951922229 283667709197160557992709)
                  ·
                    rfl

theorem cell20_621496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_621496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621496 prefixEnd_621496 := by exact prefixLift 621496
  have htrace : WordTrace (prefixWord ++ tailWord_621496) baseStart_621496 baseEnd_621496 := by
    simpa [prefixWord, tailWord_621496, baseEnd_621496] using wordTrace_append hprefix tailTrace_621496
  have hstable : (prefixWord ++ tailWord_621496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621496).length < 2 ^ (prefixWord ++ tailWord_621496).sum := by decide
  have hdescent : baseEnd_621496 < baseStart_621496 := by decide
  rcases family_descends (prefixWord ++ tailWord_621496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621516 : List Nat := [2, 2, 1, 4, 1, 1, 5, 2, 2]
def baseStart_621516 : Nat := 118140960795 + 621516 * 2 ^ 59
def prefixEnd_621516 : Nat := 4983230072969 + 3 ^ 40 * 621516 * 2
def baseEnd_621516 : Nat := 283676837742129377325961

theorem tailTrace_621516 : CollatzResearch.WordTrace tailWord_621516 prefixEnd_621516 283676837742129377325961 := by
  unfold tailWord_621516
  simp only [CollatzResearch.WordTrace]
  refine ⟨11334275408180576663578201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15112367210907435551437601 11334275408180576663578201)
  ·
    refine ⟨8500706556135432497683651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11334275408180576663578201 8500706556135432497683651)
    ·
      refine ⟨12751059834203148746525477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8500706556135432497683651 12751059834203148746525477)
      ·
        refine ⟨2390823718913090389973527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12751059834203148746525477 2390823718913090389973527)
        ·
          refine ⟨3586235578369635584960291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390823718913090389973527 3586235578369635584960291)
          ·
            refine ⟨5379353367554453377440437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586235578369635584960291 5379353367554453377440437)
            ·
              refine ⟨504314378208230004135041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5379353367554453377440437 504314378208230004135041)
              ·
                refine ⟨378235783656172503101281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504314378208230004135041 378235783656172503101281)
                ·
                  refine ⟨283676837742129377325961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378235783656172503101281 283676837742129377325961)
                  ·
                    rfl

theorem cell20_621516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 2].length) (baseStart_621516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621516 prefixEnd_621516 := by exact prefixLift 621516
  have htrace : WordTrace (prefixWord ++ tailWord_621516) baseStart_621516 baseEnd_621516 := by
    simpa [prefixWord, tailWord_621516, baseEnd_621516] using wordTrace_append hprefix tailTrace_621516
  have hstable : (prefixWord ++ tailWord_621516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621516).length < 2 ^ (prefixWord ++ tailWord_621516).sum := by decide
  have hdescent : baseEnd_621516 < baseStart_621516 := by decide
  rcases family_descends (prefixWord ++ tailWord_621516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621526 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_621526 : Nat := 118140960795 + 621526 * 2 ^ 59
def prefixEnd_621526 : Nat := 4983230072969 + 3 ^ 40 * 621526 * 2
def baseEnd_621526 : Nat := 283681402014613786992587

theorem tailTrace_621526 : CollatzResearch.WordTrace tailWord_621526 prefixEnd_621526 283681402014613786992587 := by
  unfold tailWord_621526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416807221645307814688777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15112610364216616690013621 1416807221645307814688777)
  ·
    refine ⟨1062605416233980861016583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1416807221645307814688777 1062605416233980861016583)
    ·
      refine ⟨1593908124350971291524875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062605416233980861016583 1593908124350971291524875)
      ·
        refine ⟨2390862186526456937287313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593908124350971291524875 2390862186526456937287313)
        ·
          refine ⟨1793146639894842702965485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2390862186526456937287313 1793146639894842702965485)
          ·
            refine ⟨672429989960566013612057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1793146639894842702965485 672429989960566013612057)
            ·
              refine ⟨504322492470424510209043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672429989960566013612057 504322492470424510209043)
              ·
                refine ⟨756483738705636765313565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504322492470424510209043 756483738705636765313565)
                ·
                  refine ⟨283681402014613786992587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756483738705636765313565 283681402014613786992587)
                  ·
                    rfl

theorem cell20_621526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_621526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621526 prefixEnd_621526 := by exact prefixLift 621526
  have htrace : WordTrace (prefixWord ++ tailWord_621526) baseStart_621526 baseEnd_621526 := by
    simpa [prefixWord, tailWord_621526, baseEnd_621526] using wordTrace_append hprefix tailTrace_621526
  have hstable : (prefixWord ++ tailWord_621526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621526).length < 2 ^ (prefixWord ++ tailWord_621526).sum := by decide
  have hdescent : baseEnd_621526 < baseStart_621526 := by decide
  rcases family_descends (prefixWord ++ tailWord_621526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621530 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_621530 : Nat := 118140960795 + 621530 * 2 ^ 59
def prefixEnd_621530 : Nat := 4983230072969 + 3 ^ 40 * 621530 * 2
def baseEnd_621530 : Nat := 283683227723607550859237

theorem tailTrace_621530 : CollatzResearch.WordTrace tailWord_621530 prefixEnd_621530 283683227723607550859237 := by
  unfold tailWord_621530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5667265359577608429541511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15112707625540289145444029 5667265359577608429541511)
  ·
    refine ⟨8500898039366412644312267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5667265359577608429541511 8500898039366412644312267)
    ·
      refine ⟨12751347059049618966468401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8500898039366412644312267 12751347059049618966468401)
      ·
        refine ⟨9563510294287214224851301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12751347059049618966468401 9563510294287214224851301)
        ·
          refine ⟨1793158180178852667159619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9563510294287214224851301 1793158180178852667159619)
          ·
            refine ⟨2689737270268279000739429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793158180178852667159619 2689737270268279000739429)
            ·
              refine ⟨504325738175302312638643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2689737270268279000739429 504325738175302312638643)
              ·
                refine ⟨756488607262953468957965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504325738175302312638643 756488607262953468957965)
                ·
                  refine ⟨283683227723607550859237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756488607262953468957965 283683227723607550859237)
                  ·
                    rfl

theorem cell20_621530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_621530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621530 prefixEnd_621530 := by exact prefixLift 621530
  have htrace : WordTrace (prefixWord ++ tailWord_621530) baseStart_621530 baseEnd_621530 := by
    simpa [prefixWord, tailWord_621530, baseEnd_621530] using wordTrace_append hprefix tailTrace_621530
  have hstable : (prefixWord ++ tailWord_621530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621530).length < 2 ^ (prefixWord ++ tailWord_621530).sum := by decide
  have hdescent : baseEnd_621530 < baseStart_621530 := by decide
  rcases family_descends (prefixWord ++ tailWord_621530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621575 : List Nat := [1, 1, 4, 3, 1, 1, 3, 4, 2]
def baseStart_621575 : Nat := 118140960795 + 621575 * 2 ^ 59
def prefixEnd_621575 : Nat := 4983230072969 + 3 ^ 40 * 621575 * 2
def baseEnd_621575 : Nat := 283703766949787394359053

theorem tailTrace_621575 : CollatzResearch.WordTrace tailWord_621575 prefixEnd_621575 283703766949787394359053 := by
  unfold tailWord_621575
  simp only [CollatzResearch.WordTrace]
  refine ⟨22670702723147406403554179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15113801815431604269036119 22670702723147406403554179)
  ·
    refine ⟨34006054084721109605331269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22670702723147406403554179 34006054084721109605331269)
    ·
      refine ⟨6376135140885208050999613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34006054084721109605331269 6376135140885208050999613)
      ·
        refine ⟨2391050677831953019124855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6376135140885208050999613 2391050677831953019124855)
        ·
          refine ⟨3586576016747929528687283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391050677831953019124855 3586576016747929528687283)
          ·
            refine ⟨5379864025121894293030925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586576016747929528687283 5379864025121894293030925)
            ·
              refine ⟨2017449009420710359886597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5379864025121894293030925 2017449009420710359886597)
              ·
                refine ⟨378271689266383192478737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2017449009420710359886597 378271689266383192478737)
                ·
                  refine ⟨283703766949787394359053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378271689266383192478737 283703766949787394359053)
                  ·
                    rfl

theorem cell20_621575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 2].length) (baseStart_621575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621575 prefixEnd_621575 := by exact prefixLift 621575
  have htrace : WordTrace (prefixWord ++ tailWord_621575) baseStart_621575 baseEnd_621575 := by
    simpa [prefixWord, tailWord_621575, baseEnd_621575] using wordTrace_append hprefix tailTrace_621575
  have hstable : (prefixWord ++ tailWord_621575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621575).length < 2 ^ (prefixWord ++ tailWord_621575).sum := by decide
  have hdescent : baseEnd_621575 < baseStart_621575 := by decide
  rcases family_descends (prefixWord ++ tailWord_621575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621582 : List Nat := [4, 1, 1, 2, 2, 4, 1, 5]
def baseStart_621582 : Nat := 118140960795 + 621582 * 2 ^ 59
def prefixEnd_621582 : Nat := 4983230072969 + 3 ^ 40 * 621582 * 2
def baseEnd_621582 : Nat := 94568987313508827041897

theorem tailTrace_621582 : CollatzResearch.WordTrace tailWord_621582 prefixEnd_621582 94568987313508827041897 := by
  unfold tailWord_621582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833869754265255824882375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15113972022748031066039333 2833869754265255824882375)
  ·
    refine ⟨4250804631397883737323563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2833869754265255824882375 4250804631397883737323563)
    ·
      refine ⟨6376206947096825605985345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4250804631397883737323563 6376206947096825605985345)
      ·
        refine ⟨4782155210322619204489009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6376206947096825605985345 4782155210322619204489009)
        ·
          refine ⟨3586616407741964403366757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4782155210322619204489009 3586616407741964403366757)
          ·
            refine ⟨672490576451618325631267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3586616407741964403366757 672490576451618325631267)
            ·
              refine ⟨1008735864677427488446901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672490576451618325631267 1008735864677427488446901)
              ·
                refine ⟨94568987313508827041897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1008735864677427488446901 94568987313508827041897)
                ·
                  rfl

theorem cell20_621582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_621582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621582 prefixEnd_621582 := by exact prefixLift 621582
  have htrace : WordTrace (prefixWord ++ tailWord_621582) baseStart_621582 baseEnd_621582 := by
    simpa [prefixWord, tailWord_621582, baseEnd_621582] using wordTrace_append hprefix tailTrace_621582
  have hstable : (prefixWord ++ tailWord_621582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621582).length < 2 ^ (prefixWord ++ tailWord_621582).sum := by decide
  have hdescent : baseEnd_621582 < baseStart_621582 := by decide
  rcases family_descends (prefixWord ++ tailWord_621582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621589 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 3]
def baseStart_621589 : Nat := 118140960795 + 621589 * 2 ^ 59
def prefixEnd_621589 : Nat := 4983230072969 + 3 ^ 40 * 621589 * 2
def baseEnd_621589 : Nat := 283710156931265567892329

theorem tailTrace_621589 : CollatzResearch.WordTrace tailWord_621589 prefixEnd_621589 283710156931265567892329 := by
  unfold tailWord_621589
  simp only [CollatzResearch.WordTrace]
  refine ⟨22671213345096686794563821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15114142230064457863042547 22671213345096686794563821)
  ·
    refine ⟨8501705004411257547961433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22671213345096686794563821 8501705004411257547961433)
    ·
      refine ⟨6376278753308443160971075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8501705004411257547961433 6376278753308443160971075)
      ·
        refine ⟨9564418129962664741456613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6376278753308443160971075 9564418129962664741456613)
        ·
          refine ⟨1793328399367999639023115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9564418129962664741456613 1793328399367999639023115)
          ·
            refine ⟨2689992599051999458534673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793328399367999639023115 2689992599051999458534673)
            ·
              refine ⟨2017494449288999593901005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689992599051999458534673 2017494449288999593901005)
              ·
                refine ⟨756560418483374847712877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2017494449288999593901005 756560418483374847712877)
                ·
                  refine ⟨283710156931265567892329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756560418483374847712877 283710156931265567892329)
                  ·
                    rfl

theorem cell20_621589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_621589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621589 prefixEnd_621589 := by exact prefixLift 621589
  have htrace : WordTrace (prefixWord ++ tailWord_621589) baseStart_621589 baseEnd_621589 := by
    simpa [prefixWord, tailWord_621589, baseEnd_621589] using wordTrace_append hprefix tailTrace_621589
  have hstable : (prefixWord ++ tailWord_621589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621589).length < 2 ^ (prefixWord ++ tailWord_621589).sum := by decide
  have hdescent : baseEnd_621589 < baseStart_621589 := by decide
  rcases family_descends (prefixWord ++ tailWord_621589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621617 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_621617 : Nat := 118140960795 + 621617 * 2 ^ 59
def prefixEnd_621617 : Nat := 4983230072969 + 3 ^ 40 * 621617 * 2
def baseEnd_621617 : Nat := 283722936894221914958881

theorem tailTrace_621617 : CollatzResearch.WordTrace tailWord_621617 prefixEnd_621617 283722936894221914958881 := by
  unfold tailWord_621617
  simp only [CollatzResearch.WordTrace]
  refine ⟨22672234588995247576583105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15114823059330165051055403 22672234588995247576583105)
  ·
    refine ⟨17004175941746435682437329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22672234588995247576583105 17004175941746435682437329)
    ·
      refine ⟨12753131956309826761827997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17004175941746435682437329 12753131956309826761827997)
      ·
        refine ⟨4782424483616185035685499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12753131956309826761827997 4782424483616185035685499)
        ·
          refine ⟨7173636725424277553528249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782424483616185035685499 7173636725424277553528249)
          ·
            refine ⟨5380227544068208165146187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7173636725424277553528249 5380227544068208165146187)
            ·
              refine ⟨8070341316102312247719281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5380227544068208165146187 8070341316102312247719281)
              ·
                refine ⟨6052755987076734185789461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8070341316102312247719281 6052755987076734185789461)
                ·
                  refine ⟨283722936894221914958881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6052755987076734185789461 283722936894221914958881)
                  ·
                    rfl

theorem cell20_621617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_621617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621617 prefixEnd_621617 := by exact prefixLift 621617
  have htrace : WordTrace (prefixWord ++ tailWord_621617) baseStart_621617 baseEnd_621617 := by
    simpa [prefixWord, tailWord_621617, baseEnd_621617] using wordTrace_append hprefix tailTrace_621617
  have hstable : (prefixWord ++ tailWord_621617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621617).length < 2 ^ (prefixWord ++ tailWord_621617).sum := by decide
  have hdescent : baseEnd_621617 < baseStart_621617 := by decide
  rcases family_descends (prefixWord ++ tailWord_621617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621620 : List Nat := [2, 5, 1, 2, 1, 2, 7]
def baseStart_621620 : Nat := 118140960795 + 621620 * 2 ^ 59
def prefixEnd_621620 : Nat := 4983230072969 + 3 ^ 40 * 621620 * 2
def baseEnd_621620 : Nat := 31524922908440804206541

theorem tailTrace_621620 : CollatzResearch.WordTrace tailWord_621620 prefixEnd_621620 31524922908440804206541 := by
  unfold tailWord_621620
  simp only [CollatzResearch.WordTrace]
  refine ⟨11336172003992189544471157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15114896005322919392628209 11336172003992189544471157)
  ·
    refine ⟨1062766125374267769794171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11336172003992189544471157 1062766125374267769794171)
    ·
      refine ⟨1594149188061401654691257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062766125374267769794171 1594149188061401654691257)
      ·
        refine ⟨1195611891046051241018443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1594149188061401654691257 1195611891046051241018443)
        ·
          refine ⟨1793417836569076861527665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195611891046051241018443 1793417836569076861527665)
          ·
            refine ⟨1345063377426807646145749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1793417836569076861527665 1345063377426807646145749)
            ·
              refine ⟨31524922908440804206541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1345063377426807646145749 31524922908440804206541)
              ·
                rfl

theorem cell20_621620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 7].length) (baseStart_621620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621620 prefixEnd_621620 := by exact prefixLift 621620
  have htrace : WordTrace (prefixWord ++ tailWord_621620) baseStart_621620 baseEnd_621620 := by
    simpa [prefixWord, tailWord_621620, baseEnd_621620] using wordTrace_append hprefix tailTrace_621620
  have hstable : (prefixWord ++ tailWord_621620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621620).length < 2 ^ (prefixWord ++ tailWord_621620).sum := by decide
  have hdescent : baseEnd_621620 < baseStart_621620 := by decide
  rcases family_descends (prefixWord ++ tailWord_621620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621630 : List Nat := [4, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_621630 : Nat := 118140960795 + 621630 * 2 ^ 59
def prefixEnd_621630 : Nat := 4983230072969 + 3 ^ 40 * 621630 * 2
def baseEnd_621630 : Nat := 283728870448451647525495

theorem tailTrace_621630 : CollatzResearch.WordTrace tailWord_621630 prefixEnd_621630 283728870448451647525495 := by
  unfold tailWord_621630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834088592243518849600793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15115139158632100531204229 2834088592243518849600793)
  ·
    refine ⟨2125566444182639137200595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2834088592243518849600793 2125566444182639137200595)
    ·
      refine ⟨3188349666273958705800893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2125566444182639137200595 3188349666273958705800893)
      ·
        refine ⟨1195631124852734514675335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3188349666273958705800893 1195631124852734514675335)
        ·
          refine ⟨1793446687279101772013003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195631124852734514675335 1793446687279101772013003)
          ·
            refine ⟨2690170030918652658019505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793446687279101772013003 2690170030918652658019505)
            ·
              refine ⟨2017627523188989493514629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2690170030918652658019505 2017627523188989493514629)
              ·
                refine ⟨378305160597935530033993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2017627523188989493514629 378305160597935530033993)
                ·
                  refine ⟨283728870448451647525495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378305160597935530033993 283728870448451647525495)
                  ·
                    rfl

theorem cell20_621630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_621630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621630 prefixEnd_621630 := by exact prefixLift 621630
  have htrace : WordTrace (prefixWord ++ tailWord_621630) baseStart_621630 baseEnd_621630 := by
    simpa [prefixWord, tailWord_621630, baseEnd_621630] using wordTrace_append hprefix tailTrace_621630
  have hstable : (prefixWord ++ tailWord_621630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621630).length < 2 ^ (prefixWord ++ tailWord_621630).sum := by decide
  have hdescent : baseEnd_621630 < baseStart_621630 := by decide
  rcases family_descends (prefixWord ++ tailWord_621630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621648 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_621648 : Nat := 118140960795 + 621648 * 2 ^ 59
def prefixEnd_621648 : Nat := 4983230072969 + 3 ^ 40 * 621648 * 2
def baseEnd_621648 : Nat := 283737086138923584925421

theorem tailTrace_621648 : CollatzResearch.WordTrace tailWord_621648 prefixEnd_621648 283737086138923584925421 := by
  unfold tailWord_621648
  simp only [CollatzResearch.WordTrace]
  refine ⟨11336682625941469935480799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15115576834588626580641065 11336682625941469935480799)
  ·
    refine ⟨17005023938912204903221199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11336682625941469935480799 17005023938912204903221199)
    ·
      refine ⟨25507535908368307354831799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17005023938912204903221199 25507535908368307354831799)
      ·
        refine ⟨38261303862552461032247699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25507535908368307354831799 38261303862552461032247699)
        ·
          refine ⟨57391955793828691548371549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38261303862552461032247699 57391955793828691548371549)
          ·
            refine ⟨21521983422685759330639331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57391955793828691548371549 21521983422685759330639331)
            ·
              refine ⟨32282975134028638995958997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21521983422685759330639331 32282975134028638995958997)
              ·
                refine ⟨756632229703796226467789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32282975134028638995958997 756632229703796226467789)
                ·
                  refine ⟨283737086138923584925421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756632229703796226467789 283737086138923584925421)
                  ·
                    rfl

theorem cell20_621648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_621648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621648 prefixEnd_621648 := by exact prefixLift 621648
  have htrace : WordTrace (prefixWord ++ tailWord_621648) baseStart_621648 baseEnd_621648 := by
    simpa [prefixWord, tailWord_621648, baseEnd_621648] using wordTrace_append hprefix tailTrace_621648
  have hstable : (prefixWord ++ tailWord_621648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621648).length < 2 ^ (prefixWord ++ tailWord_621648).sum := by decide
  have hdescent : baseEnd_621648 < baseStart_621648 := by decide
  rcases family_descends (prefixWord ++ tailWord_621648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621685 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 4]
def baseStart_621685 : Nat := 118140960795 + 621685 * 2 ^ 59
def prefixEnd_621685 : Nat := 4983230072969 + 3 ^ 40 * 621685 * 2
def baseEnd_621685 : Nat := 283753973947115900691937

theorem tailTrace_621685 : CollatzResearch.WordTrace tailWord_621685 prefixEnd_621685 283753973947115900691937 := by
  unfold tailWord_621685
  simp only [CollatzResearch.WordTrace]
  refine ⟨22674714752748895190058509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15116476501832596793372339 22674714752748895190058509)
  ·
    refine ⟨8503018032280835696271941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22674714752748895190058509 8503018032280835696271941)
    ·
      refine ⟨1594315881052656693050989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8503018032280835696271941 1594315881052656693050989)
      ·
        refine ⟨597868455394746259894121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1594315881052656693050989 597868455394746259894121)
        ·
          refine ⟨448401341546059694920591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597868455394746259894121 448401341546059694920591)
          ·
            refine ⟨672602012319089542380887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448401341546059694920591 672602012319089542380887)
            ·
              refine ⟨1008903018478634313571331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672602012319089542380887 1008903018478634313571331)
              ·
                refine ⟨1513354527717951470356997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008903018478634313571331 1513354527717951470356997)
                ·
                  refine ⟨283753973947115900691937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1513354527717951470356997 283753973947115900691937)
                  ·
                    rfl

theorem cell20_621685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_621685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621685 prefixEnd_621685 := by exact prefixLift 621685
  have htrace : WordTrace (prefixWord ++ tailWord_621685) baseStart_621685 baseEnd_621685 := by
    simpa [prefixWord, tailWord_621685, baseEnd_621685] using wordTrace_append hprefix tailTrace_621685
  have hstable : (prefixWord ++ tailWord_621685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621685).length < 2 ^ (prefixWord ++ tailWord_621685).sum := by decide
  have hdescent : baseEnd_621685 < baseStart_621685 := by decide
  rcases family_descends (prefixWord ++ tailWord_621685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621689 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 4]
def baseStart_621689 : Nat := 118140960795 + 621689 * 2 ^ 59
def prefixEnd_621689 : Nat := 4983230072969 + 3 ^ 40 * 621689 * 2
def baseEnd_621689 : Nat := 283755799656109664558587

theorem tailTrace_621689 : CollatzResearch.WordTrace tailWord_621689 prefixEnd_621689 283755799656109664558587 := by
  unfold tailWord_621689
  simp only [CollatzResearch.WordTrace]
  refine ⟨22674860644734403873204121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15116573763156269248802747 22674860644734403873204121)
  ·
    refine ⟨17006145483550802904903091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22674860644734403873204121 17006145483550802904903091)
    ·
      refine ⟨25509218225326204357354637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17006145483550802904903091 25509218225326204357354637)
      ·
        refine ⟨9565956834497326634007989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25509218225326204357354637 9565956834497326634007989)
        ·
          refine ⟨896808453234124371938249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9565956834497326634007989 896808453234124371938249)
          ·
            refine ⟨672606339925593278953687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 896808453234124371938249 672606339925593278953687)
            ·
              refine ⟨1008909509888389918430531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672606339925593278953687 1008909509888389918430531)
              ·
                refine ⟨1513364264832584877645797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008909509888389918430531 1513364264832584877645797)
                ·
                  refine ⟨283755799656109664558587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1513364264832584877645797 283755799656109664558587)
                  ·
                    rfl

theorem cell20_621689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_621689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621689 prefixEnd_621689 := by exact prefixLift 621689
  have htrace : WordTrace (prefixWord ++ tailWord_621689) baseStart_621689 baseEnd_621689 := by
    simpa [prefixWord, tailWord_621689, baseEnd_621689] using wordTrace_append hprefix tailTrace_621689
  have hstable : (prefixWord ++ tailWord_621689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621689).length < 2 ^ (prefixWord ++ tailWord_621689).sum := by decide
  have hdescent : baseEnd_621689 < baseStart_621689 := by decide
  rcases family_descends (prefixWord ++ tailWord_621689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621800 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_621800 : Nat := 118140960795 + 621800 * 2 ^ 59
def prefixEnd_621800 : Nat := 4983230072969 + 3 ^ 40 * 621800 * 2
def baseEnd_621800 : Nat := 283806463080686611858133

theorem tailTrace_621800 : CollatzResearch.WordTrace tailWord_621800 prefixEnd_621800 283806463080686611858133 := by
  unfold tailWord_621800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11339454573666134915247427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15119272764888179886996569 11339454573666134915247427)
  ·
    refine ⟨17009181860499202372871141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11339454573666134915247427 17009181860499202372871141)
    ·
      refine ⟨3189221598843600444913339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17009181860499202372871141 3189221598843600444913339)
      ·
        refine ⟨4783832398265400667370009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189221598843600444913339 4783832398265400667370009)
        ·
          refine ⟨3587874298699050500527507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4783832398265400667370009 3587874298699050500527507)
          ·
            refine ⟨5381811448048575750791261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3587874298699050500527507 5381811448048575750791261)
            ·
              refine ⟨2018179293018215906546723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5381811448048575750791261 2018179293018215906546723)
              ·
                refine ⟨3027268939527323859820085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018179293018215906546723 3027268939527323859820085)
                ·
                  refine ⟨283806463080686611858133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3027268939527323859820085 283806463080686611858133)
                  ·
                    rfl

theorem cell20_621800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_621800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621800 prefixEnd_621800 := by exact prefixLift 621800
  have htrace : WordTrace (prefixWord ++ tailWord_621800) baseStart_621800 baseEnd_621800 := by
    simpa [prefixWord, tailWord_621800, baseEnd_621800] using wordTrace_append hprefix tailTrace_621800
  have hstable : (prefixWord ++ tailWord_621800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621800).length < 2 ^ (prefixWord ++ tailWord_621800).sum := by decide
  have hdescent : baseEnd_621800 < baseStart_621800 := by decide
  rcases family_descends (prefixWord ++ tailWord_621800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621817 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 3]
def baseStart_621817 : Nat := 118140960795 + 621817 * 2 ^ 59
def prefixEnd_621817 : Nat := 4983230072969 + 3 ^ 40 * 621817 * 2
def baseEnd_621817 : Nat := 283814222343910108291397

theorem tailTrace_621817 : CollatzResearch.WordTrace tailWord_621817 prefixEnd_621817 283814222343910108291397 := by
  unfold tailWord_621817
  simp only [CollatzResearch.WordTrace]
  refine ⟨22679529188270681733863705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15119686125513787822575803 22679529188270681733863705)
  ·
    refine ⟨17009646891203011300397779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22679529188270681733863705 17009646891203011300397779)
    ·
      refine ⟨25514470336804516950596669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17009646891203011300397779 25514470336804516950596669)
      ·
        refine ⟨9567926376301693856473751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25514470336804516950596669 9567926376301693856473751)
        ·
          refine ⟨14351889564452540784710627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9567926376301693856473751 14351889564452540784710627)
          ·
            refine ⟨21527834346678811177065941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14351889564452540784710627 21527834346678811177065941)
            ·
              refine ⟨504558617500284636962483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21527834346678811177065941 504558617500284636962483)
              ·
                refine ⟨756837926250426955443725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504558617500284636962483 756837926250426955443725)
                ·
                  refine ⟨283814222343910108291397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756837926250426955443725 283814222343910108291397)
                  ·
                    rfl

theorem cell20_621817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_621817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621817 prefixEnd_621817 := by exact prefixLift 621817
  have htrace : WordTrace (prefixWord ++ tailWord_621817) baseStart_621817 baseEnd_621817 := by
    simpa [prefixWord, tailWord_621817, baseEnd_621817] using wordTrace_append hprefix tailTrace_621817
  have hstable : (prefixWord ++ tailWord_621817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621817).length < 2 ^ (prefixWord ++ tailWord_621817).sum := by decide
  have hdescent : baseEnd_621817 < baseStart_621817 := by decide
  rcases family_descends (prefixWord ++ tailWord_621817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621838 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_621838 : Nat := 118140960795 + 621838 * 2 ^ 59
def prefixEnd_621838 : Nat := 4983230072969 + 3 ^ 40 * 621838 * 2
def baseEnd_621838 : Nat := 283823807316127368591311

theorem tailTrace_621838 : CollatzResearch.WordTrace tailWord_621838 prefixEnd_621838 283823807316127368591311 := by
  unfold tailWord_621838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835036890149325290047271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15120196747463068213585445 2835036890149325290047271)
  ·
    refine ⟨4252555335223987935070907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2835036890149325290047271 4252555335223987935070907)
    ·
      refine ⟨6378833002835981902606361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4252555335223987935070907 6378833002835981902606361)
      ·
        refine ⟨4784124752126986426954771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6378833002835981902606361 4784124752126986426954771)
        ·
          refine ⟨7176187128190479640432157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4784124752126986426954771 7176187128190479640432157)
          ·
            refine ⟨2691070173071429865162059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7176187128190479640432157 2691070173071429865162059)
            ·
              refine ⟨4036605259607144797743089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691070173071429865162059 4036605259607144797743089)
              ·
                refine ⟨3027453944705358598307317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4036605259607144797743089 3027453944705358598307317)
                ·
                  refine ⟨283823807316127368591311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3027453944705358598307317 283823807316127368591311)
                  ·
                    rfl

theorem cell20_621838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_621838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621838 prefixEnd_621838 := by exact prefixLift 621838
  have htrace : WordTrace (prefixWord ++ tailWord_621838) baseStart_621838 baseEnd_621838 := by
    simpa [prefixWord, tailWord_621838, baseEnd_621838] using wordTrace_append hprefix tailTrace_621838
  have hstable : (prefixWord ++ tailWord_621838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621838).length < 2 ^ (prefixWord ++ tailWord_621838).sum := by decide
  have hdescent : baseEnd_621838 < baseStart_621838 := by decide
  rcases family_descends (prefixWord ++ tailWord_621838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621852 : List Nat := [2, 2, 3, 1, 1, 1, 10]
def baseStart_621852 : Nat := 118140960795 + 621852 * 2 ^ 59
def prefixEnd_621852 : Nat := 4983230072969 + 3 ^ 40 * 621852 * 2
def baseEnd_621852 : Nat := 31536688588622838013843

theorem tailTrace_621852 : CollatzResearch.WordTrace tailWord_621852 prefixEnd_621852 31536688588622838013843 := by
  unfold tailWord_621852
  simp only [CollatzResearch.WordTrace]
  refine ⟨11340402871571941355693905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15120537162095921807591873 11340402871571941355693905)
  ·
    refine ⟨8505302153678956016770429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11340402871571941355693905 8505302153678956016770429)
    ·
      refine ⟨3189488307629608506288911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8505302153678956016770429 3189488307629608506288911)
      ·
        refine ⟨4784232461444412759433367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189488307629608506288911 4784232461444412759433367)
        ·
          refine ⟨7176348692166619139150051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4784232461444412759433367 7176348692166619139150051)
          ·
            refine ⟨10764523038249928708725077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7176348692166619139150051 10764523038249928708725077)
            ·
              refine ⟨31536688588622838013843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10764523038249928708725077 31536688588622838013843)
              ·
                rfl

theorem cell20_621852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 10].length) (baseStart_621852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621852 prefixEnd_621852 := by exact prefixLift 621852
  have htrace : WordTrace (prefixWord ++ tailWord_621852) baseStart_621852 baseEnd_621852 := by
    simpa [prefixWord, tailWord_621852, baseEnd_621852] using wordTrace_append hprefix tailTrace_621852
  have hstable : (prefixWord ++ tailWord_621852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621852).length < 2 ^ (prefixWord ++ tailWord_621852).sum := by decide
  have hdescent : baseEnd_621852 < baseStart_621852 := by decide
  rcases family_descends (prefixWord ++ tailWord_621852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621854 : List Nat := [4, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_621854 : Nat := 118140960795 + 621854 * 2 ^ 59
def prefixEnd_621854 : Nat := 4983230072969 + 3 ^ 40 * 621854 * 2
def baseEnd_621854 : Nat := 283831110152102424057913

theorem tailTrace_621854 : CollatzResearch.WordTrace tailWord_621854 prefixEnd_621854 283831110152102424057913 := by
  unfold tailWord_621854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835109836142079631620077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15120585792757758035307077 2835109836142079631620077)
  ·
    refine ⟨1063166188553279861857529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2835109836142079631620077 1063166188553279861857529)
    ·
      refine ⟨797374641414959896393147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1063166188553279861857529 797374641414959896393147)
      ·
        refine ⟨1196061962122439844589721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797374641414959896393147 1196061962122439844589721)
        ·
          refine ⟨897046471591829883442291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1196061962122439844589721 897046471591829883442291)
          ·
            refine ⟨1345569707387744825163437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897046471591829883442291 1345569707387744825163437)
            ·
              refine ⟨504588640270404309436289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1345569707387744825163437 504588640270404309436289)
              ·
                refine ⟨378441480202803232077217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504588640270404309436289 378441480202803232077217)
                ·
                  refine ⟨283831110152102424057913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378441480202803232077217 283831110152102424057913)
                  ·
                    rfl

theorem cell20_621854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_621854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621854 prefixEnd_621854 := by exact prefixLift 621854
  have htrace : WordTrace (prefixWord ++ tailWord_621854) baseStart_621854 baseEnd_621854 := by
    simpa [prefixWord, tailWord_621854, baseEnd_621854] using wordTrace_append hprefix tailTrace_621854
  have hstable : (prefixWord ++ tailWord_621854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621854).length < 2 ^ (prefixWord ++ tailWord_621854).sum := by decide
  have hdescent : baseEnd_621854 < baseStart_621854 := by decide
  rcases family_descends (prefixWord ++ tailWord_621854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621858 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_621858 : Nat := 118140960795 + 621858 * 2 ^ 59
def prefixEnd_621858 : Nat := 4983230072969 + 3 ^ 40 * 621858 * 2
def baseEnd_621858 : Nat := 283832935861096187924563

theorem tailTrace_621858 : CollatzResearch.WordTrace tailWord_621858 prefixEnd_621858 283832935861096187924563 := by
  unfold tailWord_621858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670256145280536434026557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15120683054081430490737485 5670256145280536434026557)
  ·
    refine ⟨2126346054480201162759959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5670256145280536434026557 2126346054480201162759959)
    ·
      refine ⟨3189519081720301744139939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126346054480201162759959 3189519081720301744139939)
      ·
        refine ⟨4784278622580452616209909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189519081720301744139939 4784278622580452616209909)
        ·
          refine ⟨448526120866917432769679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4784278622580452616209909 448526120866917432769679)
          ·
            refine ⟨672789181300376149154519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448526120866917432769679 672789181300376149154519)
            ·
              refine ⟨1009183771950564223731779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672789181300376149154519 1009183771950564223731779)
              ·
                refine ⟨1513775657925846335597669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009183771950564223731779 1513775657925846335597669)
                ·
                  refine ⟨283832935861096187924563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1513775657925846335597669 283832935861096187924563)
                  ·
                    rfl

theorem cell20_621858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_621858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621858 prefixEnd_621858 := by exact prefixLift 621858
  have htrace : WordTrace (prefixWord ++ tailWord_621858) baseStart_621858 baseEnd_621858 := by
    simpa [prefixWord, tailWord_621858, baseEnd_621858] using wordTrace_append hprefix tailTrace_621858
  have hstable : (prefixWord ++ tailWord_621858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621858).length < 2 ^ (prefixWord ++ tailWord_621858).sum := by decide
  have hdescent : baseEnd_621858 < baseStart_621858 := by decide
  rcases family_descends (prefixWord ++ tailWord_621858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621897 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_621897 : Nat := 118140960795 + 621897 * 2 ^ 59
def prefixEnd_621897 : Nat := 4983230072969 + 3 ^ 40 * 621897 * 2
def baseEnd_621897 : Nat := 283850736523785385624403

theorem tailTrace_621897 : CollatzResearch.WordTrace tailWord_621897 prefixEnd_621897 283850736523785385624403 := by
  unfold tailWord_621897
  simp only [CollatzResearch.WordTrace]
  refine ⟨22682447027980855396775945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15121631351987236931183963 22682447027980855396775945)
  ·
    refine ⟨17011835270985641547581959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22682447027980855396775945 17011835270985641547581959)
    ·
      refine ⟨25517752906478462321372939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17011835270985641547581959 25517752906478462321372939)
      ·
        refine ⟨38276629359717693482059409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25517752906478462321372939 38276629359717693482059409)
        ·
          refine ⟨28707472019788270111544557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38276629359717693482059409 28707472019788270111544557)
          ·
            refine ⟨10765302007420601291829209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28707472019788270111544557 10765302007420601291829209)
            ·
              refine ⟨8073976505565450968871907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10765302007420601291829209 8073976505565450968871907)
              ·
                refine ⟨12110964758348176453307861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8073976505565450968871907 12110964758348176453307861)
                ·
                  refine ⟨283850736523785385624403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12110964758348176453307861 283850736523785385624403)
                  ·
                    rfl

theorem cell20_621897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_621897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621897 prefixEnd_621897 := by exact prefixLift 621897
  have htrace : WordTrace (prefixWord ++ tailWord_621897) baseStart_621897 baseEnd_621897 := by
    simpa [prefixWord, tailWord_621897, baseEnd_621897] using wordTrace_append hprefix tailTrace_621897
  have hstable : (prefixWord ++ tailWord_621897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621897).length < 2 ^ (prefixWord ++ tailWord_621897).sum := by decide
  have hdescent : baseEnd_621897 < baseStart_621897 := by decide
  rcases family_descends (prefixWord ++ tailWord_621897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621914 : List Nat := [3, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_621914 : Nat := 118140960795 + 621914 * 2 ^ 59
def prefixEnd_621914 : Nat := 4983230072969 + 3 ^ 40 * 621914 * 2
def baseEnd_621914 : Nat := 283858495787008882057667

theorem tailTrace_621914 : CollatzResearch.WordTrace tailWord_621914 prefixEnd_621914 283858495787008882057667 := by
  unfold tailWord_621914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670766767229816825036199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15122044712612844866763197 5670766767229816825036199)
  ·
    refine ⟨8506150150844725237554299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5670766767229816825036199 8506150150844725237554299)
    ·
      refine ⟨12759225226267087856331449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8506150150844725237554299 12759225226267087856331449)
      ·
        refine ⟨9569418919700315892248587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12759225226267087856331449 9569418919700315892248587)
        ·
          refine ⟨14354128379550473838372881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9569418919700315892248587 14354128379550473838372881)
          ·
            refine ⟨10765596284662855378779661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14354128379550473838372881 10765596284662855378779661)
            ·
              refine ⟨4037098606748570767042373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10765596284662855378779661 4037098606748570767042373)
              ·
                refine ⟨756955988765357018820445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4037098606748570767042373 756955988765357018820445)
                ·
                  refine ⟨283858495787008882057667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756955988765357018820445 283858495787008882057667)
                  ·
                    rfl

theorem cell20_621914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_621914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621914 prefixEnd_621914 := by exact prefixLift 621914
  have htrace : WordTrace (prefixWord ++ tailWord_621914) baseStart_621914 baseEnd_621914 := by
    simpa [prefixWord, tailWord_621914, baseEnd_621914] using wordTrace_append hprefix tailTrace_621914
  have hstable : (prefixWord ++ tailWord_621914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621914).length < 2 ^ (prefixWord ++ tailWord_621914).sum := by decide
  have hdescent : baseEnd_621914 < baseStart_621914 := by decide
  rcases family_descends (prefixWord ++ tailWord_621914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621955 : List Nat := [1, 1, 1, 3, 5, 2, 2, 3, 2]
def baseStart_621955 : Nat := 118140960795 + 621955 * 2 ^ 59
def prefixEnd_621955 : Nat := 4983230072969 + 3 ^ 40 * 621955 * 2
def baseEnd_621955 : Nat := 283877209304194961690833

theorem tailTrace_621955 : CollatzResearch.WordTrace tailWord_621955 prefixEnd_621955 283877209304194961690833 := by
  unfold tailWord_621955
  simp only [CollatzResearch.WordTrace]
  refine ⟨22684562461770731302387319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15123041641180487534924879 22684562461770731302387319)
  ·
    refine ⟨34026843692656096953580979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22684562461770731302387319 34026843692656096953580979)
    ·
      refine ⟨51040265538984145430371469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34026843692656096953580979 51040265538984145430371469)
      ·
        refine ⟨19140099577119054536389301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51040265538984145430371469 19140099577119054536389301)
        ·
          refine ⟨1794384335354911362786497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19140099577119054536389301 1794384335354911362786497)
          ·
            refine ⟨1345788251516183522089873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1794384335354911362786497 1345788251516183522089873)
            ·
              refine ⟨1009341188637137641567405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345788251516183522089873 1009341188637137641567405)
              ·
                refine ⟨378502945738926615587777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1009341188637137641567405 378502945738926615587777)
                ·
                  refine ⟨283877209304194961690833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378502945738926615587777 283877209304194961690833)
                  ·
                    rfl

theorem cell20_621955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 2].length) (baseStart_621955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621955 prefixEnd_621955 := by exact prefixLift 621955
  have htrace : WordTrace (prefixWord ++ tailWord_621955) baseStart_621955 baseEnd_621955 := by
    simpa [prefixWord, tailWord_621955, baseEnd_621955] using wordTrace_append hprefix tailTrace_621955
  have hstable : (prefixWord ++ tailWord_621955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621955).length < 2 ^ (prefixWord ++ tailWord_621955).sum := by decide
  have hdescent : baseEnd_621955 < baseStart_621955 := by decide
  rcases family_descends (prefixWord ++ tailWord_621955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621986 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_621986 : Nat := 118140960795 + 621986 * 2 ^ 59
def prefixEnd_621986 : Nat := 4983230072969 + 3 ^ 40 * 621986 * 2
def baseEnd_621986 : Nat := 283891358548896631657373

theorem tailTrace_621986 : CollatzResearch.WordTrace tailWord_621986 prefixEnd_621986 283891358548896631657373 := by
  unfold tailWord_621986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671423281164605899191453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15123795416438949064510541 5671423281164605899191453)
  ·
    refine ⟨2126783730436727212196795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5671423281164605899191453 2126783730436727212196795)
    ·
      refine ⟨3190175595655090818295193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126783730436727212196795 3190175595655090818295193)
      ·
        refine ⟨2392631696741318113721395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3190175595655090818295193 2392631696741318113721395)
        ·
          refine ⟨3588947545111977170582093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392631696741318113721395 3588947545111977170582093)
          ·
            refine ⟨1345855329416991438968285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3588947545111977170582093 1345855329416991438968285)
            ·
              refine ⟨504695748531371789613107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1345855329416991438968285 504695748531371789613107)
              ·
                refine ⟨757043622797057684419661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504695748531371789613107 757043622797057684419661)
                ·
                  refine ⟨283891358548896631657373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757043622797057684419661 283891358548896631657373)
                  ·
                    rfl

theorem cell20_621986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_621986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_621986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_621986 prefixEnd_621986 := by exact prefixLift 621986
  have htrace : WordTrace (prefixWord ++ tailWord_621986) baseStart_621986 baseEnd_621986 := by
    simpa [prefixWord, tailWord_621986, baseEnd_621986] using wordTrace_append hprefix tailTrace_621986
  have hstable : (prefixWord ++ tailWord_621986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621986).length < 2 ^ (prefixWord ++ tailWord_621986).sum := by decide
  have hdescent : baseEnd_621986 < baseStart_621986 := by decide
  rcases family_descends (prefixWord ++ tailWord_621986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622028 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_622028 : Nat := 118140960795 + 622028 * 2 ^ 59
def prefixEnd_622028 : Nat := 4983230072969 + 3 ^ 40 * 622028 * 2
def baseEnd_622028 : Nat := 283910528493331152257201

theorem tailTrace_622028 : CollatzResearch.WordTrace tailWord_622028 prefixEnd_622028 283910528493331152257201 := by
  unfold tailWord_622028
  simp only [CollatzResearch.WordTrace]
  refine ⟨11343612495253132384897369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15124816660337509846529825 11343612495253132384897369)
  ·
    refine ⟨8507709371439849288673027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11343612495253132384897369 8507709371439849288673027)
    ·
      refine ⟨12761564057159773933009541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8507709371439849288673027 12761564057159773933009541)
      ·
        refine ⟨2392793260717457612439289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12761564057159773933009541 2392793260717457612439289)
        ·
          refine ⟨1794594945538093209329467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2392793260717457612439289 1794594945538093209329467)
          ·
            refine ⟨2691892418307139813994201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794594945538093209329467 2691892418307139813994201)
            ·
              refine ⟨2018919313730354860495651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2691892418307139813994201 2018919313730354860495651)
              ·
                refine ⟨3028378970595532290743477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018919313730354860495651 3028378970595532290743477)
                ·
                  refine ⟨283910528493331152257201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3028378970595532290743477 283910528493331152257201)
                  ·
                    rfl

theorem cell20_622028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_622028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622028 prefixEnd_622028 := by exact prefixLift 622028
  have htrace : WordTrace (prefixWord ++ tailWord_622028) baseStart_622028 baseEnd_622028 := by
    simpa [prefixWord, tailWord_622028, baseEnd_622028] using wordTrace_append hprefix tailTrace_622028
  have hstable : (prefixWord ++ tailWord_622028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622028).length < 2 ^ (prefixWord ++ tailWord_622028).sum := by decide
  have hdescent : baseEnd_622028 < baseStart_622028 := by decide
  rcases family_descends (prefixWord ++ tailWord_622028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622038 : List Nat := [5, 2, 1, 1, 1, 3, 2, 5]
def baseStart_622038 : Nat := 118140960795 + 622038 * 2 ^ 59
def prefixEnd_622038 : Nat := 4983230072969 + 3 ^ 40 * 622038 * 2
def baseEnd_622038 : Nat := 94638364255271853974609

theorem tailTrace_622038 : CollatzResearch.WordTrace tailWord_622038 prefixEnd_622038 94638364255271853974609 := by
  unfold tailWord_622038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417974357529377279853673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15125059813646690985105845 1417974357529377279853673)
  ·
    refine ⟨1063480768147032959890255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1417974357529377279853673 1063480768147032959890255)
    ·
      refine ⟨1595221152220549439835383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1063480768147032959890255 1595221152220549439835383)
      ·
        refine ⟨2392831728330824159753075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595221152220549439835383 2392831728330824159753075)
        ·
          refine ⟨3589247592496236239629613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392831728330824159753075 3589247592496236239629613)
          ·
            refine ⟨1345967847186088589861105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3589247592496236239629613 1345967847186088589861105)
            ·
              refine ⟨1009475885389566442395829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345967847186088589861105 1009475885389566442395829)
              ·
                refine ⟨94638364255271853974609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1009475885389566442395829 94638364255271853974609)
                ·
                  rfl

theorem cell20_622038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_622038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622038 prefixEnd_622038 := by exact prefixLift 622038
  have htrace : WordTrace (prefixWord ++ tailWord_622038) baseStart_622038 baseEnd_622038 := by
    simpa [prefixWord, tailWord_622038, baseEnd_622038] using wordTrace_append hprefix tailTrace_622038
  have hstable : (prefixWord ++ tailWord_622038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622038).length < 2 ^ (prefixWord ++ tailWord_622038).sum := by decide
  have hdescent : baseEnd_622038 < baseStart_622038 := by decide
  rcases family_descends (prefixWord ++ tailWord_622038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622042 : List Nat := [3, 1, 1, 2, 3, 2, 1, 7]
def baseStart_622042 : Nat := 118140960795 + 622042 * 2 ^ 59
def prefixEnd_622042 : Nat := 4983230072969 + 3 ^ 40 * 622042 * 2
def baseEnd_622042 : Nat := 94638972824936441930159

theorem tailTrace_622042 : CollatzResearch.WordTrace tailWord_622042 prefixEnd_622042 94638972824936441930159 := by
  unfold tailWord_622042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671933903113886290201095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15125157074970363440536253 5671933903113886290201095)
  ·
    refine ⟨8507900854670829435301643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5671933903113886290201095 8507900854670829435301643)
    ·
      refine ⟨12761851282006244152952465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8507900854670829435301643 12761851282006244152952465)
      ·
        refine ⟨9571388461504683114714349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12761851282006244152952465 9571388461504683114714349)
        ·
          refine ⟨3589270673064256168017881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9571388461504683114714349 3589270673064256168017881)
          ·
            refine ⟨2691953004798192126013411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3589270673064256168017881 2691953004798192126013411)
            ·
              refine ⟨4037929507197288189020117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691953004798192126013411 4037929507197288189020117)
              ·
                refine ⟨94638972824936441930159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4037929507197288189020117 94638972824936441930159)
                ·
                  rfl

theorem cell20_622042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_622042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622042 prefixEnd_622042 := by exact prefixLift 622042
  have htrace : WordTrace (prefixWord ++ tailWord_622042) baseStart_622042 baseEnd_622042 := by
    simpa [prefixWord, tailWord_622042, baseEnd_622042] using wordTrace_append hprefix tailTrace_622042
  have hstable : (prefixWord ++ tailWord_622042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622042).length < 2 ^ (prefixWord ++ tailWord_622042).sum := by decide
  have hdescent : baseEnd_622042 < baseStart_622042 := by decide
  rcases family_descends (prefixWord ++ tailWord_622042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622045 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 3]
def baseStart_622045 : Nat := 118140960795 + 622045 * 2 ^ 59
def prefixEnd_622045 : Nat := 4983230072969 + 3 ^ 40 * 622045 * 2
def baseEnd_622045 : Nat := 283918287756554648690465

theorem tailTrace_622045 : CollatzResearch.WordTrace tailWord_622045 prefixEnd_622045 283918287756554648690465 := by
  unfold tailWord_622045
  simp only [CollatzResearch.WordTrace]
  refine ⟨22687845031444676673163589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15125230020963117782109059 22687845031444676673163589)
  ·
    refine ⟨4253970943395876876218173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22687845031444676673163589 4253970943395876876218173)
    ·
      refine ⟨1595239103773453828581815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4253970943395876876218173 1595239103773453828581815)
      ·
        refine ⟨2392858655660180742872723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595239103773453828581815 2392858655660180742872723)
        ·
          refine ⟨3589287983490271114309085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392858655660180742872723 3589287983490271114309085)
          ·
            refine ⟨1345982993808851667865907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3589287983490271114309085 1345982993808851667865907)
            ·
              refine ⟨2018974490713277501798861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345982993808851667865907 2018974490713277501798861)
              ·
                refine ⟨757115434017479063174573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2018974490713277501798861 757115434017479063174573)
                ·
                  refine ⟨283918287756554648690465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757115434017479063174573 283918287756554648690465)
                  ·
                    rfl

theorem cell20_622045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_622045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622045 prefixEnd_622045 := by exact prefixLift 622045
  have htrace : WordTrace (prefixWord ++ tailWord_622045) baseStart_622045 baseEnd_622045 := by
    simpa [prefixWord, tailWord_622045, baseEnd_622045] using wordTrace_append hprefix tailTrace_622045
  have hstable : (prefixWord ++ tailWord_622045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622045).length < 2 ^ (prefixWord ++ tailWord_622045).sum := by decide
  have hdescent : baseEnd_622045 < baseStart_622045 := by decide
  rcases family_descends (prefixWord ++ tailWord_622045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622149 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_622149 : Nat := 118140960795 + 622149 * 2 ^ 59
def prefixEnd_622149 : Nat := 4983230072969 + 3 ^ 40 * 622149 * 2
def baseEnd_622149 : Nat := 283965756190392509223373

theorem tailTrace_622149 : CollatzResearch.WordTrace tailWord_622149 prefixEnd_622149 283965756190392509223373 := by
  unfold tailWord_622149
  simp only [CollatzResearch.WordTrace]
  refine ⟨22691638223067902434949501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15127758815378601623299667 22691638223067902434949501)
  ·
    refine ⟨8509364333650463413106063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22691638223067902434949501 8509364333650463413106063)
    ·
      refine ⟨12764046500475695119659095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8509364333650463413106063 12764046500475695119659095)
      ·
        refine ⟨19146069750713542679488643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12764046500475695119659095 19146069750713542679488643)
        ·
          refine ⟨28719104626070314019232965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19146069750713542679488643 28719104626070314019232965)
          ·
            refine ⟨5384832117388183878606181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28719104626070314019232965 5384832117388183878606181)
            ·
              refine ⟨1009656022010284477238659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5384832117388183878606181 1009656022010284477238659)
              ·
                refine ⟨1514484033015426715857989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009656022010284477238659 1514484033015426715857989)
                ·
                  refine ⟨283965756190392509223373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1514484033015426715857989 283965756190392509223373)
                  ·
                    rfl

theorem cell20_622149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_622149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622149 prefixEnd_622149 := by exact prefixLift 622149
  have htrace : WordTrace (prefixWord ++ tailWord_622149) baseStart_622149 baseEnd_622149 := by
    simpa [prefixWord, tailWord_622149, baseEnd_622149] using wordTrace_append hprefix tailTrace_622149
  have hstable : (prefixWord ++ tailWord_622149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622149).length < 2 ^ (prefixWord ++ tailWord_622149).sum := by decide
  have hdescent : baseEnd_622149 < baseStart_622149 := by decide
  rcases family_descends (prefixWord ++ tailWord_622149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622190 : List Nat := [4, 1, 2, 2, 4, 1, 6]
def baseStart_622190 : Nat := 118140960795 + 622190 * 2 ^ 59
def prefixEnd_622190 : Nat := 4983230072969 + 3 ^ 40 * 622190 * 2
def baseEnd_622190 : Nat := 31553829967508732095171

theorem tailTrace_622190 : CollatzResearch.WordTrace tailWord_622190 prefixEnd_622190 31553829967508732095171 := by
  unfold tailWord_622190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836641701989920804649003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15128755743946244291461349 2836641701989920804649003)
  ·
    refine ⟨4254962552984881206973505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2836641701989920804649003 4254962552984881206973505)
    ·
      refine ⟨3191221914738660905230129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4254962552984881206973505 3191221914738660905230129)
      ·
        refine ⟨2393416436053995678922597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3191221914738660905230129 2393416436053995678922597)
        ·
          refine ⟨448765581760124189797987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2393416436053995678922597 448765581760124189797987)
          ·
            refine ⟨673148372640186284696981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448765581760124189797987 673148372640186284696981)
            ·
              refine ⟨31553829967508732095171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 673148372640186284696981 31553829967508732095171)
              ·
                rfl

theorem cell20_622190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 6].length) (baseStart_622190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622190 prefixEnd_622190 := by exact prefixLift 622190
  have htrace : WordTrace (prefixWord ++ tailWord_622190) baseStart_622190 baseEnd_622190 := by
    simpa [prefixWord, tailWord_622190, baseEnd_622190] using wordTrace_append hprefix tailTrace_622190
  have hstable : (prefixWord ++ tailWord_622190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622190).length < 2 ^ (prefixWord ++ tailWord_622190).sum := by decide
  have hdescent : baseEnd_622190 < baseStart_622190 := by decide
  rcases family_descends (prefixWord ++ tailWord_622190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622194 : List Nat := [3, 2, 1, 2, 3, 1, 8]
def baseStart_622194 : Nat := 118140960795 + 622194 * 2 ^ 59
def prefixEnd_622194 : Nat := 4983230072969 + 3 ^ 40 * 622194 * 2
def baseEnd_622194 : Nat := 31554032824063594747021

theorem tailTrace_622194 : CollatzResearch.WordTrace tailWord_622194 prefixEnd_622194 31554032824063594747021 := by
  unfold tailWord_622194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5673319876976218780084409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15128853005269916746891757 5673319876976218780084409)
  ·
    refine ⟨4254989907732164085063307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5673319876976218780084409 4254989907732164085063307)
    ·
      refine ⟨6382484861598246127594961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4254989907732164085063307 6382484861598246127594961)
      ·
        refine ⟨4786863646198684595696221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6382484861598246127594961 4786863646198684595696221)
        ·
          refine ⟨1795073867324506723386083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4786863646198684595696221 1795073867324506723386083)
          ·
            refine ⟨2692610800986760085079125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1795073867324506723386083 2692610800986760085079125)
            ·
              refine ⟨31554032824063594747021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2692610800986760085079125 31554032824063594747021)
              ·
                rfl

theorem cell20_622194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 8].length) (baseStart_622194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622194 prefixEnd_622194 := by exact prefixLift 622194
  have htrace : WordTrace (prefixWord ++ tailWord_622194) baseStart_622194 baseEnd_622194 := by
    simpa [prefixWord, tailWord_622194, baseEnd_622194] using wordTrace_append hprefix tailTrace_622194
  have hstable : (prefixWord ++ tailWord_622194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622194).length < 2 ^ (prefixWord ++ tailWord_622194).sum := by decide
  have hdescent : baseEnd_622194 < baseStart_622194 := by decide
  rcases family_descends (prefixWord ++ tailWord_622194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622201 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_622201 : Nat := 118140960795 + 622201 * 2 ^ 59
def prefixEnd_622201 : Nat := 4983230072969 + 3 ^ 40 * 622201 * 2
def baseEnd_622201 : Nat := 283989490407311439489827

theorem tailTrace_622201 : CollatzResearch.WordTrace tailWord_622201 prefixEnd_622201 283989490407311439489827 := by
  unfold tailWord_622201
  simp only [CollatzResearch.WordTrace]
  refine ⟨22693534818879515315842457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15129023212586343543894971 22693534818879515315842457)
  ·
    refine ⟨17020151114159636486881843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22693534818879515315842457 17020151114159636486881843)
    ·
      refine ⟨25530226671239454730322765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17020151114159636486881843 25530226671239454730322765)
      ·
        refine ⟨9573835001714795523871037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25530226671239454730322765 9573835001714795523871037)
        ·
          refine ⟨3590188125643048321451639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9573835001714795523871037 3590188125643048321451639)
          ·
            refine ⟨5385282188464572482177459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590188125643048321451639 5385282188464572482177459)
            ·
              refine ⟨8077923282696858723266189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385282188464572482177459 8077923282696858723266189)
              ·
                refine ⟨3029221231011322021224821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8077923282696858723266189 3029221231011322021224821)
                ·
                  refine ⟨283989490407311439489827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3029221231011322021224821 283989490407311439489827)
                  ·
                    rfl

theorem cell20_622201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_622201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622201 prefixEnd_622201 := by exact prefixLift 622201
  have htrace : WordTrace (prefixWord ++ tailWord_622201) baseStart_622201 baseEnd_622201 := by
    simpa [prefixWord, tailWord_622201, baseEnd_622201] using wordTrace_append hprefix tailTrace_622201
  have hstable : (prefixWord ++ tailWord_622201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622201).length < 2 ^ (prefixWord ++ tailWord_622201).sum := by decide
  have hdescent : baseEnd_622201 < baseStart_622201 := by decide
  rcases family_descends (prefixWord ++ tailWord_622201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622232 : List Nat := [2, 1, 2, 4, 1, 2, 2, 6]
def baseStart_622232 : Nat := 118140960795 + 622232 * 2 ^ 59
def prefixEnd_622232 : Nat := 4983230072969 + 3 ^ 40 * 622232 * 2
def baseEnd_622232 : Nat := 94667879884004369818789

theorem tailTrace_622232 : CollatzResearch.WordTrace tailWord_622232 prefixEnd_622232 94667879884004369818789 := by
  unfold tailWord_622232
  simp only [CollatzResearch.WordTrace]
  refine ⟨11347332740883603805110475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15129776987844805073480633 11347332740883603805110475)
  ·
    refine ⟨17020999111325405707665713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11347332740883603805110475 17020999111325405707665713)
    ·
      refine ⟨12765749333494054280749285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17020999111325405707665713 12765749333494054280749285)
      ·
        refine ⟨2393578000030135177640491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12765749333494054280749285 2393578000030135177640491)
        ·
          refine ⟨3590367000045202766460737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393578000030135177640491 3590367000045202766460737)
          ·
            refine ⟨2692775250033902074845553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3590367000045202766460737 2692775250033902074845553)
            ·
              refine ⟨2019581437525426556134165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2692775250033902074845553 2019581437525426556134165)
              ·
                refine ⟨94667879884004369818789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2019581437525426556134165 94667879884004369818789)
                ·
                  rfl

theorem cell20_622232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_622232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622232 prefixEnd_622232 := by exact prefixLift 622232
  have htrace : WordTrace (prefixWord ++ tailWord_622232) baseStart_622232 baseEnd_622232 := by
    simpa [prefixWord, tailWord_622232, baseEnd_622232] using wordTrace_append hprefix tailTrace_622232
  have hstable : (prefixWord ++ tailWord_622232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622232).length < 2 ^ (prefixWord ++ tailWord_622232).sum := by decide
  have hdescent : baseEnd_622232 < baseStart_622232 := by decide
  rcases family_descends (prefixWord ++ tailWord_622232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622311 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 5]
def baseStart_622311 : Nat := 118140960795 + 622311 * 2 ^ 59
def prefixEnd_622311 : Nat := 4983230072969 + 3 ^ 40 * 622311 * 2
def baseEnd_622311 : Nat := 284039697404639945822711

theorem tailTrace_622311 : CollatzResearch.WordTrace tailWord_622311 prefixEnd_622311 284039697404639945822711 := by
  unfold tailWord_622311
  simp only [CollatzResearch.WordTrace]
  refine ⟨22697546848481004102346787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15131697898987336068231191 22697546848481004102346787)
  ·
    refine ⟨34046320272721506153520181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22697546848481004102346787 34046320272721506153520181)
    ·
      refine ⟨3191842525567641201892517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34046320272721506153520181 3191842525567641201892517)
      ·
        refine ⟨598470473543932725354847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3191842525567641201892517 598470473543932725354847)
        ·
          refine ⟨897705710315899088032271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598470473543932725354847 897705710315899088032271)
          ·
            refine ⟨1346558565473848632048407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897705710315899088032271 1346558565473848632048407)
            ·
              refine ⟨2019837848210772948072611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346558565473848632048407 2019837848210772948072611)
              ·
                refine ⟨3029756772316159422108917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019837848210772948072611 3029756772316159422108917)
                ·
                  refine ⟨284039697404639945822711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3029756772316159422108917 284039697404639945822711)
                  ·
                    rfl

theorem cell20_622311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 5].length) (baseStart_622311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622311 prefixEnd_622311 := by exact prefixLift 622311
  have htrace : WordTrace (prefixWord ++ tailWord_622311) baseStart_622311 baseEnd_622311 := by
    simpa [prefixWord, tailWord_622311, baseEnd_622311] using wordTrace_append hprefix tailTrace_622311
  have hstable : (prefixWord ++ tailWord_622311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622311).length < 2 ^ (prefixWord ++ tailWord_622311).sum := by decide
  have hdescent : baseEnd_622311 < baseStart_622311 := by decide
  rcases family_descends (prefixWord ++ tailWord_622311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622318 : List Nat := [4, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_622318 : Nat := 118140960795 + 622318 * 2 ^ 59
def prefixEnd_622318 : Nat := 4983230072969 + 3 ^ 40 * 622318 * 2
def baseEnd_622318 : Nat := 284042892395379032589349

theorem tailTrace_622318 : CollatzResearch.WordTrace tailWord_622318 prefixEnd_622318 284042892395379032589349 := by
  unfold tailWord_622318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837225269931955537231451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15131868106303762865234405 2837225269931955537231451)
  ·
    refine ⟨4255837904897933305847177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2837225269931955537231451 4255837904897933305847177)
    ·
      refine ⟨3191878428673449979385383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4255837904897933305847177 3191878428673449979385383)
      ·
        refine ⟨4787817643010174969078075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191878428673449979385383 4787817643010174969078075)
        ·
          refine ⟨7181726464515262453617113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4787817643010174969078075 7181726464515262453617113)
          ·
            refine ⟨5386294848386446840212835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7181726464515262453617113 5386294848386446840212835)
            ·
              refine ⟨8079442272579670260319253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386294848386446840212835 8079442272579670260319253)
              ·
                refine ⟨378723856527172043452465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8079442272579670260319253 378723856527172043452465)
                ·
                  refine ⟨284042892395379032589349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378723856527172043452465 284042892395379032589349)
                  ·
                    rfl

theorem cell20_622318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_622318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622318 prefixEnd_622318 := by exact prefixLift 622318
  have htrace : WordTrace (prefixWord ++ tailWord_622318) baseStart_622318 baseEnd_622318 := by
    simpa [prefixWord, tailWord_622318, baseEnd_622318] using wordTrace_append hprefix tailTrace_622318
  have hstable : (prefixWord ++ tailWord_622318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622318).length < 2 ^ (prefixWord ++ tailWord_622318).sum := by decide
  have hdescent : baseEnd_622318 < baseStart_622318 := by decide
  rcases family_descends (prefixWord ++ tailWord_622318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622346 : List Nat := [3, 1, 2, 2, 1, 4, 1, 6]
def baseStart_622346 : Nat := 118140960795 + 622346 * 2 ^ 59
def prefixEnd_622346 : Nat := 4983230072969 + 3 ^ 40 * 622346 * 2
def baseEnd_622346 : Nat := 94685224119445126551967

theorem tailTrace_622346 : CollatzResearch.WordTrace tailWord_622346 prefixEnd_622346 94685224119445126551967 := by
  unfold tailWord_622346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5674705850838551269967723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15132548935569470053247261 5674705850838551269967723)
  ·
    refine ⟨8512058776257826904951585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5674705850838551269967723 8512058776257826904951585)
    ·
      refine ⟨6384044082193370178713689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8512058776257826904951585 6384044082193370178713689)
      ·
        refine ⟨4788033061645027634035267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6384044082193370178713689 4788033061645027634035267)
        ·
          refine ⟨7182049592467541451052901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788033061645027634035267 7182049592467541451052901)
          ·
            refine ⟨1346634298587664022072419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7182049592467541451052901 1346634298587664022072419)
            ·
              refine ⟨2019951447881496033108629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346634298587664022072419 2019951447881496033108629)
              ·
                refine ⟨94685224119445126551967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2019951447881496033108629 94685224119445126551967)
                ·
                  rfl

theorem cell20_622346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_622346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622346 prefixEnd_622346 := by exact prefixLift 622346
  have htrace : WordTrace (prefixWord ++ tailWord_622346) baseStart_622346 baseEnd_622346 := by
    simpa [prefixWord, tailWord_622346, baseEnd_622346] using wordTrace_append hprefix tailTrace_622346
  have hstable : (prefixWord ++ tailWord_622346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622346).length < 2 ^ (prefixWord ++ tailWord_622346).sum := by decide
  have hdescent : baseEnd_622346 < baseStart_622346 := by decide
  rcases family_descends (prefixWord ++ tailWord_622346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622360 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_622360 : Nat := 118140960795 + 622360 * 2 ^ 59
def prefixEnd_622360 : Nat := 4983230072969 + 3 ^ 40 * 622360 * 2
def baseEnd_622360 : Nat := 284062062339813553189177

theorem tailTrace_622360 : CollatzResearch.WordTrace tailWord_622360 prefixEnd_622360 284062062339813553189177 := by
  unfold tailWord_622360
  simp only [CollatzResearch.WordTrace]
  refine ⟨11349667012651742735440267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15132889350202323647253689 11349667012651742735440267)
  ·
    refine ⟨17024500518977614103160401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11349667012651742735440267 17024500518977614103160401)
    ·
      refine ⟨12768375389233210577370301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17024500518977614103160401 12768375389233210577370301)
      ·
        refine ⟨4788140770962453966513863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12768375389233210577370301 4788140770962453966513863)
        ·
          refine ⟨7182211156443680949770795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788140770962453966513863 7182211156443680949770795)
          ·
            refine ⟨10773316734665521424656193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7182211156443680949770795 10773316734665521424656193)
            ·
              refine ⟨8079987550999141068492145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10773316734665521424656193 8079987550999141068492145)
              ·
                refine ⟨6059990663249355801369109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8079987550999141068492145 6059990663249355801369109)
                ·
                  refine ⟨284062062339813553189177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6059990663249355801369109 284062062339813553189177)
                  ·
                    rfl

theorem cell20_622360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_622360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622360 prefixEnd_622360 := by exact prefixLift 622360
  have htrace : WordTrace (prefixWord ++ tailWord_622360) baseStart_622360 baseEnd_622360 := by
    simpa [prefixWord, tailWord_622360, baseEnd_622360] using wordTrace_append hprefix tailTrace_622360
  have hstable : (prefixWord ++ tailWord_622360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622360).length < 2 ^ (prefixWord ++ tailWord_622360).sum := by decide
  have hdescent : baseEnd_622360 < baseStart_622360 := by decide
  rcases family_descends (prefixWord ++ tailWord_622360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622370 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_622370 : Nat := 118140960795 + 622370 * 2 ^ 59
def prefixEnd_622370 : Nat := 4983230072969 + 3 ^ 40 * 622370 * 2
def baseEnd_622370 : Nat := 284066626612297962855803

theorem tailTrace_622370 : CollatzResearch.WordTrace tailWord_622370 prefixEnd_622370 284066626612297962855803 := by
  unfold tailWord_622370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5674924688816814294686141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15133132503511504785829709 5674924688816814294686141)
  ·
    refine ⟨2128096758306305360507303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5674924688816814294686141 2128096758306305360507303)
    ·
      refine ⟨3192145137459458040760955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128096758306305360507303 3192145137459458040760955)
      ·
        refine ⟨4788217706189187061141433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3192145137459458040760955 4788217706189187061141433)
        ·
          refine ⟨3591163279641890295856075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4788217706189187061141433 3591163279641890295856075)
          ·
            refine ⟨5386744919462835443784113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591163279641890295856075 5386744919462835443784113)
            ·
              refine ⟨4040058689597126582838085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5386744919462835443784113 4040058689597126582838085)
              ·
                refine ⟨757511004299461234282141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4040058689597126582838085 757511004299461234282141)
                ·
                  refine ⟨284066626612297962855803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757511004299461234282141 284066626612297962855803)
                  ·
                    rfl

theorem cell20_622370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_622370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622370 prefixEnd_622370 := by exact prefixLift 622370
  have htrace : WordTrace (prefixWord ++ tailWord_622370) baseStart_622370 baseEnd_622370 := by
    simpa [prefixWord, tailWord_622370, baseEnd_622370] using wordTrace_append hprefix tailTrace_622370
  have hstable : (prefixWord ++ tailWord_622370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622370).length < 2 ^ (prefixWord ++ tailWord_622370).sum := by decide
  have hdescent : baseEnd_622370 < baseStart_622370 := by decide
  rcases family_descends (prefixWord ++ tailWord_622370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622373 : List Nat := [1, 3, 1, 2, 3, 3, 3, 2, 2]
def baseStart_622373 : Nat := 118140960795 + 622373 * 2 ^ 59
def prefixEnd_622373 : Nat := 4983230072969 + 3 ^ 40 * 622373 * 2
def baseEnd_622373 : Nat := 284067995894043285755791

theorem tailTrace_622373 : CollatzResearch.WordTrace tailWord_622373 prefixEnd_622373 284067995894043285755791 := by
  unfold tailWord_622373
  simp only [CollatzResearch.WordTrace]
  refine ⟨22699808174256388691103773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15133205449504259127402515 22699808174256388691103773)
  ·
    refine ⟨8512428065346145759163915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22699808174256388691103773 8512428065346145759163915)
    ·
      refine ⟨12768642098019218638745873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8512428065346145759163915 12768642098019218638745873)
      ·
        refine ⟨9576481573514413979059405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12768642098019218638745873 9576481573514413979059405)
        ·
          refine ⟨3591180590067905242147277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9576481573514413979059405 3591180590067905242147277)
          ·
            refine ⟨1346692721275464465805229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3591180590067905242147277 1346692721275464465805229)
            ·
              refine ⟨505009770478299174676961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1346692721275464465805229 505009770478299174676961)
              ·
                refine ⟨378757327858724381007721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505009770478299174676961 378757327858724381007721)
                ·
                  refine ⟨284067995894043285755791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378757327858724381007721 284067995894043285755791)
                  ·
                    rfl

theorem cell20_622373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_622373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622373 prefixEnd_622373 := by exact prefixLift 622373
  have htrace : WordTrace (prefixWord ++ tailWord_622373) baseStart_622373 baseEnd_622373 := by
    simpa [prefixWord, tailWord_622373, baseEnd_622373] using wordTrace_append hprefix tailTrace_622373
  have hstable : (prefixWord ++ tailWord_622373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622373).length < 2 ^ (prefixWord ++ tailWord_622373).sum := by decide
  have hdescent : baseEnd_622373 < baseStart_622373 := by decide
  rcases family_descends (prefixWord ++ tailWord_622373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622405 : List Nat := [1, 3, 1, 1, 1, 2, 3, 8]
def baseStart_622405 : Nat := 118140960795 + 622405 * 2 ^ 59
def prefixEnd_622405 : Nat := 4983230072969 + 3 ^ 40 * 622405 * 2
def baseEnd_622405 : Nat := 94694200521997798896331

theorem tailTrace_622405 : CollatzResearch.WordTrace tailWord_622405 prefixEnd_622405 94694200521997798896331 := by
  unfold tailWord_622405
  simp only [CollatzResearch.WordTrace]
  refine ⟨22700975310140458156268669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15133983540093638770845779 22700975310140458156268669)
  ·
    refine ⟨8512865741302671808600751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22700975310140458156268669 8512865741302671808600751)
    ·
      refine ⟨12769298611954007712901127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8512865741302671808600751 12769298611954007712901127)
      ·
        refine ⟨19153947917931011569351691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12769298611954007712901127 19153947917931011569351691)
        ·
          refine ⟨28730921876896517354027537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19153947917931011569351691 28730921876896517354027537)
          ·
            refine ⟨21548191407672388015520653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28730921876896517354027537 21548191407672388015520653)
            ·
              refine ⟨8080571777877145505820245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21548191407672388015520653 8080571777877145505820245)
              ·
                refine ⟨94694200521997798896331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8080571777877145505820245 94694200521997798896331)
                ·
                  rfl

theorem cell20_622405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_622405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622405 prefixEnd_622405 := by exact prefixLift 622405
  have htrace : WordTrace (prefixWord ++ tailWord_622405) baseStart_622405 baseEnd_622405 := by
    simpa [prefixWord, tailWord_622405, baseEnd_622405] using wordTrace_append hprefix tailTrace_622405
  have hstable : (prefixWord ++ tailWord_622405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622405).length < 2 ^ (prefixWord ++ tailWord_622405).sum := by decide
  have hdescent : baseEnd_622405 < baseStart_622405 := by decide
  rcases family_descends (prefixWord ++ tailWord_622405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622432 : List Nat := [2, 1, 1, 3, 3, 3, 1, 4, 2]
def baseStart_622432 : Nat := 118140960795 + 622432 * 2 ^ 59
def prefixEnd_622432 : Nat := 4983230072969 + 3 ^ 40 * 622432 * 2
def baseEnd_622432 : Nat := 284094925101701302788883

theorem tailTrace_622432 : CollatzResearch.WordTrace tailWord_622432 prefixEnd_622432 284094925101701302788883 := by
  unfold tailWord_622432
  simp only [CollatzResearch.WordTrace]
  refine ⟨11350980040521320883750775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15134640054028427845001033 11350980040521320883750775)
  ·
    refine ⟨17026470060781981325626163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11350980040521320883750775 17026470060781981325626163)
    ·
      refine ⟨25539705091172971988439245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17026470060781981325626163 25539705091172971988439245)
      ·
        refine ⟨9577389409189864495664717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25539705091172971988439245 9577389409189864495664717)
        ·
          refine ⟨3591521028446199185874269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9577389409189864495664717 3591521028446199185874269)
          ·
            refine ⟨1346820385667324694702851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3591521028446199185874269 1346820385667324694702851)
            ·
              refine ⟨2020230578500987042054277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346820385667324694702851 2020230578500987042054277)
              ·
                refine ⟨378793233468935070385177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2020230578500987042054277 378793233468935070385177)
                ·
                  refine ⟨284094925101701302788883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378793233468935070385177 284094925101701302788883)
                  ·
                    rfl

theorem cell20_622432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 4, 2].length) (baseStart_622432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622432 prefixEnd_622432 := by exact prefixLift 622432
  have htrace : WordTrace (prefixWord ++ tailWord_622432) baseStart_622432 baseEnd_622432 := by
    simpa [prefixWord, tailWord_622432, baseEnd_622432] using wordTrace_append hprefix tailTrace_622432
  have hstable : (prefixWord ++ tailWord_622432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622432).length < 2 ^ (prefixWord ++ tailWord_622432).sum := by decide
  have hdescent : baseEnd_622432 < baseStart_622432 := by decide
  rcases family_descends (prefixWord ++ tailWord_622432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622453 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_622453 : Nat := 118140960795 + 622453 * 2 ^ 59
def prefixEnd_622453 : Nat := 4983230072969 + 3 ^ 40 * 622453 * 2
def baseEnd_622453 : Nat := 284104510073918563088797

theorem tailTrace_622453 : CollatzResearch.WordTrace tailWord_622453 prefixEnd_622453 284104510073918563088797 := by
  unfold tailWord_622453
  simp only [CollatzResearch.WordTrace]
  refine ⟨22702726013966562354016013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15135150675977708236010675 22702726013966562354016013)
  ·
    refine ⟨8513522255237460882756005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22702726013966562354016013 8513522255237460882756005)
    ·
      refine ⟨1596285422857023915516751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8513522255237460882756005 1596285422857023915516751)
      ·
        refine ⟨2394428134285535873275127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596285422857023915516751 2394428134285535873275127)
        ·
          refine ⟨3591642201428303809912691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394428134285535873275127 3591642201428303809912691)
          ·
            refine ⟨5387463302142455714869037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591642201428303809912691 5387463302142455714869037)
            ·
              refine ⟨2020298738303420893075889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5387463302142455714869037 2020298738303420893075889)
              ·
                refine ⟨1515224053727565669806917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020298738303420893075889 1515224053727565669806917)
                ·
                  refine ⟨284104510073918563088797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515224053727565669806917 284104510073918563088797)
                  ·
                    rfl

theorem cell20_622453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_622453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622453 prefixEnd_622453 := by exact prefixLift 622453
  have htrace : WordTrace (prefixWord ++ tailWord_622453) baseStart_622453 baseEnd_622453 := by
    simpa [prefixWord, tailWord_622453, baseEnd_622453] using wordTrace_append hprefix tailTrace_622453
  have hstable : (prefixWord ++ tailWord_622453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622453).length < 2 ^ (prefixWord ++ tailWord_622453).sum := by decide
  have hdescent : baseEnd_622453 < baseStart_622453 := by decide
  rcases family_descends (prefixWord ++ tailWord_622453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622484 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_622484 : Nat := 118140960795 + 622484 * 2 ^ 59
def prefixEnd_622484 : Nat := 4983230072969 + 3 ^ 40 * 622484 * 2
def baseEnd_622484 : Nat := 284118659318620233055337

theorem tailTrace_622484 : CollatzResearch.WordTrace tailWord_622484 prefixEnd_622484 284118659318620233055337 := by
  unfold tailWord_622484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11351928338427127324197253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15135904451236169765596337 11351928338427127324197253)
  ·
    refine ⟨2128486563455086373286985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11351928338427127324197253 2128486563455086373286985)
    ·
      refine ⟨1596364922591314779965239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2128486563455086373286985 1596364922591314779965239)
      ·
        refine ⟨2394547383886972169947859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596364922591314779965239 2394547383886972169947859)
        ·
          refine ⟨3591821075830458254921789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394547383886972169947859 3591821075830458254921789)
          ·
            refine ⟨1346932903436421845595671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3591821075830458254921789 1346932903436421845595671)
            ·
              refine ⟨2020399355154632768393507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346932903436421845595671 2020399355154632768393507)
              ·
                refine ⟨3030599032731949152590261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2020399355154632768393507 3030599032731949152590261)
                ·
                  refine ⟨284118659318620233055337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3030599032731949152590261 284118659318620233055337)
                  ·
                    rfl

theorem cell20_622484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_622484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622484 prefixEnd_622484 := by exact prefixLift 622484
  have htrace : WordTrace (prefixWord ++ tailWord_622484) baseStart_622484 baseEnd_622484 := by
    simpa [prefixWord, tailWord_622484, baseEnd_622484] using wordTrace_append hprefix tailTrace_622484
  have hstable : (prefixWord ++ tailWord_622484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622484).length < 2 ^ (prefixWord ++ tailWord_622484).sum := by decide
  have hdescent : baseEnd_622484 < baseStart_622484 := by decide
  rcases family_descends (prefixWord ++ tailWord_622484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622525 : List Nat := [1, 4, 1, 2, 3, 3, 1, 3, 2]
def baseStart_622525 : Nat := 118140960795 + 622525 * 2 ^ 59
def prefixEnd_622525 : Nat := 4983230072969 + 3 ^ 40 * 622525 * 2
def baseEnd_622525 : Nat := 284137372835806312688503

theorem tailTrace_622525 : CollatzResearch.WordTrace tailWord_622525 prefixEnd_622525 284137372835806312688503 := by
  unfold tailWord_622525
  simp only [CollatzResearch.WordTrace]
  refine ⟨22705352069705718650637029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15136901379803812433758019 22705352069705718650637029)
  ·
    refine ⟨4257253513069822246994443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22705352069705718650637029 4257253513069822246994443)
    ·
      refine ⟨6385880269604733370491665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4257253513069822246994443 6385880269604733370491665)
      ·
        refine ⟨4789410202203550027868749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6385880269604733370491665 4789410202203550027868749)
        ·
          refine ⟨1796028825826331260450781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4789410202203550027868749 1796028825826331260450781)
          ·
            refine ⟨673510809684874222669043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1796028825826331260450781 673510809684874222669043)
            ·
              refine ⟨1010266214527311334003565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673510809684874222669043 1010266214527311334003565)
              ·
                refine ⟨378849830447741750251337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1010266214527311334003565 378849830447741750251337)
                ·
                  refine ⟨284137372835806312688503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378849830447741750251337 284137372835806312688503)
                  ·
                    rfl

theorem cell20_622525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_622525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622525 prefixEnd_622525 := by exact prefixLift 622525
  have htrace : WordTrace (prefixWord ++ tailWord_622525) baseStart_622525 baseEnd_622525 := by
    simpa [prefixWord, tailWord_622525, baseEnd_622525] using wordTrace_append hprefix tailTrace_622525
  have hstable : (prefixWord ++ tailWord_622525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622525).length < 2 ^ (prefixWord ++ tailWord_622525).sum := by decide
  have hdescent : baseEnd_622525 < baseStart_622525 := by decide
  rcases family_descends (prefixWord ++ tailWord_622525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622536 : List Nat := [2, 1, 3, 1, 4, 3, 6]
def baseStart_622536 : Nat := 118140960795 + 622536 * 2 ^ 59
def prefixEnd_622536 : Nat := 4983230072969 + 3 ^ 40 * 622536 * 2
def baseEnd_622536 : Nat := 31571377059504351480199

theorem tailTrace_622536 : CollatzResearch.WordTrace tailWord_622536 prefixEnd_622536 31571377059504351480199 := by
  unfold tailWord_622536
  simp only [CollatzResearch.WordTrace]
  refine ⟨11352876636332933764643731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15137168848443911686191641 11352876636332933764643731)
  ·
    refine ⟨17029314954499400646965597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11352876636332933764643731 17029314954499400646965597)
    ·
      refine ⟨6385993107937275242612099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17029314954499400646965597 6385993107937275242612099)
      ·
        refine ⟨9578989661905912863918149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6385993107937275242612099 9578989661905912863918149)
        ·
          refine ⟨1796060561607358661984653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9578989661905912863918149 1796060561607358661984653)
          ·
            refine ⟨673522710602759498244245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1796060561607358661984653 673522710602759498244245)
            ·
              refine ⟨31571377059504351480199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 673522710602759498244245 31571377059504351480199)
              ·
                rfl

theorem cell20_622536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 6].length) (baseStart_622536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622536 prefixEnd_622536 := by exact prefixLift 622536
  have htrace : WordTrace (prefixWord ++ tailWord_622536) baseStart_622536 baseEnd_622536 := by
    simpa [prefixWord, tailWord_622536, baseEnd_622536] using wordTrace_append hprefix tailTrace_622536
  have hstable : (prefixWord ++ tailWord_622536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622536).length < 2 ^ (prefixWord ++ tailWord_622536).sum := by decide
  have hdescent : baseEnd_622536 < baseStart_622536 := by decide
  rcases family_descends (prefixWord ++ tailWord_622536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622543 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 3]
def baseStart_622543 : Nat := 118140960795 + 622543 * 2 ^ 59
def prefixEnd_622543 : Nat := 4983230072969 + 3 ^ 40 * 622543 * 2
def baseEnd_622543 : Nat := 284145588526278250088429

theorem tailTrace_622543 : CollatzResearch.WordTrace tailWord_622543 prefixEnd_622543 284145588526278250088429 := by
  unfold tailWord_622543
  simp only [CollatzResearch.WordTrace]
  refine ⟨22706008583640507724792283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15137339055760338483194855 22706008583640507724792283)
  ·
    refine ⟨34059012875460761587188425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22706008583640507724792283 34059012875460761587188425)
    ·
      refine ⟨25544259656595571190391319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34059012875460761587188425 25544259656595571190391319)
      ·
        refine ⟨38316389484893356785586979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25544259656595571190391319 38316389484893356785586979)
        ·
          refine ⟨57474584227340035178380469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38316389484893356785586979 57474584227340035178380469)
          ·
            refine ⟨5388242271313128297973169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57474584227340035178380469 5388242271313128297973169)
            ·
              refine ⟨4041181703484846223479877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5388242271313128297973169 4041181703484846223479877)
              ·
                refine ⟨757721569403408666902477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4041181703484846223479877 757721569403408666902477)
                ·
                  refine ⟨284145588526278250088429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757721569403408666902477 284145588526278250088429)
                  ·
                    rfl

theorem cell20_622543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_622543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622543 prefixEnd_622543 := by exact prefixLift 622543
  have htrace : WordTrace (prefixWord ++ tailWord_622543) baseStart_622543 baseEnd_622543 := by
    simpa [prefixWord, tailWord_622543, baseEnd_622543] using wordTrace_append hprefix tailTrace_622543
  have hstable : (prefixWord ++ tailWord_622543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622543).length < 2 ^ (prefixWord ++ tailWord_622543).sum := by decide
  have hdescent : baseEnd_622543 < baseStart_622543 := by decide
  rcases family_descends (prefixWord ++ tailWord_622543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622574 : List Nat := [4, 1, 2, 1, 3, 1, 2, 6]
def baseStart_622574 : Nat := 118140960795 + 622574 * 2 ^ 59
def prefixEnd_622574 : Nat := 4983230072969 + 3 ^ 40 * 622574 * 2
def baseEnd_622574 : Nat := 94719912590326640018323

theorem tailTrace_622574 : CollatzResearch.WordTrace tailWord_622574 prefixEnd_622574 94719912590326640018323 := by
  unfold tailWord_622574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2838392405816025002396347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15138092831018800012780517 2838392405816025002396347)
  ·
    refine ⟨4257588608724037503594521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2838392405816025002396347 4257588608724037503594521)
    ·
      refine ⟨3193191456543028127695891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4257588608724037503594521 3193191456543028127695891)
      ·
        refine ⟨4789787184814542191543837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193191456543028127695891 4789787184814542191543837)
        ·
          refine ⟨1796170194305453321828939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4789787184814542191543837 1796170194305453321828939)
          ·
            refine ⟨2694255291458179982743409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796170194305453321828939 2694255291458179982743409)
            ·
              refine ⟨2020691468593634987057557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2694255291458179982743409 2020691468593634987057557)
              ·
                refine ⟨94719912590326640018323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2020691468593634987057557 94719912590326640018323)
                ·
                  rfl

theorem cell20_622574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_622574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622574 prefixEnd_622574 := by exact prefixLift 622574
  have htrace : WordTrace (prefixWord ++ tailWord_622574) baseStart_622574 baseEnd_622574 := by
    simpa [prefixWord, tailWord_622574, baseEnd_622574] using wordTrace_append hprefix tailTrace_622574
  have hstable : (prefixWord ++ tailWord_622574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622574).length < 2 ^ (prefixWord ++ tailWord_622574).sum := by decide
  have hdescent : baseEnd_622574 < baseStart_622574 := by decide
  rcases family_descends (prefixWord ++ tailWord_622574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622643 : List Nat := [1, 1, 1, 2, 4, 1, 3, 5, 2]
def baseStart_622643 : Nat := 118140960795 + 622643 * 2 ^ 59
def prefixEnd_622643 : Nat := 4983230072969 + 3 ^ 40 * 622643 * 2
def baseEnd_622643 : Nat := 284191231251122346754687

theorem tailTrace_622643 : CollatzResearch.WordTrace tailWord_622643 prefixEnd_622643 284191231251122346754687 := by
  unfold tailWord_622643
  simp only [CollatzResearch.WordTrace]
  refine ⟨22709655883278224803432583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15139770588852149868955055 22709655883278224803432583)
  ·
    refine ⟨34064483824917337205148875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22709655883278224803432583 34064483824917337205148875)
    ·
      refine ⟨51096725737376005807723313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34064483824917337205148875 51096725737376005807723313)
      ·
        refine ⟨38322544303032004355792485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51096725737376005807723313 38322544303032004355792485)
        ·
          refine ⟨7185477056818500816711091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38322544303032004355792485 7185477056818500816711091)
          ·
            refine ⟨10778215585227751225066637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185477056818500816711091 10778215585227751225066637)
            ·
              refine ⟨4041830844460406709399989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10778215585227751225066637 4041830844460406709399989)
              ·
                refine ⟨378921641668163129006249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4041830844460406709399989 378921641668163129006249)
                ·
                  refine ⟨284191231251122346754687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378921641668163129006249 284191231251122346754687)
                  ·
                    rfl

theorem cell20_622643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 2].length) (baseStart_622643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622643 prefixEnd_622643 := by exact prefixLift 622643
  have htrace : WordTrace (prefixWord ++ tailWord_622643) baseStart_622643 baseEnd_622643 := by
    simpa [prefixWord, tailWord_622643, baseEnd_622643] using wordTrace_append hprefix tailTrace_622643
  have hstable : (prefixWord ++ tailWord_622643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622643).length < 2 ^ (prefixWord ++ tailWord_622643).sum := by decide
  have hdescent : baseEnd_622643 < baseStart_622643 := by decide
  rcases family_descends (prefixWord ++ tailWord_622643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622688 : List Nat := [2, 1, 1, 3, 2, 3, 4, 4]
def baseStart_622688 : Nat := 118140960795 + 622688 * 2 ^ 59
def prefixEnd_622688 : Nat := 4983230072969 + 3 ^ 40 * 622688 * 2
def baseEnd_622688 : Nat := 94737256825767396751501

theorem tailTrace_622688 : CollatzResearch.WordTrace tailWord_622688 prefixEnd_622688 94737256825767396751501 := by
  unfold tailWord_622688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11355648584057598744410359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15140864778743464992547145 11355648584057598744410359)
  ·
    refine ⟨17033472876086398116615539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11355648584057598744410359 17033472876086398116615539)
    ·
      refine ⟨25550209314129597174923309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17033472876086398116615539 25550209314129597174923309)
      ·
        refine ⟨9581328492798598940596241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25550209314129597174923309 9581328492798598940596241)
        ·
          refine ⟨7185996369598949205447181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9581328492798598940596241 7185996369598949205447181)
          ·
            refine ⟨2694748638599605952042693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7185996369598949205447181 2694748638599605952042693)
            ·
              refine ⟨505265369737426116008005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2694748638599605952042693 505265369737426116008005)
              ·
                refine ⟨94737256825767396751501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 505265369737426116008005 94737256825767396751501)
                ·
                  rfl

theorem cell20_622688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_622688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622688 prefixEnd_622688 := by exact prefixLift 622688
  have htrace : WordTrace (prefixWord ++ tailWord_622688) baseStart_622688 baseEnd_622688 := by
    simpa [prefixWord, tailWord_622688, baseEnd_622688] using wordTrace_append hprefix tailTrace_622688
  have hstable : (prefixWord ++ tailWord_622688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622688).length < 2 ^ (prefixWord ++ tailWord_622688).sum := by decide
  have hdescent : baseEnd_622688 < baseStart_622688 := by decide
  rcases family_descends (prefixWord ++ tailWord_622688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622757 : List Nat := [1, 3, 1, 2, 1, 3, 2, 5, 2]
def baseStart_622757 : Nat := 118140960795 + 622757 * 2 ^ 59
def prefixEnd_622757 : Nat := 4983230072969 + 3 ^ 40 * 622757 * 2
def baseEnd_622757 : Nat := 284243263957444616954221

theorem tailTrace_622757 : CollatzResearch.WordTrace tailWord_622757 prefixEnd_622757 284243263957444616954221 := by
  unfold tailWord_622757
  simp only [CollatzResearch.WordTrace]
  refine ⟨22713813804865222273082525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15142542536576814848721683 22713813804865222273082525)
  ·
    refine ⟨8517680176824458352405947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22713813804865222273082525 8517680176824458352405947)
    ·
      refine ⟨12776520265236687528608921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8517680176824458352405947 12776520265236687528608921)
      ·
        refine ⟨9582390198927515646456691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12776520265236687528608921 9582390198927515646456691)
        ·
          refine ⟨14373585298391273469685037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9582390198927515646456691 14373585298391273469685037)
          ·
            refine ⟨5390094486896727551131889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14373585298391273469685037 5390094486896727551131889)
            ·
              refine ⟨4042570865172545663348917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5390094486896727551131889 4042570865172545663348917)
              ·
                refine ⟨378991018609926155938961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4042570865172545663348917 378991018609926155938961)
                ·
                  refine ⟨284243263957444616954221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378991018609926155938961 284243263957444616954221)
                  ·
                    rfl

theorem cell20_622757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_622757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622757 prefixEnd_622757 := by exact prefixLift 622757
  have htrace : WordTrace (prefixWord ++ tailWord_622757) baseStart_622757 baseEnd_622757 := by
    simpa [prefixWord, tailWord_622757, baseEnd_622757] using wordTrace_append hprefix tailTrace_622757
  have hstable : (prefixWord ++ tailWord_622757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622757).length < 2 ^ (prefixWord ++ tailWord_622757).sum := by decide
  have hdescent : baseEnd_622757 < baseStart_622757 := by decide
  rcases family_descends (prefixWord ++ tailWord_622757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622766 : List Nat := [4, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_622766 : Nat := 118140960795 + 622766 * 2 ^ 59
def prefixEnd_622766 : Nat := 4983230072969 + 3 ^ 40 * 622766 * 2
def baseEnd_622766 : Nat := 284247371802680585654185

theorem tailTrace_622766 : CollatzResearch.WordTrace tailWord_622766 prefixEnd_622766 284247371802680585654185 := by
  unfold tailWord_622766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839267757729077101270019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15142761374555077873440101 2839267757729077101270019)
  ·
    refine ⟨4258901636593615651905029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2839267757729077101270019 4258901636593615651905029)
    ·
      refine ⟨798544056861302934732193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4258901636593615651905029 798544056861302934732193)
      ·
        refine ⟨598908042645977201049145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 798544056861302934732193 598908042645977201049145)
        ·
          refine ⟨449181031984482900786859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598908042645977201049145 449181031984482900786859)
          ·
            refine ⟨673771547976724351180289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449181031984482900786859 673771547976724351180289)
            ·
              refine ⟨505328660982543263385217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673771547976724351180289 505328660982543263385217)
              ·
                refine ⟨378996495736907447538913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505328660982543263385217 378996495736907447538913)
                ·
                  refine ⟨284247371802680585654185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378996495736907447538913 284247371802680585654185)
                  ·
                    rfl

theorem cell20_622766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_622766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622766 prefixEnd_622766 := by exact prefixLift 622766
  have htrace : WordTrace (prefixWord ++ tailWord_622766) baseStart_622766 baseEnd_622766 := by
    simpa [prefixWord, tailWord_622766, baseEnd_622766] using wordTrace_append hprefix tailTrace_622766
  have hstable : (prefixWord ++ tailWord_622766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622766).length < 2 ^ (prefixWord ++ tailWord_622766).sum := by decide
  have hdescent : baseEnd_622766 < baseStart_622766 := by decide
  rcases family_descends (prefixWord ++ tailWord_622766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622788 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_622788 : Nat := 118140960795 + 622788 * 2 ^ 59
def prefixEnd_622788 : Nat := 4983230072969 + 3 ^ 40 * 622788 * 2
def baseEnd_622788 : Nat := 284257413202146286920761

theorem tailTrace_622788 : CollatzResearch.WordTrace tailWord_622788 prefixEnd_622788 284257413202146286920761 := by
  unfold tailWord_622788
  simp only [CollatzResearch.WordTrace]
  refine ⟨11357472233876457283730509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15143296311835276378307345 11357472233876457283730509)
  ·
    refine ⟨4259052087703671481398941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11357472233876457283730509 4259052087703671481398941)
    ·
      refine ⟨1597144532888876805524603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4259052087703671481398941 1597144532888876805524603)
      ·
        refine ⟨2395716799333315208286905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1597144532888876805524603 2395716799333315208286905)
        ·
          refine ⟨1796787599499986406215179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2395716799333315208286905 1796787599499986406215179)
          ·
            refine ⟨2695181399249979609322769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796787599499986406215179 2695181399249979609322769)
            ·
              refine ⟨2021386049437484706992077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2695181399249979609322769 2021386049437484706992077)
              ·
                refine ⟨758019768539056765122029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2021386049437484706992077 758019768539056765122029)
                ·
                  refine ⟨284257413202146286920761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758019768539056765122029 284257413202146286920761)
                  ·
                    rfl

theorem cell20_622788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_622788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622788 prefixEnd_622788 := by exact prefixLift 622788
  have htrace : WordTrace (prefixWord ++ tailWord_622788) baseStart_622788 baseEnd_622788 := by
    simpa [prefixWord, tailWord_622788, baseEnd_622788] using wordTrace_append hprefix tailTrace_622788
  have hstable : (prefixWord ++ tailWord_622788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622788).length < 2 ^ (prefixWord ++ tailWord_622788).sum := by decide
  have hdescent : baseEnd_622788 < baseStart_622788 := by decide
  rcases family_descends (prefixWord ++ tailWord_622788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622792 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_622792 : Nat := 118140960795 + 622792 * 2 ^ 59
def prefixEnd_622792 : Nat := 4983230072969 + 3 ^ 40 * 622792 * 2
def baseEnd_622792 : Nat := 284259238911140050787411

theorem tailTrace_622792 : CollatzResearch.WordTrace tailWord_622792 prefixEnd_622792 284259238911140050787411 := by
  unfold tailWord_622792
  simp only [CollatzResearch.WordTrace]
  refine ⟨11357545179869211625303315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15143393573158948833737753 11357545179869211625303315)
  ·
    refine ⟨17036317769803817437954973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11357545179869211625303315 17036317769803817437954973)
    ·
      refine ⟨6388619163676431539233115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17036317769803817437954973 6388619163676431539233115)
      ·
        refine ⟨9582928745514647308849673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6388619163676431539233115 9582928745514647308849673)
        ·
          refine ⟨7187196559135985481637255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9582928745514647308849673 7187196559135985481637255)
          ·
            refine ⟨10780794838703978222455883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187196559135985481637255 10780794838703978222455883)
            ·
              refine ⟨16171192258055967333683825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10780794838703978222455883 16171192258055967333683825)
              ·
                refine ⟨12128394193541975500262869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16171192258055967333683825 12128394193541975500262869)
                ·
                  refine ⟨284259238911140050787411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12128394193541975500262869 284259238911140050787411)
                  ·
                    rfl

theorem cell20_622792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_622792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622792 prefixEnd_622792 := by exact prefixLift 622792
  have htrace : WordTrace (prefixWord ++ tailWord_622792) baseStart_622792 baseEnd_622792 := by
    simpa [prefixWord, tailWord_622792, baseEnd_622792] using wordTrace_append hprefix tailTrace_622792
  have hstable : (prefixWord ++ tailWord_622792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622792).length < 2 ^ (prefixWord ++ tailWord_622792).sum := by decide
  have hdescent : baseEnd_622792 < baseStart_622792 := by decide
  rcases family_descends (prefixWord ++ tailWord_622792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622818 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_622818 : Nat := 118140960795 + 622818 * 2 ^ 59
def prefixEnd_622818 : Nat := 4983230072969 + 3 ^ 40 * 622818 * 2
def baseEnd_622818 : Nat := 284271106019599515920639

theorem tailTrace_622818 : CollatzResearch.WordTrace tailWord_622818 prefixEnd_622818 284271106019599515920639 := by
  unfold tailWord_622818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5679009664411057422763277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15144025771762819794035405 5679009664411057422763277)
  ·
    refine ⟨2129628624154146533536229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5679009664411057422763277 2129628624154146533536229)
    ·
      refine ⟨399305367028902475038043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2129628624154146533536229 399305367028902475038043)
      ·
        refine ⟨598958050543353712557065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399305367028902475038043 598958050543353712557065)
        ·
          refine ⟨449218537907515284417799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598958050543353712557065 449218537907515284417799)
          ·
            refine ⟨673827806861272926626699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449218537907515284417799 673827806861272926626699)
            ·
              refine ⟨1010741710291909389940049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673827806861272926626699 1010741710291909389940049)
              ·
                refine ⟨758056282718932042455037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010741710291909389940049 758056282718932042455037)
                ·
                  refine ⟨284271106019599515920639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758056282718932042455037 284271106019599515920639)
                  ·
                    rfl

theorem cell20_622818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_622818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622818 prefixEnd_622818 := by exact prefixLift 622818
  have htrace : WordTrace (prefixWord ++ tailWord_622818) baseStart_622818 baseEnd_622818 := by
    simpa [prefixWord, tailWord_622818, baseEnd_622818] using wordTrace_append hprefix tailTrace_622818
  have hstable : (prefixWord ++ tailWord_622818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622818).length < 2 ^ (prefixWord ++ tailWord_622818).sum := by decide
  have hdescent : baseEnd_622818 < baseStart_622818 := by decide
  rcases family_descends (prefixWord ++ tailWord_622818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622833 : List Nat := [1, 2, 2, 2, 2, 1, 4, 4, 2]
def baseStart_622833 : Nat := 118140960795 + 622833 * 2 ^ 59
def prefixEnd_622833 : Nat := 4983230072969 + 3 ^ 40 * 622833 * 2
def baseEnd_622833 : Nat := 284277952428326130420577

theorem tailTrace_622833 : CollatzResearch.WordTrace tailWord_622833 prefixEnd_622833 284277952428326130420577 := by
  unfold tailWord_622833
  simp only [CollatzResearch.WordTrace]
  refine ⟨22716585752589887252849153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15144390501726591501899435 22716585752589887252849153)
  ·
    refine ⟨17037439314442415439636865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22716585752589887252849153 17037439314442415439636865)
    ·
      refine ⟨12778079485831811579727649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17037439314442415439636865 12778079485831811579727649)
      ·
        refine ⟨9583559614373858684795737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12778079485831811579727649 9583559614373858684795737)
        ·
          refine ⟨7187669710780394013596803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9583559614373858684795737 7187669710780394013596803)
          ·
            refine ⟨10781504566170591020395205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187669710780394013596803 10781504566170591020395205)
            ·
              refine ⟨2021532106156985816324101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10781504566170591020395205 2021532106156985816324101)
              ·
                refine ⟨379037269904434840560769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2021532106156985816324101 379037269904434840560769)
                ·
                  refine ⟨284277952428326130420577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379037269904434840560769 284277952428326130420577)
                  ·
                    rfl

theorem cell20_622833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_622833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622833 prefixEnd_622833 := by exact prefixLift 622833
  have htrace : WordTrace (prefixWord ++ tailWord_622833) baseStart_622833 baseEnd_622833 := by
    simpa [prefixWord, tailWord_622833, baseEnd_622833] using wordTrace_append hprefix tailTrace_622833
  have hstable : (prefixWord ++ tailWord_622833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622833).length < 2 ^ (prefixWord ++ tailWord_622833).sum := by decide
  have hdescent : baseEnd_622833 < baseStart_622833 := by decide
  rcases family_descends (prefixWord ++ tailWord_622833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622875 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_622875 : Nat := 118140960795 + 622875 * 2 ^ 59
def prefixEnd_622875 : Nat := 4983230072969 + 3 ^ 40 * 622875 * 2
def baseEnd_622875 : Nat := 284297122372760651020405

theorem tailTrace_622875 : CollatzResearch.WordTrace tailWord_622875 prefixEnd_622875 284297122372760651020405 := by
  unfold tailWord_622875
  simp only [CollatzResearch.WordTrace]
  refine ⟨22718117618437728425878079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15145411745625152283918719 22718117618437728425878079)
  ·
    refine ⟨34077176427656592638817119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22718117618437728425878079 34077176427656592638817119)
    ·
      refine ⟨51115764641484888958225679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34077176427656592638817119 51115764641484888958225679)
      ·
        refine ⟨76673646962227333437338519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51115764641484888958225679 76673646962227333437338519)
        ·
          refine ⟨115010470443341000156007779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76673646962227333437338519 115010470443341000156007779)
          ·
            refine ⟨172515705665011500234011669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115010470443341000156007779 172515705665011500234011669)
            ·
              refine ⟨8086673703047414073469297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 172515705665011500234011669 8086673703047414073469297)
              ·
                refine ⟨6065005277285560555101973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8086673703047414073469297 6065005277285560555101973)
                ·
                  refine ⟨284297122372760651020405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6065005277285560555101973 284297122372760651020405)
                  ·
                    rfl

theorem cell20_622875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_622875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622875 prefixEnd_622875 := by exact prefixLift 622875
  have htrace : WordTrace (prefixWord ++ tailWord_622875) baseStart_622875 baseEnd_622875 := by
    simpa [prefixWord, tailWord_622875, baseEnd_622875] using wordTrace_append hprefix tailTrace_622875
  have hstable : (prefixWord ++ tailWord_622875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622875).length < 2 ^ (prefixWord ++ tailWord_622875).sum := by decide
  have hdescent : baseEnd_622875 < baseStart_622875 := by decide
  rcases family_descends (prefixWord ++ tailWord_622875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622888 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 4]
def baseStart_622888 : Nat := 118140960795 + 622888 * 2 ^ 59
def prefixEnd_622888 : Nat := 4983230072969 + 3 ^ 40 * 622888 * 2
def baseEnd_622888 : Nat := 284303055926990383587019

theorem tailTrace_622888 : CollatzResearch.WordTrace tailWord_622888 prefixEnd_622888 284303055926990383587019 := by
  unfold tailWord_622888
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359295883695315823050659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15145727844927087764067545 11359295883695315823050659)
  ·
    refine ⟨17038943825542973734575989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11359295883695315823050659 17038943825542973734575989)
    ·
      refine ⟨1597400983644653787616499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17038943825542973734575989 1597400983644653787616499)
      ·
        refine ⟨2396101475466980681424749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1597400983644653787616499 2396101475466980681424749)
        ·
          refine ⟨898538053300117755534281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2396101475466980681424749 898538053300117755534281)
          ·
            refine ⟨673903539975088316650711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898538053300117755534281 673903539975088316650711)
            ·
              refine ⟨1010855309962632474976067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673903539975088316650711 1010855309962632474976067)
              ·
                refine ⟨1516282964943948712464101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010855309962632474976067 1516282964943948712464101)
                ·
                  refine ⟨284303055926990383587019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516282964943948712464101 284303055926990383587019)
                  ·
                    rfl

theorem cell20_622888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_622888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622888 prefixEnd_622888 := by exact prefixLift 622888
  have htrace : WordTrace (prefixWord ++ tailWord_622888) baseStart_622888 baseEnd_622888 := by
    simpa [prefixWord, tailWord_622888, baseEnd_622888] using wordTrace_append hprefix tailTrace_622888
  have hstable : (prefixWord ++ tailWord_622888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622888).length < 2 ^ (prefixWord ++ tailWord_622888).sum := by decide
  have hdescent : baseEnd_622888 < baseStart_622888 := by decide
  rcases family_descends (prefixWord ++ tailWord_622888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622892 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_622892 : Nat := 118140960795 + 622892 * 2 ^ 59
def prefixEnd_622892 : Nat := 4983230072969 + 3 ^ 40 * 622892 * 2
def baseEnd_622892 : Nat := 284304881635984147453669

theorem tailTrace_622892 : CollatzResearch.WordTrace tailWord_622892 prefixEnd_622892 284304881635984147453669 := by
  unfold tailWord_622892
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359368829688070164623465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15145825106250760219497953 11359368829688070164623465)
  ·
    refine ⟨8519526622266052623467599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11359368829688070164623465 8519526622266052623467599)
    ·
      refine ⟨12779289933399078935201399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8519526622266052623467599 12779289933399078935201399)
      ·
        refine ⟨19168934900098618402802099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12779289933399078935201399 19168934900098618402802099)
        ·
          refine ⟨28753402350147927604203149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19168934900098618402802099 28753402350147927604203149)
          ·
            refine ⟨10782525881305472851576181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28753402350147927604203149 10782525881305472851576181)
            ·
              refine ⟨1010861801372388079835267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10782525881305472851576181 1010861801372388079835267)
              ·
                refine ⟨1516292702058582119752901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010861801372388079835267 1516292702058582119752901)
                ·
                  refine ⟨284304881635984147453669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516292702058582119752901 284304881635984147453669)
                  ·
                    rfl

theorem cell20_622892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_622892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622892 prefixEnd_622892 := by exact prefixLift 622892
  have htrace : WordTrace (prefixWord ++ tailWord_622892) baseStart_622892 baseEnd_622892 := by
    simpa [prefixWord, tailWord_622892, baseEnd_622892] using wordTrace_append hprefix tailTrace_622892
  have hstable : (prefixWord ++ tailWord_622892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622892).length < 2 ^ (prefixWord ++ tailWord_622892).sum := by decide
  have hdescent : baseEnd_622892 < baseStart_622892 := by decide
  rcases family_descends (prefixWord ++ tailWord_622892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622898 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_622898 : Nat := 118140960795 + 622898 * 2 ^ 59
def prefixEnd_622898 : Nat := 4983230072969 + 3 ^ 40 * 622898 * 2
def baseEnd_622898 : Nat := 284307620199474793253645

theorem tailTrace_622898 : CollatzResearch.WordTrace tailWord_622898 prefixEnd_622898 284307620199474793253645 := by
  unfold tailWord_622898
  simp only [CollatzResearch.WordTrace]
  refine ⟨5679739124338600838491337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15145970998236268902643565 5679739124338600838491337)
  ·
    refine ⟨4259804343253950628868503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5679739124338600838491337 4259804343253950628868503)
    ·
      refine ⟨6389706514880925943302755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4259804343253950628868503 6389706514880925943302755)
      ·
        refine ⟨9584559772321388914954133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6389706514880925943302755 9584559772321388914954133)
        ·
          refine ⟨449276239327565105388475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9584559772321388914954133 449276239327565105388475)
          ·
            refine ⟨673914358991347658082713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449276239327565105388475 673914358991347658082713)
            ·
              refine ⟨505435769243510743562035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673914358991347658082713 505435769243510743562035)
              ·
                refine ⟨758153653865266115343053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505435769243510743562035 758153653865266115343053)
                ·
                  refine ⟨284307620199474793253645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758153653865266115343053 284307620199474793253645)
                  ·
                    rfl

theorem cell20_622898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_622898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622898 prefixEnd_622898 := by exact prefixLift 622898
  have htrace : WordTrace (prefixWord ++ tailWord_622898) baseStart_622898 baseEnd_622898 := by
    simpa [prefixWord, tailWord_622898, baseEnd_622898] using wordTrace_append hprefix tailTrace_622898
  have hstable : (prefixWord ++ tailWord_622898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622898).length < 2 ^ (prefixWord ++ tailWord_622898).sum := by decide
  have hdescent : baseEnd_622898 < baseStart_622898 := by decide
  rcases family_descends (prefixWord ++ tailWord_622898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622899 : List Nat := [1, 1, 1, 2, 5, 1, 4, 5]
def baseStart_622899 : Nat := 118140960795 + 622899 * 2 ^ 59
def prefixEnd_622899 : Nat := 4983230072969 + 3 ^ 40 * 622899 * 2
def baseEnd_622899 : Nat := 94769358875574411406769

theorem tailTrace_622899 : CollatzResearch.WordTrace tailWord_622899 prefixEnd_622899 94769358875574411406769 := by
  unfold tailWord_622899
  simp only [CollatzResearch.WordTrace]
  refine ⟨22718992970350780524751751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15145995313567187016501167 22718992970350780524751751)
  ·
    refine ⟨34078489455526170787127627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22718992970350780524751751 34078489455526170787127627)
    ·
      refine ⟨51117734183289256180691441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34078489455526170787127627 51117734183289256180691441)
      ·
        refine ⟨38338300637466942135518581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51117734183289256180691441 38338300637466942135518581)
        ·
          refine ⟨3594215684762525825204867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38338300637466942135518581 3594215684762525825204867)
          ·
            refine ⟨5391323527143788737807301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594215684762525825204867 5391323527143788737807301)
            ·
              refine ⟨1010873161339460388338869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5391323527143788737807301 1010873161339460388338869)
              ·
                refine ⟨94769358875574411406769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1010873161339460388338869 94769358875574411406769)
                ·
                  rfl

theorem cell20_622899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_622899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622899 prefixEnd_622899 := by exact prefixLift 622899
  have htrace : WordTrace (prefixWord ++ tailWord_622899) baseStart_622899 baseEnd_622899 := by
    simpa [prefixWord, tailWord_622899, baseEnd_622899] using wordTrace_append hprefix tailTrace_622899
  have hstable : (prefixWord ++ tailWord_622899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622899).length < 2 ^ (prefixWord ++ tailWord_622899).sum := by decide
  have hdescent : baseEnd_622899 < baseStart_622899 := by decide
  rcases family_descends (prefixWord ++ tailWord_622899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622947 : List Nat := [1, 1, 1, 5, 2, 1, 3, 4, 2]
def baseStart_622947 : Nat := 118140960795 + 622947 * 2 ^ 59
def prefixEnd_622947 : Nat := 4983230072969 + 3 ^ 40 * 622947 * 2
def baseEnd_622947 : Nat := 284329985134648400620111

theorem tailTrace_622947 : CollatzResearch.WordTrace tailWord_622947 prefixEnd_622947 284329985134648400620111 := by
  unfold tailWord_622947
  simp only [CollatzResearch.WordTrace]
  refine ⟨22720743674176884722499095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15147162449451256481666063 22720743674176884722499095)
  ·
    refine ⟨34081115511265327083748643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22720743674176884722499095 34081115511265327083748643)
    ·
      refine ⟨51121673266897990625622965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34081115511265327083748643 51121673266897990625622965)
      ·
        refine ⟨4792656868771686621152153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51121673266897990625622965 4792656868771686621152153)
        ·
          refine ⟨3594492651578764965864115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4792656868771686621152153 3594492651578764965864115)
          ·
            refine ⟨5391738977368147448796173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594492651578764965864115 5391738977368147448796173)
            ·
              refine ⟨2021902116513055293298565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5391738977368147448796173 2021902116513055293298565)
              ·
                refine ⟨379106646846197867493481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2021902116513055293298565 379106646846197867493481)
                ·
                  refine ⟨284329985134648400620111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379106646846197867493481 284329985134648400620111)
                  ·
                    rfl

theorem cell20_622947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 2].length) (baseStart_622947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622947 prefixEnd_622947 := by exact prefixLift 622947
  have htrace : WordTrace (prefixWord ++ tailWord_622947) baseStart_622947 baseEnd_622947 := by
    simpa [prefixWord, tailWord_622947, baseEnd_622947] using wordTrace_append hprefix tailTrace_622947
  have hstable : (prefixWord ++ tailWord_622947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622947).length < 2 ^ (prefixWord ++ tailWord_622947).sum := by decide
  have hdescent : baseEnd_622947 < baseStart_622947 := by decide
  rcases family_descends (prefixWord ++ tailWord_622947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622954 : List Nat := [3, 1, 3, 3, 1, 1, 3, 5]
def baseStart_622954 : Nat := 118140960795 + 622954 * 2 ^ 59
def prefixEnd_622954 : Nat := 4983230072969 + 3 ^ 40 * 622954 * 2
def baseEnd_622954 : Nat := 94777726708462495795583

theorem tailTrace_622954 : CollatzResearch.WordTrace tailWord_622954 prefixEnd_622954 94777726708462495795583 := by
  unfold tailWord_622954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5680249746287881229500979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15147332656767683278669277 5680249746287881229500979)
  ·
    refine ⟨8520374619431821844251469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5680249746287881229500979 8520374619431821844251469)
    ·
      refine ⟨3195140482286933191594301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8520374619431821844251469 3195140482286933191594301)
      ·
        refine ⟨1198177680857599946847863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3195140482286933191594301 1198177680857599946847863)
        ·
          refine ⟨1797266521286399920271795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198177680857599946847863 1797266521286399920271795)
          ·
            refine ⟨2695899781929599880407693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797266521286399920271795 2695899781929599880407693)
            ·
              refine ⟨1010962418223599955152885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2695899781929599880407693 1010962418223599955152885)
              ·
                refine ⟨94777726708462495795583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1010962418223599955152885 94777726708462495795583)
                ·
                  rfl

theorem cell20_622954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_622954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622954 prefixEnd_622954 := by exact prefixLift 622954
  have htrace : WordTrace (prefixWord ++ tailWord_622954) baseStart_622954 baseEnd_622954 := by
    simpa [prefixWord, tailWord_622954, baseEnd_622954] using wordTrace_append hprefix tailTrace_622954
  have hstable : (prefixWord ++ tailWord_622954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622954).length < 2 ^ (prefixWord ++ tailWord_622954).sum := by decide
  have hdescent : baseEnd_622954 < baseStart_622954 := by decide
  rcases family_descends (prefixWord ++ tailWord_622954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622985 : List Nat := [1, 2, 1, 1, 6, 1, 1, 5, 2]
def baseStart_622985 : Nat := 118140960795 + 622985 * 2 ^ 59
def prefixEnd_622985 : Nat := 4983230072969 + 3 ^ 40 * 622985 * 2
def baseEnd_622985 : Nat := 284347329370089157353289

theorem tailTrace_622985 : CollatzResearch.WordTrace tailWord_622985 prefixEnd_622985 284347329370089157353289 := by
  unfold tailWord_622985
  simp only [CollatzResearch.WordTrace]
  refine ⟨22722129648039217212382409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15148086432026144808254939 22722129648039217212382409)
  ·
    refine ⟨17041597236029412909286807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22722129648039217212382409 17041597236029412909286807)
    ·
      refine ⟨25562395854044119363930211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17041597236029412909286807 25562395854044119363930211)
      ·
        refine ⟨38343593781066179045895317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25562395854044119363930211 38343593781066179045895317)
        ·
          refine ⟨1797355958487477142776343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38343593781066179045895317 1797355958487477142776343)
          ·
            refine ⟨2696033937731215714164515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797355958487477142776343 2696033937731215714164515)
            ·
              refine ⟨4044050906596823571246773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2696033937731215714164515 4044050906596823571246773)
              ·
                refine ⟨379129772493452209804385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4044050906596823571246773 379129772493452209804385)
                ·
                  refine ⟨284347329370089157353289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379129772493452209804385 284347329370089157353289)
                  ·
                    rfl

theorem cell20_622985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_622985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622985 prefixEnd_622985 := by exact prefixLift 622985
  have htrace : WordTrace (prefixWord ++ tailWord_622985) baseStart_622985 baseEnd_622985 := by
    simpa [prefixWord, tailWord_622985, baseEnd_622985] using wordTrace_append hprefix tailTrace_622985
  have hstable : (prefixWord ++ tailWord_622985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622985).length < 2 ^ (prefixWord ++ tailWord_622985).sum := by decide
  have hdescent : baseEnd_622985 < baseStart_622985 := by decide
  rcases family_descends (prefixWord ++ tailWord_622985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622998 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_622998 : Nat := 118140960795 + 622998 * 2 ^ 59
def prefixEnd_622998 : Nat := 4983230072969 + 3 ^ 40 * 622998 * 2
def baseEnd_622998 : Nat := 284353262924318889919903

theorem tailTrace_622998 : CollatzResearch.WordTrace tailWord_622998 prefixEnd_622998 284353262924318889919903 := by
  unfold tailWord_622998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1420162737312007527037853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15148402531328080288403765 1420162737312007527037853)
  ·
    refine ⟨532561026492002822639195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1420162737312007527037853 532561026492002822639195)
    ·
      refine ⟨798841539738004233958793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 532561026492002822639195 798841539738004233958793)
      ·
        refine ⟨599131154803503175469095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 798841539738004233958793 599131154803503175469095)
        ·
          refine ⟨898696732205254763203643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599131154803503175469095 898696732205254763203643)
          ·
            refine ⟨1348045098307882144805465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898696732205254763203643 1348045098307882144805465)
            ·
              refine ⟨1011033823730911608604099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348045098307882144805465 1011033823730911608604099)
              ·
                refine ⟨1516550735596367412906149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011033823730911608604099 1516550735596367412906149)
                ·
                  refine ⟨284353262924318889919903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516550735596367412906149 284353262924318889919903)
                  ·
                    rfl

theorem cell20_622998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_622998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622998 prefixEnd_622998 := by exact prefixLift 622998
  have htrace : WordTrace (prefixWord ++ tailWord_622998) baseStart_622998 baseEnd_622998 := by
    simpa [prefixWord, tailWord_622998, baseEnd_622998] using wordTrace_append hprefix tailTrace_622998
  have hstable : (prefixWord ++ tailWord_622998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622998).length < 2 ^ (prefixWord ++ tailWord_622998).sum := by decide
  have hdescent : baseEnd_622998 < baseStart_622998 := by decide
  rcases family_descends (prefixWord ++ tailWord_622998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622999 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 3]
def baseStart_622999 : Nat := 118140960795 + 622999 * 2 ^ 59
def prefixEnd_622999 : Nat := 4983230072969 + 3 ^ 40 * 622999 * 2
def baseEnd_622999 : Nat := 284353719351567330886565

theorem tailTrace_622999 : CollatzResearch.WordTrace tailWord_622999 prefixEnd_622999 284353719351567330886565 := by
  unfold tailWord_622999
  simp only [CollatzResearch.WordTrace]
  refine ⟨22722640269988497603392051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15148426846658998402261367 22722640269988497603392051)
  ·
    refine ⟨34083960404982746405088077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22722640269988497603392051 34083960404982746405088077)
    ·
      refine ⟨12781485151868529901908029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34083960404982746405088077 12781485151868529901908029)
      ·
        refine ⟨4793056931950698713215511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12781485151868529901908029 4793056931950698713215511)
        ·
          refine ⟨7189585397926048069823267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4793056931950698713215511 7189585397926048069823267)
          ·
            refine ⟨10784378096889072104734901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7189585397926048069823267 10784378096889072104734901)
            ·
              refine ⟨1011035446583350509818897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10784378096889072104734901 1011035446583350509818897)
              ·
                refine ⟨758276584937512882364173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011035446583350509818897 758276584937512882364173)
                ·
                  refine ⟨284353719351567330886565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758276584937512882364173 284353719351567330886565)
                  ·
                    rfl

theorem cell20_622999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_622999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_622999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_622999 prefixEnd_622999 := by exact prefixLift 622999
  have htrace : WordTrace (prefixWord ++ tailWord_622999) baseStart_622999 baseEnd_622999 := by
    simpa [prefixWord, tailWord_622999, baseEnd_622999] using wordTrace_append hprefix tailTrace_622999
  have hstable : (prefixWord ++ tailWord_622999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622999).length < 2 ^ (prefixWord ++ tailWord_622999).sum := by decide
  have hdescent : baseEnd_622999 < baseStart_622999 := by decide
  rcases family_descends (prefixWord ++ tailWord_622999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623061 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 4]
def baseStart_623061 : Nat := 118140960795 + 623061 * 2 ^ 59
def prefixEnd_623061 : Nat := 4983230072969 + 3 ^ 40 * 623061 * 2
def baseEnd_623061 : Nat := 284382017840970670819645

theorem tailTrace_623061 : CollatzResearch.WordTrace tailWord_623061 prefixEnd_623061 284382017840970670819645 := by
  unfold tailWord_623061
  simp only [CollatzResearch.WordTrace]
  refine ⟨22724901595763882192149037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15149934397175921461432691 22724901595763882192149037)
  ·
    refine ⟨8521838098411455822055889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22724901595763882192149037 8521838098411455822055889)
    ·
      refine ⟨6391378573808591866541917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8521838098411455822055889 6391378573808591866541917)
      ·
        refine ⟨2396766965178221949953219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6391378573808591866541917 2396766965178221949953219)
        ·
          refine ⟨3595150447767332924929829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2396766965178221949953219 3595150447767332924929829)
          ·
            refine ⟨674090708956374923424343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3595150447767332924929829 674090708956374923424343)
            ·
              refine ⟨1011136063434562385136515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674090708956374923424343 1011136063434562385136515)
              ·
                refine ⟨1516704095151843577704773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011136063434562385136515 1516704095151843577704773)
                ·
                  refine ⟨284382017840970670819645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516704095151843577704773 284382017840970670819645)
                  ·
                    rfl

theorem cell20_623061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_623061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623061 prefixEnd_623061 := by exact prefixLift 623061
  have htrace : WordTrace (prefixWord ++ tailWord_623061) baseStart_623061 baseEnd_623061 := by
    simpa [prefixWord, tailWord_623061, baseEnd_623061] using wordTrace_append hprefix tailTrace_623061
  have hstable : (prefixWord ++ tailWord_623061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623061).length < 2 ^ (prefixWord ++ tailWord_623061).sum := by decide
  have hdescent : baseEnd_623061 < baseStart_623061 := by decide
  rcases family_descends (prefixWord ++ tailWord_623061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623106 : List Nat := [3, 4, 1, 2, 2, 8]
def baseStart_623106 : Nat := 118140960795 + 623106 * 2 ^ 59
def prefixEnd_623106 : Nat := 4983230072969 + 3 ^ 40 * 623106 * 2
def baseEnd_623106 : Nat := 10533428039524093122943

theorem tailTrace_623106 : CollatzResearch.WordTrace tailWord_623106 prefixEnd_623106 10533428039524093122943 := by
  unfold tailWord_623106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681635720150213719384293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15151028587067236585024781 5681635720150213719384293)
  ·
    refine ⟨1065306697528165072384555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5681635720150213719384293 1065306697528165072384555)
    ·
      refine ⟨1597960046292247608576833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1065306697528165072384555 1597960046292247608576833)
      ·
        refine ⟨1198470034719185706432625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1597960046292247608576833 1198470034719185706432625)
        ·
          refine ⟨898852526039389279824469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1198470034719185706432625 898852526039389279824469)
          ·
            refine ⟨10533428039524093122943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 898852526039389279824469 10533428039524093122943)
            ·
              rfl

theorem cell20_623106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 8].length) (baseStart_623106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623106 prefixEnd_623106 := by exact prefixLift 623106
  have htrace : WordTrace (prefixWord ++ tailWord_623106) baseStart_623106 baseEnd_623106 := by
    simpa [prefixWord, tailWord_623106, baseEnd_623106] using wordTrace_append hprefix tailTrace_623106
  have hstable : (prefixWord ++ tailWord_623106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623106).length < 2 ^ (prefixWord ++ tailWord_623106).sum := by decide
  have hdescent : baseEnd_623106 < baseStart_623106 := by decide
  rcases family_descends (prefixWord ++ tailWord_623106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623116 : List Nat := [2, 2, 1, 2, 4, 1, 4, 2, 2]
def baseStart_623116 : Nat := 118140960795 + 623116 * 2 ^ 59
def prefixEnd_623116 : Nat := 4983230072969 + 3 ^ 40 * 623116 * 2
def baseEnd_623116 : Nat := 284407121339634923986087

theorem tailTrace_623116 : CollatzResearch.WordTrace tailWord_623116 prefixEnd_623116 284407121339634923986087 := by
  unfold tailWord_623116
  simp only [CollatzResearch.WordTrace]
  refine ⟨11363453805282313292700601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15151271740376417723600801 11363453805282313292700601)
  ·
    refine ⟨8522590353961734969525451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11363453805282313292700601 8522590353961734969525451)
    ·
      refine ⟨12783885530942602454288177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8522590353961734969525451 12783885530942602454288177)
      ·
        refine ⟨9587914148206951840716133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12783885530942602454288177 9587914148206951840716133)
        ·
          refine ⟨1797733902788803470134275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9587914148206951840716133 1797733902788803470134275)
          ·
            refine ⟨2696600854183205205201413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797733902788803470134275 2696600854183205205201413)
            ·
              refine ⟨505612660159350975975265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2696600854183205205201413 505612660159350975975265)
              ·
                refine ⟨379209495119513231981449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505612660159350975975265 379209495119513231981449)
                ·
                  refine ⟨284407121339634923986087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379209495119513231981449 284407121339634923986087)
                  ·
                    rfl

theorem cell20_623116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_623116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623116 prefixEnd_623116 := by exact prefixLift 623116
  have htrace : WordTrace (prefixWord ++ tailWord_623116) baseStart_623116 baseEnd_623116 := by
    simpa [prefixWord, tailWord_623116, baseEnd_623116] using wordTrace_append hprefix tailTrace_623116
  have hstable : (prefixWord ++ tailWord_623116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623116).length < 2 ^ (prefixWord ++ tailWord_623116).sum := by decide
  have hdescent : baseEnd_623116 < baseStart_623116 := by decide
  rcases family_descends (prefixWord ++ tailWord_623116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623141 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_623141 : Nat := 118140960795 + 623141 * 2 ^ 59
def prefixEnd_623141 : Nat := 4983230072969 + 3 ^ 40 * 623141 * 2
def baseEnd_623141 : Nat := 284418532020845948152651

theorem tailTrace_623141 : CollatzResearch.WordTrace tailWord_623141 prefixEnd_623141 284418532020845948152651 := by
  unfold tailWord_623141
  simp only [CollatzResearch.WordTrace]
  refine ⟨22727819435474055855061277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15151879623649370570040851 22727819435474055855061277)
  ·
    refine ⟨8522932288302770945647979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22727819435474055855061277 8522932288302770945647979)
    ·
      refine ⟨12784398432454156418471969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8522932288302770945647979 12784398432454156418471969)
      ·
        refine ⟨9588298824340617313853977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12784398432454156418471969 9588298824340617313853977)
        ·
          refine ⟨7191224118255462985390483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9588298824340617313853977 7191224118255462985390483)
          ·
            refine ⟨10786836177383194478085725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7191224118255462985390483 10786836177383194478085725)
            ·
              refine ⟨4045063566518697929282147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10786836177383194478085725 4045063566518697929282147)
              ·
                refine ⟨6067595349778046893923221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045063566518697929282147 6067595349778046893923221)
                ·
                  refine ⟨284418532020845948152651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6067595349778046893923221 284418532020845948152651)
                  ·
                    rfl

theorem cell20_623141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_623141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623141 prefixEnd_623141 := by exact prefixLift 623141
  have htrace : WordTrace (prefixWord ++ tailWord_623141) baseStart_623141 baseEnd_623141 := by
    simpa [prefixWord, tailWord_623141, baseEnd_623141] using wordTrace_append hprefix tailTrace_623141
  have hstable : (prefixWord ++ tailWord_623141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623141).length < 2 ^ (prefixWord ++ tailWord_623141).sum := by decide
  have hdescent : baseEnd_623141 < baseStart_623141 := by decide
  rcases family_descends (prefixWord ++ tailWord_623141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623148 : List Nat := [2, 2, 1, 1, 1, 2, 1, 10]
def baseStart_623148 : Nat := 118140960795 + 623148 * 2 ^ 59
def prefixEnd_623148 : Nat := 4983230072969 + 3 ^ 40 * 623148 * 2
def baseEnd_623148 : Nat := 94807242337195011639763

theorem tailTrace_623148 : CollatzResearch.WordTrace tailWord_623148 prefixEnd_623148 94807242337195011639763 := by
  unfold tailWord_623148
  simp only [CollatzResearch.WordTrace]
  refine ⟨11364037373224348025283049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15152049830965797367044065 11364037373224348025283049)
  ·
    refine ⟨8523028029918261018962287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11364037373224348025283049 8523028029918261018962287)
    ·
      refine ⟨12784542044877391528443431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8523028029918261018962287 12784542044877391528443431)
      ·
        refine ⟨19176813067316087292665147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12784542044877391528443431 19176813067316087292665147)
        ·
          refine ⟨28765219600974130938997721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19176813067316087292665147 28765219600974130938997721)
          ·
            refine ⟨21573914700730598204248291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28765219600974130938997721 21573914700730598204248291)
            ·
              refine ⟨32360872051095897306372437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21573914700730598204248291 32360872051095897306372437)
              ·
                refine ⟨94807242337195011639763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32360872051095897306372437 94807242337195011639763)
                ·
                  rfl

theorem cell20_623148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_623148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623148 prefixEnd_623148 := by exact prefixLift 623148
  have htrace : WordTrace (prefixWord ++ tailWord_623148) baseStart_623148 baseEnd_623148 := by
    simpa [prefixWord, tailWord_623148, baseEnd_623148] using wordTrace_append hprefix tailTrace_623148
  have hstable : (prefixWord ++ tailWord_623148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623148).length < 2 ^ (prefixWord ++ tailWord_623148).sum := by decide
  have hdescent : baseEnd_623148 < baseStart_623148 := by decide
  rcases family_descends (prefixWord ++ tailWord_623148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623165 : List Nat := [1, 4, 1, 3, 2, 2, 7]
def baseStart_623165 : Nat := 118140960795 + 623165 * 2 ^ 59
def prefixEnd_623165 : Nat := 4983230072969 + 3 ^ 40 * 623165 * 2
def baseEnd_623165 : Nat := 31603276252756503483617

theorem tailTrace_623165 : CollatzResearch.WordTrace tailWord_623165 prefixEnd_623165 31603276252756503483617 := by
  unfold tailWord_623165
  simp only [CollatzResearch.WordTrace]
  refine ⟨22728694787387107953934949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15152463191591405302623299 22728694787387107953934949)
  ·
    refine ⟨4261630272635082741362803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22728694787387107953934949 4261630272635082741362803)
    ·
      refine ⟨6392445408952624112044205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4261630272635082741362803 6392445408952624112044205)
      ·
        refine ⟨2397167028357234042016577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6392445408952624112044205 2397167028357234042016577)
        ·
          refine ⟨1797875271267925531512433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2397167028357234042016577 1797875271267925531512433)
          ·
            refine ⟨1348406453450944148634325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797875271267925531512433 1348406453450944148634325)
            ·
              refine ⟨31603276252756503483617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1348406453450944148634325 31603276252756503483617)
              ·
                rfl

theorem cell20_623165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 7].length) (baseStart_623165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623165 prefixEnd_623165 := by exact prefixLift 623165
  have htrace : WordTrace (prefixWord ++ tailWord_623165) baseStart_623165 baseEnd_623165 := by
    simpa [prefixWord, tailWord_623165, baseEnd_623165] using wordTrace_append hprefix tailTrace_623165
  have hstable : (prefixWord ++ tailWord_623165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623165).length < 2 ^ (prefixWord ++ tailWord_623165).sum := by decide
  have hdescent : baseEnd_623165 < baseStart_623165 := by decide
  rcases family_descends (prefixWord ++ tailWord_623165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623175 : List Nat := [1, 1, 4, 1, 4, 1, 2, 4, 2]
def baseStart_623175 : Nat := 118140960795 + 623175 * 2 ^ 59
def prefixEnd_623175 : Nat := 4983230072969 + 3 ^ 40 * 623175 * 2
def baseEnd_623175 : Nat := 284434050547292941019179

theorem tailTrace_623175 : CollatzResearch.WordTrace tailWord_623175 prefixEnd_623175 284434050547292941019179 := by
  unfold tailWord_623175
  simp only [CollatzResearch.WordTrace]
  refine ⟨22729059517350879661798979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15152706344900586441199319 22729059517350879661798979)
  ·
    refine ⟨34093589276026319492698469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22729059517350879661798979 34093589276026319492698469)
    ·
      refine ⟨6392547989254934904880963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34093589276026319492698469 6392547989254934904880963)
      ·
        refine ⟨9588821983882402357321445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6392547989254934904880963 9588821983882402357321445)
        ·
          refine ⟨1797904121977950441997771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9588821983882402357321445 1797904121977950441997771)
          ·
            refine ⟨2696856182966925662996657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797904121977950441997771 2696856182966925662996657)
            ·
              refine ⟨2022642137225194247247493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2696856182966925662996657 2022642137225194247247493)
              ·
                refine ⟨379245400729723921358905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2022642137225194247247493 379245400729723921358905)
                ·
                  refine ⟨284434050547292941019179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379245400729723921358905 284434050547292941019179)
                  ·
                    rfl

theorem cell20_623175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 2].length) (baseStart_623175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623175 prefixEnd_623175 := by exact prefixLift 623175
  have htrace : WordTrace (prefixWord ++ tailWord_623175) baseStart_623175 baseEnd_623175 := by
    simpa [prefixWord, tailWord_623175, baseEnd_623175] using wordTrace_append hprefix tailTrace_623175
  have hstable : (prefixWord ++ tailWord_623175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623175).length < 2 ^ (prefixWord ++ tailWord_623175).sum := by decide
  have hdescent : baseEnd_623175 < baseStart_623175 := by decide
  rcases family_descends (prefixWord ++ tailWord_623175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623179 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_623179 : Nat := 118140960795 + 623179 * 2 ^ 59
def prefixEnd_623179 : Nat := 4983230072969 + 3 ^ 40 * 623179 * 2
def baseEnd_623179 : Nat := 284435876256286704885829

theorem tailTrace_623179 : CollatzResearch.WordTrace tailWord_623179 prefixEnd_623179 284435876256286704885829 := by
  unfold tailWord_623179
  simp only [CollatzResearch.WordTrace]
  refine ⟨22729205409336388344944591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15152803606224258896629727 22729205409336388344944591)
  ·
    refine ⟨34093808114004582517416887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22729205409336388344944591 34093808114004582517416887)
    ·
      refine ⟨51140712171006873776125331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34093808114004582517416887 51140712171006873776125331)
      ·
        refine ⟨76711068256510310664187997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51140712171006873776125331 76711068256510310664187997)
        ·
          refine ⟨28766650596191366499070499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76711068256510310664187997 28766650596191366499070499)
          ·
            refine ⟨43149975894287049748605749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28766650596191366499070499 43149975894287049748605749)
            ·
              refine ⟨4045310240089410913931789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43149975894287049748605749 4045310240089410913931789)
              ·
                refine ⟨1516991340033529092724421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4045310240089410913931789 1516991340033529092724421)
                ·
                  refine ⟨284435876256286704885829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516991340033529092724421 284435876256286704885829)
                  ·
                    rfl

theorem cell20_623179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_623179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623179 prefixEnd_623179 := by exact prefixLift 623179
  have htrace : WordTrace (prefixWord ++ tailWord_623179) baseStart_623179 baseEnd_623179 := by
    simpa [prefixWord, tailWord_623179, baseEnd_623179] using wordTrace_append hprefix tailTrace_623179
  have hstable : (prefixWord ++ tailWord_623179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623179).length < 2 ^ (prefixWord ++ tailWord_623179).sum := by decide
  have hdescent : baseEnd_623179 < baseStart_623179 := by decide
  rcases family_descends (prefixWord ++ tailWord_623179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623210 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_623210 : Nat := 118140960795 + 623210 * 2 ^ 59
def prefixEnd_623210 : Nat := 4983230072969 + 3 ^ 40 * 623210 * 2
def baseEnd_623210 : Nat := 284450025500988374852369

theorem tailTrace_623210 : CollatzResearch.WordTrace tailWord_623210 prefixEnd_623210 284450025500988374852369 := by
  unfold tailWord_623210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682584018056020159830771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15153557381482720426215389 5682584018056020159830771)
  ·
    refine ⟨8523876027084030239746157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5682584018056020159830771 8523876027084030239746157)
    ·
      refine ⟨3196453510156511339904809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8523876027084030239746157 3196453510156511339904809)
      ·
        refine ⟨2397340132617383504928607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3196453510156511339904809 2397340132617383504928607)
        ·
          refine ⟨3596010198926075257392911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397340132617383504928607 3596010198926075257392911)
          ·
            refine ⟨5394015298389112886089367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596010198926075257392911 5394015298389112886089367)
            ·
              refine ⟨8091022947583669329134051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5394015298389112886089367 8091022947583669329134051)
              ·
                refine ⟨12136534421375503993701077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8091022947583669329134051 12136534421375503993701077)
                ·
                  refine ⟨284450025500988374852369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12136534421375503993701077 284450025500988374852369)
                  ·
                    rfl

theorem cell20_623210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_623210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623210 prefixEnd_623210 := by exact prefixLift 623210
  have htrace : WordTrace (prefixWord ++ tailWord_623210) baseStart_623210 baseEnd_623210 := by
    simpa [prefixWord, tailWord_623210, baseEnd_623210] using wordTrace_append hprefix tailTrace_623210
  have hstable : (prefixWord ++ tailWord_623210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623210).length < 2 ^ (prefixWord ++ tailWord_623210).sum := by decide
  have hdescent : baseEnd_623210 < baseStart_623210 := by decide
  rcases family_descends (prefixWord ++ tailWord_623210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623255 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_623255 : Nat := 118140960795 + 623255 * 2 ^ 59
def prefixEnd_623255 : Nat := 4983230072969 + 3 ^ 40 * 623255 * 2
def baseEnd_623255 : Nat := 284470564727168218352185

theorem tailTrace_623255 : CollatzResearch.WordTrace tailWord_623255 prefixEnd_623255 284470564727168218352185 := by
  unfold tailWord_623255
  simp only [CollatzResearch.WordTrace]
  refine ⟨22731977357061053324711219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15154651571374035549807479 22731977357061053324711219)
  ·
    refine ⟨34097966035591579987066829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22731977357061053324711219 34097966035591579987066829)
    ·
      refine ⟨12786737263346842495150061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34097966035591579987066829 12786737263346842495150061)
      ·
        refine ⟨4795026473755065935681273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12786737263346842495150061 4795026473755065935681273)
        ·
          refine ⟨3596269855316299451760955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4795026473755065935681273 3596269855316299451760955)
          ·
            refine ⟨5394404782974449177641433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596269855316299451760955 5394404782974449177641433)
            ·
              refine ⟨4045803587230836883231075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5394404782974449177641433 4045803587230836883231075)
              ·
                refine ⟨6068705380846255324846613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4045803587230836883231075 6068705380846255324846613)
                ·
                  refine ⟨284470564727168218352185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6068705380846255324846613 284470564727168218352185)
                  ·
                    rfl

theorem cell20_623255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_623255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623255 prefixEnd_623255 := by exact prefixLift 623255
  have htrace : WordTrace (prefixWord ++ tailWord_623255) baseStart_623255 baseEnd_623255 := by
    simpa [prefixWord, tailWord_623255, baseEnd_623255] using wordTrace_append hprefix tailTrace_623255
  have hstable : (prefixWord ++ tailWord_623255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623255).length < 2 ^ (prefixWord ++ tailWord_623255).sum := by decide
  have hdescent : baseEnd_623255 < baseStart_623255 := by decide
  rcases family_descends (prefixWord ++ tailWord_623255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623285 : List Nat := [1, 3, 3, 3, 1, 3, 2, 2, 2]
def baseStart_623285 : Nat := 118140960795 + 623285 * 2 ^ 59
def prefixEnd_623285 : Nat := 4983230072969 + 3 ^ 40 * 623285 * 2
def baseEnd_623285 : Nat := 284484257544621447352063

theorem tailTrace_623285 : CollatzResearch.WordTrace tailWord_623285 prefixEnd_623285 284484257544621447352063 := by
  unfold tailWord_623285
  simp only [CollatzResearch.WordTrace]
  refine ⟨22733071546952368448303309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15155381031301578965535539 22733071546952368448303309)
  ·
    refine ⟨8524901830107138168113741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22733071546952368448303309 8524901830107138168113741)
    ·
      refine ⟨3196838186290176813042653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8524901830107138168113741 3196838186290176813042653)
      ·
        refine ⟨1198814319858816304890995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3196838186290176813042653 1198814319858816304890995)
        ·
          refine ⟨1798221479788224457336493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198814319858816304890995 1798221479788224457336493)
          ·
            refine ⟨674333054920584171501185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1798221479788224457336493 674333054920584171501185)
            ·
              refine ⟨505749791190438128625889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674333054920584171501185 505749791190438128625889)
              ·
                refine ⟨379312343392828596469417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505749791190438128625889 379312343392828596469417)
                ·
                  refine ⟨284484257544621447352063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379312343392828596469417 284484257544621447352063)
                  ·
                    rfl

theorem cell20_623285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_623285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623285 prefixEnd_623285 := by exact prefixLift 623285
  have htrace : WordTrace (prefixWord ++ tailWord_623285) baseStart_623285 baseEnd_623285 := by
    simpa [prefixWord, tailWord_623285, baseEnd_623285] using wordTrace_append hprefix tailTrace_623285
  have hstable : (prefixWord ++ tailWord_623285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623285).length < 2 ^ (prefixWord ++ tailWord_623285).sum := by decide
  have hdescent : baseEnd_623285 < baseStart_623285 := by decide
  rcases family_descends (prefixWord ++ tailWord_623285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623307 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_623307 : Nat := 118140960795 + 623307 * 2 ^ 59
def prefixEnd_623307 : Nat := 4983230072969 + 3 ^ 40 * 623307 * 2
def baseEnd_623307 : Nat := 284494298944087148618639

theorem tailTrace_623307 : CollatzResearch.WordTrace tailWord_623307 prefixEnd_623307 284494298944087148618639 := by
  unfold tailWord_623307
  simp only [CollatzResearch.WordTrace]
  refine ⟨22733873952872666205604175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15155915968581777470402783 22733873952872666205604175)
  ·
    refine ⟨34100810929308999308406263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22733873952872666205604175 34100810929308999308406263)
    ·
      refine ⟨51151216393963498962609395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34100810929308999308406263 51151216393963498962609395)
      ·
        refine ⟨76726824590945248443914093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51151216393963498962609395 76726824590945248443914093)
        ·
          refine ⟨28772559221604468166467785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76726824590945248443914093 28772559221604468166467785)
          ·
            refine ⟨21579419416203351124850839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28772559221604468166467785 21579419416203351124850839)
            ·
              refine ⟨32369129124305026687276259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21579419416203351124850839 32369129124305026687276259)
              ·
                refine ⟨48553693686457540030914389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32369129124305026687276259 48553693686457540030914389)
                ·
                  refine ⟨284494298944087148618639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48553693686457540030914389 284494298944087148618639)
                  ·
                    rfl

theorem cell20_623307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_623307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623307 prefixEnd_623307 := by exact prefixLift 623307
  have htrace : WordTrace (prefixWord ++ tailWord_623307) baseStart_623307 baseEnd_623307 := by
    simpa [prefixWord, tailWord_623307, baseEnd_623307] using wordTrace_append hprefix tailTrace_623307
  have hstable : (prefixWord ++ tailWord_623307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623307).length < 2 ^ (prefixWord ++ tailWord_623307).sum := by decide
  have hdescent : baseEnd_623307 < baseStart_623307 := by decide
  rcases family_descends (prefixWord ++ tailWord_623307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623310 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_623310 : Nat := 118140960795 + 623310 * 2 ^ 59
def prefixEnd_623310 : Nat := 4983230072969 + 3 ^ 40 * 623310 * 2
def baseEnd_623310 : Nat := 284495668225832471518627

theorem tailTrace_623310 : CollatzResearch.WordTrace tailWord_623310 prefixEnd_623310 284495668225832471518627 := by
  unfold tailWord_623310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841747921482724714745423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15155988914574531811975589 2841747921482724714745423)
  ·
    refine ⟨4262621882224087072118135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2841747921482724714745423 4262621882224087072118135)
    ·
      refine ⟨6393932823336130608177203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262621882224087072118135 6393932823336130608177203)
      ·
        refine ⟨9590899235004195912265805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6393932823336130608177203 9590899235004195912265805)
        ·
          refine ⟨3596587213126573467099677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9590899235004195912265805 3596587213126573467099677)
          ·
            refine ⟨1348720204922465050162379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3596587213126573467099677 1348720204922465050162379)
            ·
              refine ⟨2023080307383697575243569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348720204922465050162379 2023080307383697575243569)
              ·
                refine ⟨1517310230537773181432677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023080307383697575243569 1517310230537773181432677)
                ·
                  refine ⟨284495668225832471518627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1517310230537773181432677 284495668225832471518627)
                  ·
                    rfl

theorem cell20_623310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_623310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623310 prefixEnd_623310 := by exact prefixLift 623310
  have htrace : WordTrace (prefixWord ++ tailWord_623310) baseStart_623310 baseEnd_623310 := by
    simpa [prefixWord, tailWord_623310, baseEnd_623310] using wordTrace_append hprefix tailTrace_623310
  have hstable : (prefixWord ++ tailWord_623310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623310).length < 2 ^ (prefixWord ++ tailWord_623310).sum := by decide
  have hdescent : baseEnd_623310 < baseStart_623310 := by decide
  rcases family_descends (prefixWord ++ tailWord_623310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623327 : List Nat := [1, 1, 2, 3, 2, 4, 2, 3, 2]
def baseStart_623327 : Nat := 118140960795 + 623327 * 2 ^ 59
def prefixEnd_623327 : Nat := 4983230072969 + 3 ^ 40 * 623327 * 2
def baseEnd_623327 : Nat := 284503427489055967951891

theorem tailTrace_623327 : CollatzResearch.WordTrace tailWord_623327 prefixEnd_623327 284503427489055967951891 := by
  unfold tailWord_623327
  simp only [CollatzResearch.WordTrace]
  refine ⟨22734603412800209621332235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15156402275200139747554823 22734603412800209621332235)
  ·
    refine ⟨34101905119200314431998353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22734603412800209621332235 34101905119200314431998353)
    ·
      refine ⟨25576428839400235823998765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34101905119200314431998353 25576428839400235823998765)
      ·
        refine ⟨9591160814775088433999537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25576428839400235823998765 9591160814775088433999537)
        ·
          refine ⟨7193370611081316325499653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9591160814775088433999537 7193370611081316325499653)
          ·
            refine ⟨1348756989577746811031185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7193370611081316325499653 1348756989577746811031185)
            ·
              refine ⟨1011567742183310108273389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348756989577746811031185 1011567742183310108273389)
              ·
                refine ⟨379337903318741290602521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1011567742183310108273389 379337903318741290602521)
                ·
                  refine ⟨284503427489055967951891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379337903318741290602521 284503427489055967951891)
                  ·
                    rfl

theorem cell20_623327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 2].length) (baseStart_623327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623327 prefixEnd_623327 := by exact prefixLift 623327
  have htrace : WordTrace (prefixWord ++ tailWord_623327) baseStart_623327 baseEnd_623327 := by
    simpa [prefixWord, tailWord_623327, baseEnd_623327] using wordTrace_append hprefix tailTrace_623327
  have hstable : (prefixWord ++ tailWord_623327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623327).length < 2 ^ (prefixWord ++ tailWord_623327).sum := by decide
  have hdescent : baseEnd_623327 < baseStart_623327 := by decide
  rcases family_descends (prefixWord ++ tailWord_623327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623369 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_623369 : Nat := 118140960795 + 623369 * 2 ^ 59
def prefixEnd_623369 : Nat := 4983230072969 + 3 ^ 40 * 623369 * 2
def baseEnd_623369 : Nat := 284522597433490488551719

theorem tailTrace_623369 : CollatzResearch.WordTrace tailWord_623369 prefixEnd_623369 284522597433490488551719 := by
  unfold tailWord_623369
  simp only [CollatzResearch.WordTrace]
  refine ⟨22736135278648050794361161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15157423519098700529574107 22736135278648050794361161)
  ·
    refine ⟨17052101458986038095770871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22736135278648050794361161 17052101458986038095770871)
    ·
      refine ⟨25578152188479057143656307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17052101458986038095770871 25578152188479057143656307)
      ·
        refine ⟨38367228282718585715484461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25578152188479057143656307 38367228282718585715484461)
        ·
          refine ⟨14387710606019469643306673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38367228282718585715484461 14387710606019469643306673)
          ·
            refine ⟨10790782954514602232480005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14387710606019469643306673 10790782954514602232480005)
            ·
              refine ⟨2023271803971487918590001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10790782954514602232480005 2023271803971487918590001)
              ·
                refine ⟨1517453852978615938942501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023271803971487918590001 1517453852978615938942501)
                ·
                  refine ⟨284522597433490488551719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1517453852978615938942501 284522597433490488551719)
                  ·
                    rfl

theorem cell20_623369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_623369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623369 prefixEnd_623369 := by exact prefixLift 623369
  have htrace : WordTrace (prefixWord ++ tailWord_623369) baseStart_623369 baseEnd_623369 := by
    simpa [prefixWord, tailWord_623369, baseEnd_623369] using wordTrace_append hprefix tailTrace_623369
  have hstable : (prefixWord ++ tailWord_623369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623369).length < 2 ^ (prefixWord ++ tailWord_623369).sum := by decide
  have hdescent : baseEnd_623369 < baseStart_623369 := by decide
  rcases family_descends (prefixWord ++ tailWord_623369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623378 : List Nat := [3, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_623378 : Nat := 118140960795 + 623378 * 2 ^ 59
def prefixEnd_623378 : Nat := 4983230072969 + 3 ^ 40 * 623378 * 2
def baseEnd_623378 : Nat := 284526705278726457251683

theorem tailTrace_623378 : CollatzResearch.WordTrace tailWord_623378 prefixEnd_623378 284526705278726457251683 := by
  unfold tailWord_623378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5684115883903861332859697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15157642357076963554292525 5684115883903861332859697)
  ·
    refine ⟨4263086912927895999644773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5684115883903861332859697 4263086912927895999644773)
    ·
      refine ⟨799328796173980499933395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4263086912927895999644773 799328796173980499933395)
      ·
        refine ⟨1198993194260970749900093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799328796173980499933395 1198993194260970749900093)
        ·
          refine ⟨449622447847864031212535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1198993194260970749900093 449622447847864031212535)
          ·
            refine ⟨674433671771796046818803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449622447847864031212535 674433671771796046818803)
            ·
              refine ⟨1011650507657694070228205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674433671771796046818803 1011650507657694070228205)
              ·
                refine ⟨379368940371635276335577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1011650507657694070228205 379368940371635276335577)
                ·
                  refine ⟨284526705278726457251683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379368940371635276335577 284526705278726457251683)
                  ·
                    rfl

theorem cell20_623378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_623378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623378 prefixEnd_623378 := by exact prefixLift 623378
  have htrace : WordTrace (prefixWord ++ tailWord_623378) baseStart_623378 baseEnd_623378 := by
    simpa [prefixWord, tailWord_623378, baseEnd_623378] using wordTrace_append hprefix tailTrace_623378
  have hstable : (prefixWord ++ tailWord_623378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623378).length < 2 ^ (prefixWord ++ tailWord_623378).sum := by decide
  have hdescent : baseEnd_623378 < baseStart_623378 := by decide
  rcases family_descends (prefixWord ++ tailWord_623378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623389 : List Nat := [1, 4, 2, 4, 2, 1, 6]
def baseStart_623389 : Nat := 118140960795 + 623389 * 2 ^ 59
def prefixEnd_623389 : Nat := 4983230072969 + 3 ^ 40 * 623389 * 2
def baseEnd_623389 : Nat := 31614636219828811987219

theorem tailTrace_623389 : CollatzResearch.WordTrace tailWord_623389 prefixEnd_623389 31614636219828811987219 := by
  unfold tailWord_623389
  simp only [CollatzResearch.WordTrace]
  refine ⟨22736864738575594210089221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15157909825717062806726147 22736864738575594210089221)
  ·
    refine ⟨4263162138482923914391729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22736864738575594210089221 4263162138482923914391729)
    ·
      refine ⟨3197371603862192935793797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4263162138482923914391729 3197371603862192935793797)
      ·
        refine ⟨599507175724161175461337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3197371603862192935793797 599507175724161175461337)
        ·
          refine ⟨449630381793120881596003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599507175724161175461337 449630381793120881596003)
          ·
            refine ⟨674445572689681322394005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449630381793120881596003 674445572689681322394005)
            ·
              refine ⟨31614636219828811987219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 674445572689681322394005 31614636219828811987219)
              ·
                rfl

theorem cell20_623389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 6].length) (baseStart_623389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623389 prefixEnd_623389 := by exact prefixLift 623389
  have htrace : WordTrace (prefixWord ++ tailWord_623389) baseStart_623389 baseEnd_623389 := by
    simpa [prefixWord, tailWord_623389, baseEnd_623389] using wordTrace_append hprefix tailTrace_623389
  have hstable : (prefixWord ++ tailWord_623389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623389).length < 2 ^ (prefixWord ++ tailWord_623389).sum := by decide
  have hdescent : baseEnd_623389 < baseStart_623389 := by decide
  rcases family_descends (prefixWord ++ tailWord_623389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623400 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_623400 : Nat := 118140960795 + 623400 * 2 ^ 59
def prefixEnd_623400 : Nat := 4983230072969 + 3 ^ 40 * 623400 * 2
def baseEnd_623400 : Nat := 284536746678192158518259

theorem tailTrace_623400 : CollatzResearch.WordTrace tailWord_623400 prefixEnd_623400 284536746678192158518259 := by
  unfold tailWord_623400
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368632970767871544369827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15158177294357162059159769 11368632970767871544369827)
  ·
    refine ⟨17052949456151807316554741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11368632970767871544369827 17052949456151807316554741)
    ·
      refine ⟨1598714011514231935927007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17052949456151807316554741 1598714011514231935927007)
      ·
        refine ⟨2398071017271347903890511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598714011514231935927007 2398071017271347903890511)
        ·
          refine ⟨3597106525907021855835767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2398071017271347903890511 3597106525907021855835767)
          ·
            refine ⟨5395659788860532783753651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597106525907021855835767 5395659788860532783753651)
            ·
              refine ⟨8093489683290799175630477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5395659788860532783753651 8093489683290799175630477)
              ·
                refine ⟨3035058631234049690861429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8093489683290799175630477 3035058631234049690861429)
                ·
                  refine ⟨284536746678192158518259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3035058631234049690861429 284536746678192158518259)
                  ·
                    rfl

theorem cell20_623400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_623400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623400 prefixEnd_623400 := by exact prefixLift 623400
  have htrace : WordTrace (prefixWord ++ tailWord_623400) baseStart_623400 baseEnd_623400 := by
    simpa [prefixWord, tailWord_623400, baseEnd_623400] using wordTrace_append hprefix tailTrace_623400
  have hstable : (prefixWord ++ tailWord_623400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623400).length < 2 ^ (prefixWord ++ tailWord_623400).sum := by decide
  have hdescent : baseEnd_623400 < baseStart_623400 := by decide
  rcases family_descends (prefixWord ++ tailWord_623400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623458 : List Nat := [3, 3, 2, 1, 3, 1, 1, 4, 2]
def baseStart_623458 : Nat := 118140960795 + 623458 * 2 ^ 59
def prefixEnd_623458 : Nat := 4983230072969 + 3 ^ 40 * 623458 * 2
def baseEnd_623458 : Nat := 284563219458601734584689

theorem tailTrace_623458 : CollatzResearch.WordTrace tailWord_623458 prefixEnd_623458 284563219458601734584689 := by
  unfold tailWord_623458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5684845343831404748587757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15159587583550412662900685 5684845343831404748587757)
  ·
    refine ⟨2131817003936776780720409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5684845343831404748587757 2131817003936776780720409)
    ·
      refine ⟨1598862752952582585540307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2131817003936776780720409 1598862752952582585540307)
      ·
        refine ⟨2398294129428873878310461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598862752952582585540307 2398294129428873878310461)
        ·
          refine ⟨899360298535827704366423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2398294129428873878310461 899360298535827704366423)
          ·
            refine ⟨1349040447803741556549635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899360298535827704366423 1349040447803741556549635)
            ·
              refine ⟨2023560671705612334824453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349040447803741556549635 2023560671705612334824453)
              ·
                refine ⟨379417625944802312779585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2023560671705612334824453 379417625944802312779585)
                ·
                  refine ⟨284563219458601734584689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379417625944802312779585 284563219458601734584689)
                  ·
                    rfl

theorem cell20_623458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_623458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623458 prefixEnd_623458 := by exact prefixLift 623458
  have htrace : WordTrace (prefixWord ++ tailWord_623458) baseStart_623458 baseEnd_623458 := by
    simpa [prefixWord, tailWord_623458, baseEnd_623458] using wordTrace_append hprefix tailTrace_623458
  have hstable : (prefixWord ++ tailWord_623458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623458).length < 2 ^ (prefixWord ++ tailWord_623458).sum := by decide
  have hdescent : baseEnd_623458 < baseStart_623458 := by decide
  rcases family_descends (prefixWord ++ tailWord_623458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623500 : List Nat := [2, 2, 1, 2, 1, 2, 3, 5, 2]
def baseStart_623500 : Nat := 118140960795 + 623500 * 2 ^ 59
def prefixEnd_623500 : Nat := 4983230072969 + 3 ^ 40 * 623500 * 2
def baseEnd_623500 : Nat := 284582389403036255184517

theorem tailTrace_623500 : CollatzResearch.WordTrace tailWord_623500 prefixEnd_623500 284582389403036255184517 := by
  unfold tailWord_623500
  simp only [CollatzResearch.WordTrace]
  refine ⟨11370456620586730083689977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15160608827448973444919969 11370456620586730083689977)
  ·
    refine ⟨8527842465440047562767483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11370456620586730083689977 8527842465440047562767483)
    ·
      refine ⟨12791763698160071344151225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8527842465440047562767483 12791763698160071344151225)
      ·
        refine ⟨9593822773620053508113419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12791763698160071344151225 9593822773620053508113419)
        ·
          refine ⟨14390734160430080262170129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9593822773620053508113419 14390734160430080262170129)
          ·
            refine ⟨10793050620322560196627597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14390734160430080262170129 10793050620322560196627597)
            ·
              refine ⟨4047393982620960073735349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10793050620322560196627597 4047393982620960073735349)
              ·
                refine ⟨379443185870715006912689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4047393982620960073735349 379443185870715006912689)
                ·
                  refine ⟨284582389403036255184517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379443185870715006912689 284582389403036255184517)
                  ·
                    rfl

theorem cell20_623500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_623500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623500 prefixEnd_623500 := by exact prefixLift 623500
  have htrace : WordTrace (prefixWord ++ tailWord_623500) baseStart_623500 baseEnd_623500 := by
    simpa [prefixWord, tailWord_623500, baseEnd_623500] using wordTrace_append hprefix tailTrace_623500
  have hstable : (prefixWord ++ tailWord_623500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623500).length < 2 ^ (prefixWord ++ tailWord_623500).sum := by decide
  have hdescent : baseEnd_623500 < baseStart_623500 := by decide
  rcases family_descends (prefixWord ++ tailWord_623500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623545 : List Nat := [1, 2, 1, 4, 2, 2, 4, 4]
def baseStart_623545 : Nat := 118140960795 + 623545 * 2 ^ 59
def prefixEnd_623545 : Nat := 4983230072969 + 3 ^ 40 * 623545 * 2
def baseEnd_623545 : Nat := 94867642876405366228111

theorem tailTrace_623545 : CollatzResearch.WordTrace tailWord_623545 prefixEnd_623545 94867642876405366228111 := by
  unfold tailWord_623545
  simp only [CollatzResearch.WordTrace]
  refine ⟨22742554526010432852768089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15161703017340288568512059 22742554526010432852768089)
  ·
    refine ⟨17056915894507824639576067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22742554526010432852768089 17056915894507824639576067)
    ·
      refine ⟨25585373841761736959364101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17056915894507824639576067 25585373841761736959364101)
      ·
        refine ⟨4797257595330325679880769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25585373841761736959364101 4797257595330325679880769)
        ·
          refine ⟨3597943196497744259910577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4797257595330325679880769 3597943196497744259910577)
          ·
            refine ⟨2698457397373308194932933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3597943196497744259910577 2698457397373308194932933)
            ·
              refine ⟨505960762007495286549925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2698457397373308194932933 505960762007495286549925)
              ·
                refine ⟨94867642876405366228111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 505960762007495286549925 94867642876405366228111)
                ·
                  rfl

theorem cell20_623545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 4].length) (baseStart_623545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623545 prefixEnd_623545 := by exact prefixLift 623545
  have htrace : WordTrace (prefixWord ++ tailWord_623545) baseStart_623545 baseEnd_623545 := by
    simpa [prefixWord, tailWord_623545, baseEnd_623545] using wordTrace_append hprefix tailTrace_623545
  have hstable : (prefixWord ++ tailWord_623545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623545).length < 2 ^ (prefixWord ++ tailWord_623545).sum := by decide
  have hdescent : baseEnd_623545 < baseStart_623545 := by decide
  rcases family_descends (prefixWord ++ tailWord_623545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623566 : List Nat := [4, 1, 1, 1, 2, 3, 8]
def baseStart_623566 : Nat := 118140960795 + 623566 * 2 ^ 59
def prefixEnd_623566 : Nat := 4983230072969 + 3 ^ 40 * 623566 * 2
def baseEnd_623566 : Nat := 31623612622381484331583

theorem tailTrace_623566 : CollatzResearch.WordTrace tailWord_623566 prefixEnd_623566 31623612622381484331583 := by
  unfold tailWord_623566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842915057366794179910319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15162213639289568959521701 2842915057366794179910319)
  ·
    refine ⟨4264372586050191269865479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2842915057366794179910319 4264372586050191269865479)
    ·
      refine ⟨6396558879075286904798219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4264372586050191269865479 6396558879075286904798219)
      ·
        refine ⟨9594838318612930357197329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6396558879075286904798219 9594838318612930357197329)
        ·
          refine ⟨7196128738959697767897997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9594838318612930357197329 7196128738959697767897997)
          ·
            refine ⟨2698548277109886662961749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7196128738959697767897997 2698548277109886662961749)
            ·
              refine ⟨31623612622381484331583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2698548277109886662961749 31623612622381484331583)
              ·
                rfl

theorem cell20_623566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 8].length) (baseStart_623566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623566 prefixEnd_623566 := by exact prefixLift 623566
  have htrace : WordTrace (prefixWord ++ tailWord_623566) baseStart_623566 baseEnd_623566 := by
    simpa [prefixWord, tailWord_623566, baseEnd_623566] using wordTrace_append hprefix tailTrace_623566
  have hstable : (prefixWord ++ tailWord_623566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623566).length < 2 ^ (prefixWord ++ tailWord_623566).sum := by decide
  have hdescent : baseEnd_623566 < baseStart_623566 := by decide
  rcases family_descends (prefixWord ++ tailWord_623566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623572 : List Nat := [2, 4, 1, 2, 1, 3, 3, 2, 2]
def baseStart_623572 : Nat := 118140960795 + 623572 * 2 ^ 59
def prefixEnd_623572 : Nat := 4983230072969 + 3 ^ 40 * 623572 * 2
def baseEnd_623572 : Nat := 284615252164924004784223

theorem tailTrace_623572 : CollatzResearch.WordTrace tailWord_623572 prefixEnd_623572 284615252164924004784223 := by
  unfold tailWord_623572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11371769648456308232000485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15162359531275077642667313 11371769648456308232000485)
  ·
    refine ⟨2132206809085557793500091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11371769648456308232000485 2132206809085557793500091)
    ·
      refine ⟨3198310213628336690250137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2132206809085557793500091 3198310213628336690250137)
      ·
        refine ⟨2398732660221252517687603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3198310213628336690250137 2398732660221252517687603)
        ·
          refine ⟨3598098990331878776531405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2398732660221252517687603 3598098990331878776531405)
          ·
            refine ⟨1349287121374454541199277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3598098990331878776531405 1349287121374454541199277)
            ·
              refine ⟨505982670515420452949729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1349287121374454541199277 505982670515420452949729)
              ·
                refine ⟨379487002886565339712297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505982670515420452949729 379487002886565339712297)
                ·
                  refine ⟨284615252164924004784223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379487002886565339712297 284615252164924004784223)
                  ·
                    rfl

theorem cell20_623572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_623572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623572 prefixEnd_623572 := by exact prefixLift 623572
  have htrace : WordTrace (prefixWord ++ tailWord_623572) baseStart_623572 baseEnd_623572 := by
    simpa [prefixWord, tailWord_623572, baseEnd_623572] using wordTrace_append hprefix tailTrace_623572
  have hstable : (prefixWord ++ tailWord_623572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623572).length < 2 ^ (prefixWord ++ tailWord_623572).sum := by decide
  have hdescent : baseEnd_623572 < baseStart_623572 := by decide
  rcases family_descends (prefixWord ++ tailWord_623572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623576 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 4]
def baseStart_623576 : Nat := 118140960795 + 623576 * 2 ^ 59
def prefixEnd_623576 : Nat := 4983230072969 + 3 ^ 40 * 623576 * 2
def baseEnd_623576 : Nat := 284617077873917768650873

theorem tailTrace_623576 : CollatzResearch.WordTrace tailWord_623576 prefixEnd_623576 284617077873917768650873 := by
  unfold tailWord_623576
  simp only [CollatzResearch.WordTrace]
  refine ⟨11371842594449062573573291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15162456792598750098097721 11371842594449062573573291)
  ·
    refine ⟨17057763891673593860359937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11371842594449062573573291 17057763891673593860359937)
    ·
      refine ⟨12793322918755195395269953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17057763891673593860359937 12793322918755195395269953)
      ·
        refine ⟨9594992189066396546452465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12793322918755195395269953 9594992189066396546452465)
        ·
          refine ⟨7196244141799797409839349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9594992189066396546452465 7196244141799797409839349)
          ·
            refine ⟨674647888293731007172439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7196244141799797409839349 674647888293731007172439)
            ·
              refine ⟨1011971832440596510758659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674647888293731007172439 1011971832440596510758659)
              ·
                refine ⟨1517957748660894766137989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011971832440596510758659 1517957748660894766137989)
                ·
                  refine ⟨284617077873917768650873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1517957748660894766137989 284617077873917768650873)
                  ·
                    rfl

theorem cell20_623576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_623576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623576 prefixEnd_623576 := by exact prefixLift 623576
  have htrace : WordTrace (prefixWord ++ tailWord_623576) baseStart_623576 baseEnd_623576 := by
    simpa [prefixWord, tailWord_623576, baseEnd_623576] using wordTrace_append hprefix tailTrace_623576
  have hstable : (prefixWord ++ tailWord_623576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623576).length < 2 ^ (prefixWord ++ tailWord_623576).sum := by decide
  have hdescent : baseEnd_623576 < baseStart_623576 := by decide
  rcases family_descends (prefixWord ++ tailWord_623576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623583 : List Nat := [1, 1, 2, 3, 5, 1, 2, 5]
def baseStart_623583 : Nat := 118140960795 + 623583 * 2 ^ 59
def prefixEnd_623583 : Nat := 4983230072969 + 3 ^ 40 * 623583 * 2
def baseEnd_623583 : Nat := 94873424288218951805837

theorem tailTrace_623583 : CollatzResearch.WordTrace tailWord_623583 prefixEnd_623583 94873424288218951805837 := by
  unfold tailWord_623583
  simp only [CollatzResearch.WordTrace]
  refine ⟨22743940499872765342651403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15162626999915176895100935 22743940499872765342651403)
  ·
    refine ⟨34115910749809148013977105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22743940499872765342651403 34115910749809148013977105)
    ·
      refine ⟨25586933062356861010482829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34115910749809148013977105 25586933062356861010482829)
      ·
        refine ⟨9595099898383822878931061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25586933062356861010482829 9595099898383822878931061)
        ·
          refine ⟨899540615473483394899787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9595099898383822878931061 899540615473483394899787)
          ·
            refine ⟨1349310923210225092349681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899540615473483394899787 1349310923210225092349681)
            ·
              refine ⟨1011983192407668819262261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349310923210225092349681 1011983192407668819262261)
              ·
                refine ⟨94873424288218951805837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1011983192407668819262261 94873424288218951805837)
                ·
                  rfl

theorem cell20_623583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_623583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623583 prefixEnd_623583 := by exact prefixLift 623583
  have htrace : WordTrace (prefixWord ++ tailWord_623583) baseStart_623583 baseEnd_623583 := by
    simpa [prefixWord, tailWord_623583, baseEnd_623583] using wordTrace_append hprefix tailTrace_623583
  have hstable : (prefixWord ++ tailWord_623583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623583).length < 2 ^ (prefixWord ++ tailWord_623583).sum := by decide
  have hdescent : baseEnd_623583 < baseStart_623583 := by decide
  rcases family_descends (prefixWord ++ tailWord_623583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623586 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_623586 : Nat := 118140960795 + 623586 * 2 ^ 59
def prefixEnd_623586 : Nat := 4983230072969 + 3 ^ 40 * 623586 * 2
def baseEnd_623586 : Nat := 284621642146402178317499

theorem tailTrace_623586 : CollatzResearch.WordTrace tailWord_623586 prefixEnd_623586 284621642146402178317499 := by
  unfold tailWord_623586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686012479715474213752653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15162699945907931236673741 5686012479715474213752653)
  ·
    refine ⟨2132254679893302830157245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5686012479715474213752653 2132254679893302830157245)
    ·
      refine ⟨799595504959988561308967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2132254679893302830157245 799595504959988561308967)
      ·
        refine ⟨1199393257439982841963451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799595504959988561308967 1199393257439982841963451)
        ·
          refine ⟨1799089886159974262945177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199393257439982841963451 1799089886159974262945177)
          ·
            refine ⟨1349317414619980697208883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1799089886159974262945177 1349317414619980697208883)
            ·
              refine ⟨2023976121929971045813325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349317414619980697208883 2023976121929971045813325)
              ·
                refine ⟨758991045723739142179997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2023976121929971045813325 758991045723739142179997)
                ·
                  refine ⟨284621642146402178317499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758991045723739142179997 284621642146402178317499)
                  ·
                    rfl

theorem cell20_623586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_623586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623586 prefixEnd_623586 := by exact prefixLift 623586
  have htrace : WordTrace (prefixWord ++ tailWord_623586) baseStart_623586 baseEnd_623586 := by
    simpa [prefixWord, tailWord_623586, baseEnd_623586] using wordTrace_append hprefix tailTrace_623586
  have hstable : (prefixWord ++ tailWord_623586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623586).length < 2 ^ (prefixWord ++ tailWord_623586).sum := by decide
  have hdescent : baseEnd_623586 < baseStart_623586 := by decide
  rcases family_descends (prefixWord ++ tailWord_623586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623628 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_623628 : Nat := 118140960795 + 623628 * 2 ^ 59
def prefixEnd_623628 : Nat := 4983230072969 + 3 ^ 40 * 623628 * 2
def baseEnd_623628 : Nat := 284640812090836698917327

theorem tailTrace_623628 : CollatzResearch.WordTrace tailWord_623628 prefixEnd_623628 284640812090836698917327 := by
  unfold tailWord_623628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11372790892354869014019769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15163721189806492018693025 11372790892354869014019769)
  ·
    refine ⟨8529593169266151760514827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11372790892354869014019769 8529593169266151760514827)
    ·
      refine ⟨12794389753899227640772241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8529593169266151760514827 12794389753899227640772241)
      ·
        refine ⟨9595792315424420730579181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12794389753899227640772241 9595792315424420730579181)
        ·
          refine ⟨3598422118284157773967193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9595792315424420730579181 3598422118284157773967193)
          ·
            refine ⟨2698816588713118330475395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3598422118284157773967193 2698816588713118330475395)
            ·
              refine ⟨4048224883069677495713093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698816588713118330475395 4048224883069677495713093)
              ·
                refine ⟨759042165575564530446205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4048224883069677495713093 759042165575564530446205)
                ·
                  refine ⟨284640812090836698917327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759042165575564530446205 284640812090836698917327)
                  ·
                    rfl

theorem cell20_623628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_623628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623628 prefixEnd_623628 := by exact prefixLift 623628
  have htrace : WordTrace (prefixWord ++ tailWord_623628) baseStart_623628 baseEnd_623628 := by
    simpa [prefixWord, tailWord_623628, baseEnd_623628] using wordTrace_append hprefix tailTrace_623628
  have hstable : (prefixWord ++ tailWord_623628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623628).length < 2 ^ (prefixWord ++ tailWord_623628).sum := by decide
  have hdescent : baseEnd_623628 < baseStart_623628 := by decide
  rcases family_descends (prefixWord ++ tailWord_623628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623634 : List Nat := [3, 2, 5, 1, 1, 2, 1, 5]
def baseStart_623634 : Nat := 118140960795 + 623634 * 2 ^ 59
def prefixEnd_623634 : Nat := 4983230072969 + 3 ^ 40 * 623634 * 2
def baseEnd_623634 : Nat := 94881183551442448239101

theorem tailTrace_623634 : CollatzResearch.WordTrace tailWord_623634 prefixEnd_623634 94881183551442448239101 := by
  unfold tailWord_623634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686450155672000263189489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15163867081792000701838637 5686450155672000263189489)
  ·
    refine ⟨4264837616754000197392117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5686450155672000263189489 4264837616754000197392117)
    ·
      refine ⟨399828526570687518505511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4264837616754000197392117 399828526570687518505511)
      ·
        refine ⟨599742789856031277758267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399828526570687518505511 599742789856031277758267)
        ·
          refine ⟨899614184784046916637401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599742789856031277758267 899614184784046916637401)
          ·
            refine ⟨674710638588035187478051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 899614184784046916637401 674710638588035187478051)
            ·
              refine ⟨1012065957882052781217077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674710638588035187478051 1012065957882052781217077)
              ·
                refine ⟨94881183551442448239101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1012065957882052781217077 94881183551442448239101)
                ·
                  rfl

theorem cell20_623634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_623634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623634 prefixEnd_623634 := by exact prefixLift 623634
  have htrace : WordTrace (prefixWord ++ tailWord_623634) baseStart_623634 baseEnd_623634 := by
    simpa [prefixWord, tailWord_623634, baseEnd_623634] using wordTrace_append hprefix tailTrace_623634
  have hstable : (prefixWord ++ tailWord_623634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623634).length < 2 ^ (prefixWord ++ tailWord_623634).sum := by decide
  have hdescent : baseEnd_623634 < baseStart_623634 := by decide
  rcases family_descends (prefixWord ++ tailWord_623634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623652 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_623652 : Nat := 118140960795 + 623652 * 2 ^ 59
def prefixEnd_623652 : Nat := 4983230072969 + 3 ^ 40 * 623652 * 2
def baseEnd_623652 : Nat := 284651766344799282117229

theorem tailTrace_623652 : CollatzResearch.WordTrace tailWord_623652 prefixEnd_623652 284651766344799282117229 := by
  unfold tailWord_623652
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373228568311395063456605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15164304757748526751275473 11373228568311395063456605)
  ·
    refine ⟨4264960713116773148796227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11373228568311395063456605 4264960713116773148796227)
    ·
      refine ⟨6397441069675159723194341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4264960713116773148796227 6397441069675159723194341)
      ·
        refine ⟨1199520200564092448098939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6397441069675159723194341 1199520200564092448098939)
        ·
          refine ⟨1799280300846138672148409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199520200564092448098939 1799280300846138672148409)
          ·
            refine ⟨1349460225634604004111307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1799280300846138672148409 1349460225634604004111307)
            ·
              refine ⟨2024190338451906006166961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349460225634604004111307 2024190338451906006166961)
              ·
                refine ⟨1518142753838929504625221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2024190338451906006166961 1518142753838929504625221)
                ·
                  refine ⟨284651766344799282117229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1518142753838929504625221 284651766344799282117229)
                  ·
                    rfl

theorem cell20_623652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_623652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623652 prefixEnd_623652 := by exact prefixLift 623652
  have htrace : WordTrace (prefixWord ++ tailWord_623652) baseStart_623652 baseEnd_623652 := by
    simpa [prefixWord, tailWord_623652, baseEnd_623652] using wordTrace_append hprefix tailTrace_623652
  have hstable : (prefixWord ++ tailWord_623652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623652).length < 2 ^ (prefixWord ++ tailWord_623652).sum := by decide
  have hdescent : baseEnd_623652 < baseStart_623652 := by decide
  rcases family_descends (prefixWord ++ tailWord_623652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623686 : List Nat := [6, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_623686 : Nat := 118140960795 + 623686 * 2 ^ 59
def prefixEnd_623686 : Nat := 4983230072969 + 3 ^ 40 * 623686 * 2
def baseEnd_623686 : Nat := 284667284871246274983757

theorem tailTrace_623686 : CollatzResearch.WordTrace tailWord_623686 prefixEnd_623686 284667284871246274983757 := by
  unfold tailWord_623686
  simp only [CollatzResearch.WordTrace]
  refine ⟨710865538078112935426591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15165131478999742622433941 710865538078112935426591)
  ·
    refine ⟨1066298307117169403139887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 710865538078112935426591 1066298307117169403139887)
    ·
      refine ⟨1599447460675754104709831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066298307117169403139887 1599447460675754104709831)
      ·
        refine ⟨2399171191013631157064747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599447460675754104709831 2399171191013631157064747)
        ·
          refine ⟨3598756786520446735597121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399171191013631157064747 3598756786520446735597121)
          ·
            refine ⟨2699067589890335051697841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3598756786520446735597121 2699067589890335051697841)
            ·
              refine ⟨2024300692417751288773381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2699067589890335051697841 2024300692417751288773381)
              ·
                refine ⟨379556379828328366645009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2024300692417751288773381 379556379828328366645009)
                ·
                  refine ⟨284667284871246274983757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379556379828328366645009 284667284871246274983757)
                  ·
                    rfl

theorem cell20_623686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_623686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623686 prefixEnd_623686 := by exact prefixLift 623686
  have htrace : WordTrace (prefixWord ++ tailWord_623686) baseStart_623686 baseEnd_623686 := by
    simpa [prefixWord, tailWord_623686, baseEnd_623686] using wordTrace_append hprefix tailTrace_623686
  have hstable : (prefixWord ++ tailWord_623686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623686).length < 2 ^ (prefixWord ++ tailWord_623686).sum := by decide
  have hdescent : baseEnd_623686 < baseStart_623686 := by decide
  rcases family_descends (prefixWord ++ tailWord_623686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623690 : List Nat := [3, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_623690 : Nat := 118140960795 + 623690 * 2 ^ 59
def prefixEnd_623690 : Nat := 4983230072969 + 3 ^ 40 * 623690 * 2
def baseEnd_623690 : Nat := 284669110580240038850407

theorem tailTrace_623690 : CollatzResearch.WordTrace tailWord_623690 prefixEnd_623690 284669110580240038850407 := by
  unfold tailWord_623690
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686960777621280654199131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15165228740323415077864349 5686960777621280654199131)
  ·
    refine ⟨8530441166431920981298697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5686960777621280654199131 8530441166431920981298697)
    ·
      refine ⟨6397830874823940735974023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8530441166431920981298697 6397830874823940735974023)
      ·
        refine ⟨9596746312235911103961035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6397830874823940735974023 9596746312235911103961035)
        ·
          refine ⟨14395119468353866655941553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9596746312235911103961035 14395119468353866655941553)
          ·
            refine ⟨10796339601265399991956165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14395119468353866655941553 10796339601265399991956165)
            ·
              refine ⟨2024313675237262498491781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10796339601265399991956165 2024313675237262498491781)
              ·
                refine ⟨379558814106986718467209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2024313675237262498491781 379558814106986718467209)
                ·
                  refine ⟨284669110580240038850407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379558814106986718467209 284669110580240038850407)
                  ·
                    rfl

theorem cell20_623690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_623690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623690 prefixEnd_623690 := by exact prefixLift 623690
  have htrace : WordTrace (prefixWord ++ tailWord_623690) baseStart_623690 baseEnd_623690 := by
    simpa [prefixWord, tailWord_623690, baseEnd_623690] using wordTrace_append hprefix tailTrace_623690
  have hstable : (prefixWord ++ tailWord_623690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623690).length < 2 ^ (prefixWord ++ tailWord_623690).sum := by decide
  have hdescent : baseEnd_623690 < baseStart_623690 := by decide
  rcases family_descends (prefixWord ++ tailWord_623690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623710 : List Nat := [4, 4, 1, 1, 1, 3, 2, 4]
def baseStart_623710 : Nat := 118140960795 + 623710 * 2 ^ 59
def prefixEnd_623710 : Nat := 4983230072969 + 3 ^ 40 * 623710 * 2
def baseEnd_623710 : Nat := 94892746375069619394553

theorem tailTrace_623710 : CollatzResearch.WordTrace tailWord_623710 prefixEnd_623710 94892746375069619394553 := by
  unfold tailWord_623710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843571571301583254065573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15165715046941777355016389 2843571571301583254065573)
  ·
    refine ⟨533169669619046860137295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2843571571301583254065573 533169669619046860137295)
    ·
      refine ⟨799754504428570290205943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533169669619046860137295 799754504428570290205943)
      ·
        refine ⟨1199631756642855435308915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799754504428570290205943 1199631756642855435308915)
        ·
          refine ⟨1799447634964283152963373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199631756642855435308915 1799447634964283152963373)
          ·
            refine ⟨674792863111606182361265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1799447634964283152963373 674792863111606182361265)
            ·
              refine ⟨506094647333704636770949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674792863111606182361265 506094647333704636770949)
              ·
                refine ⟨94892746375069619394553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 506094647333704636770949 94892746375069619394553)
                ·
                  rfl

theorem cell20_623710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_623710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623710 prefixEnd_623710 := by exact prefixLift 623710
  have htrace : WordTrace (prefixWord ++ tailWord_623710) baseStart_623710 baseEnd_623710 := by
    simpa [prefixWord, tailWord_623710, baseEnd_623710] using wordTrace_append hprefix tailTrace_623710
  have hstable : (prefixWord ++ tailWord_623710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623710).length < 2 ^ (prefixWord ++ tailWord_623710).sum := by decide
  have hdescent : baseEnd_623710 < baseStart_623710 := by decide
  rcases family_descends (prefixWord ++ tailWord_623710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623714 : List Nat := [3, 3, 2, 2, 1, 1, 4, 4]
def baseStart_623714 : Nat := 118140960795 + 623714 * 2 ^ 59
def prefixEnd_623714 : Nat := 4983230072969 + 3 ^ 40 * 623714 * 2
def baseEnd_623714 : Nat := 94893354944734207350103

theorem tailTrace_623714 : CollatzResearch.WordTrace tailWord_623714 prefixEnd_623714 94893354944734207350103 := by
  unfold tailWord_623714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5687179615599543678917549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15165812308265449810446797 5687179615599543678917549)
  ·
    refine ⟨2132692355849828879594081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5687179615599543678917549 2132692355849828879594081)
    ·
      refine ⟨1599519266887371659695561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2132692355849828879594081 1599519266887371659695561)
      ·
        refine ⟨1199639450165528744771671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1599519266887371659695561 1199639450165528744771671)
        ·
          refine ⟨1799459175248293117157507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199639450165528744771671 1799459175248293117157507)
          ·
            refine ⟨2699188762872439675736261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799459175248293117157507 2699188762872439675736261)
            ·
              refine ⟨506097893038582439200549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2699188762872439675736261 506097893038582439200549)
              ·
                refine ⟨94893354944734207350103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 506097893038582439200549 94893354944734207350103)
                ·
                  rfl

theorem cell20_623714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_623714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623714 prefixEnd_623714 := by exact prefixLift 623714
  have htrace : WordTrace (prefixWord ++ tailWord_623714) baseStart_623714 baseEnd_623714 := by
    simpa [prefixWord, tailWord_623714, baseEnd_623714] using wordTrace_append hprefix tailTrace_623714
  have hstable : (prefixWord ++ tailWord_623714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623714).length < 2 ^ (prefixWord ++ tailWord_623714).sum := by decide
  have hdescent : baseEnd_623714 < baseStart_623714 := by decide
  rcases family_descends (prefixWord ++ tailWord_623714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623818 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_623818 : Nat := 118140960795 + 623818 * 2 ^ 59
def prefixEnd_623818 : Nat := 4983230072969 + 3 ^ 40 * 623818 * 2
def baseEnd_623818 : Nat := 284727533268040482583217

theorem tailTrace_623818 : CollatzResearch.WordTrace tailWord_623818 prefixEnd_623818 284727533268040482583217 := by
  unfold tailWord_623818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5688127913505350119364027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15168341102680933651637405 5688127913505350119364027)
  ·
    refine ⟨8532191870258025179046041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5688127913505350119364027 8532191870258025179046041)
    ·
      refine ⟨6399143902693518884284531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8532191870258025179046041 6399143902693518884284531)
      ·
        refine ⟨9598715854040278326426797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6399143902693518884284531 9598715854040278326426797)
        ·
          refine ⟨3599518445265104372410049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9598715854040278326426797 3599518445265104372410049)
          ·
            refine ⟨2699638833948828279307537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3599518445265104372410049 2699638833948828279307537)
            ·
              refine ⟨2024729125461621209480653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2699638833948828279307537 2024729125461621209480653)
              ·
                refine ⟨759273422048107953555245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2024729125461621209480653 759273422048107953555245)
                ·
                  refine ⟨284727533268040482583217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759273422048107953555245 284727533268040482583217)
                  ·
                    rfl

theorem cell20_623818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_623818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623818 prefixEnd_623818 := by exact prefixLift 623818
  have htrace : WordTrace (prefixWord ++ tailWord_623818) baseStart_623818 baseEnd_623818 := by
    simpa [prefixWord, tailWord_623818, baseEnd_623818] using wordTrace_append hprefix tailTrace_623818
  have hstable : (prefixWord ++ tailWord_623818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623818).length < 2 ^ (prefixWord ++ tailWord_623818).sum := by decide
  have hdescent : baseEnd_623818 < baseStart_623818 := by decide
  rcases family_descends (prefixWord ++ tailWord_623818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623873 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 3]
def baseStart_623873 : Nat := 118140960795 + 623873 * 2 ^ 59
def prefixEnd_623873 : Nat := 4983230072969 + 3 ^ 40 * 623873 * 2
def baseEnd_623873 : Nat := 284752636766704735749659

theorem tailTrace_623873 : CollatzResearch.WordTrace tailWord_623873 prefixEnd_623873 284752636766704735749659 := by
  unfold tailWord_623873
  simp only [CollatzResearch.WordTrace]
  refine ⟨22754517668822144870708273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15169678445881429913805515 22754517668822144870708273)
  ·
    refine ⟨17065888251616608653031205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22754517668822144870708273 17065888251616608653031205)
    ·
      refine ⟨3199854047178114122443351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17065888251616608653031205 3199854047178114122443351)
      ·
        refine ⟨4799781070767171183665027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199854047178114122443351 4799781070767171183665027)
        ·
          refine ⟨7199671606150756775497541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799781070767171183665027 7199671606150756775497541)
          ·
            refine ⟨1349938426153266895405789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7199671606150756775497541 1349938426153266895405789)
            ·
              refine ⟨506226909807475085777171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1349938426153266895405789 506226909807475085777171)
              ·
                refine ⟨759340364711212628665757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506226909807475085777171 759340364711212628665757)
                ·
                  refine ⟨284752636766704735749659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759340364711212628665757 284752636766704735749659)
                  ·
                    rfl

theorem cell20_623873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_623873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623873 prefixEnd_623873 := by exact prefixLift 623873
  have htrace : WordTrace (prefixWord ++ tailWord_623873) baseStart_623873 baseEnd_623873 := by
    simpa [prefixWord, tailWord_623873, baseEnd_623873] using wordTrace_append hprefix tailTrace_623873
  have hstable : (prefixWord ++ tailWord_623873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623873).length < 2 ^ (prefixWord ++ tailWord_623873).sum := by decide
  have hdescent : baseEnd_623873 < baseStart_623873 := by decide
  rcases family_descends (prefixWord ++ tailWord_623873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623914 : List Nat := [3, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_623914 : Nat := 118140960795 + 623914 * 2 ^ 59
def prefixEnd_623914 : Nat := 4983230072969 + 3 ^ 40 * 623914 * 2
def baseEnd_623914 : Nat := 284771350283890815382825

theorem tailTrace_623914 : CollatzResearch.WordTrace tailWord_623914 prefixEnd_623914 284771350283890815382825 := by
  unfold tailWord_623914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5689003265418402218237699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15170675374449072581967197 5689003265418402218237699)
  ·
    refine ⟨8533504898127603327356549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5689003265418402218237699 8533504898127603327356549)
    ·
      refine ⟨1600032168398925623879353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8533504898127603327356549 1600032168398925623879353)
      ·
        refine ⟨1200024126299194217909515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1600032168398925623879353 1200024126299194217909515)
        ·
          refine ⟨1800036189448791326864273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200024126299194217909515 1800036189448791326864273)
          ·
            refine ⟨1350027142086593495148205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1800036189448791326864273 1350027142086593495148205)
            ·
              refine ⟨506260178282472560680577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1350027142086593495148205 506260178282472560680577)
              ·
                refine ⟨379695133711854420510433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506260178282472560680577 379695133711854420510433)
                ·
                  refine ⟨284771350283890815382825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379695133711854420510433 284771350283890815382825)
                  ·
                    rfl

theorem cell20_623914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_623914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623914 prefixEnd_623914 := by exact prefixLift 623914
  have htrace : WordTrace (prefixWord ++ tailWord_623914) baseStart_623914 baseEnd_623914 := by
    simpa [prefixWord, tailWord_623914, baseEnd_623914] using wordTrace_append hprefix tailTrace_623914
  have hstable : (prefixWord ++ tailWord_623914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623914).length < 2 ^ (prefixWord ++ tailWord_623914).sum := by decide
  have hdescent : baseEnd_623914 < baseStart_623914 := by decide
  rcases family_descends (prefixWord ++ tailWord_623914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623932 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_623932 : Nat := 118140960795 + 623932 * 2 ^ 59
def prefixEnd_623932 : Nat := 4983230072969 + 3 ^ 40 * 623932 * 2
def baseEnd_623932 : Nat := 284779565974362752782751

theorem tailTrace_623932 : CollatzResearch.WordTrace tailWord_623932 prefixEnd_623932 284779565974362752782751 := by
  unfold tailWord_623932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11378334787804198973553025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15171113050405598631404033 11378334787804198973553025)
  ·
    refine ⟨8533751090853149230164769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11378334787804198973553025 8533751090853149230164769)
    ·
      refine ⟨6400313318139861922623577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8533751090853149230164769 6400313318139861922623577)
      ·
        refine ⟨4800234988604896441967683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6400313318139861922623577 4800234988604896441967683)
        ·
          refine ⟨7200352482907344662951525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4800234988604896441967683 7200352482907344662951525)
          ·
            refine ⟨1350066090545127124303411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7200352482907344662951525 1350066090545127124303411)
            ·
              refine ⟨2025099135817690686455117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350066090545127124303411 2025099135817690686455117)
              ·
                refine ⟨759412175931634007420669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2025099135817690686455117 759412175931634007420669)
                ·
                  refine ⟨284779565974362752782751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759412175931634007420669 284779565974362752782751)
                  ·
                    rfl

theorem cell20_623932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_623932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623932 prefixEnd_623932 := by exact prefixLift 623932
  have htrace : WordTrace (prefixWord ++ tailWord_623932) baseStart_623932 baseEnd_623932 := by
    simpa [prefixWord, tailWord_623932, baseEnd_623932] using wordTrace_append hprefix tailTrace_623932
  have hstable : (prefixWord ++ tailWord_623932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623932).length < 2 ^ (prefixWord ++ tailWord_623932).sum := by decide
  have hdescent : baseEnd_623932 < baseStart_623932 := by decide
  rcases family_descends (prefixWord ++ tailWord_623932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623956 : List Nat := [2, 4, 1, 1, 2, 1, 2, 5, 2]
def baseStart_623956 : Nat := 118140960795 + 623956 * 2 ^ 59
def prefixEnd_623956 : Nat := 4983230072969 + 3 ^ 40 * 623956 * 2
def baseEnd_623956 : Nat := 284790520228325335982653

theorem tailTrace_623956 : CollatzResearch.WordTrace tailWord_623956 prefixEnd_623956 284790520228325335982653 := by
  unfold tailWord_623956
  simp only [CollatzResearch.WordTrace]
  refine ⟨11378772463760725022989861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15171696618347633363986481 11378772463760725022989861)
  ·
    refine ⟨2133519836955135941810599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11378772463760725022989861 2133519836955135941810599)
    ·
      refine ⟨3200279755432703912715899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2133519836955135941810599 3200279755432703912715899)
      ·
        refine ⟨4800419633149055869073849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200279755432703912715899 4800419633149055869073849)
        ·
          refine ⟨3600314724861791901805387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4800419633149055869073849 3600314724861791901805387)
          ·
            refine ⟨5400472087292687852708081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600314724861791901805387 5400472087292687852708081)
            ·
              refine ⟨4050354065469515889531061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5400472087292687852708081 4050354065469515889531061)
              ·
                refine ⟨379720693637767114643537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4050354065469515889531061 379720693637767114643537)
                ·
                  refine ⟨284790520228325335982653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379720693637767114643537 284790520228325335982653)
                  ·
                    rfl

theorem cell20_623956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_623956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623956 prefixEnd_623956 := by exact prefixLift 623956
  have htrace : WordTrace (prefixWord ++ tailWord_623956) baseStart_623956 baseEnd_623956 := by
    simpa [prefixWord, tailWord_623956, baseEnd_623956] using wordTrace_append hprefix tailTrace_623956
  have hstable : (prefixWord ++ tailWord_623956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623956).length < 2 ^ (prefixWord ++ tailWord_623956).sum := by decide
  have hdescent : baseEnd_623956 < baseStart_623956 := by decide
  rcases family_descends (prefixWord ++ tailWord_623956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623965 : List Nat := [1, 4, 5, 1, 2, 1, 2, 2, 2]
def baseStart_623965 : Nat := 118140960795 + 623965 * 2 ^ 59
def prefixEnd_623965 : Nat := 4983230072969 + 3 ^ 40 * 623965 * 2
def baseEnd_623965 : Nat := 284794628073561304682617

theorem tailTrace_623965 : CollatzResearch.WordTrace tailWord_623965 prefixEnd_623965 284794628073561304682617 := by
  unfold tailWord_623965
  simp only [CollatzResearch.WordTrace]
  refine ⟨22757873184488844583057349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15171915456325896388704899 22757873184488844583057349)
  ·
    refine ⟨4267101222091658359323253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22757873184488844583057349 4267101222091658359323253)
    ·
      refine ⟨400040739571092971186555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4267101222091658359323253 400040739571092971186555)
      ·
        refine ⟨600061109356639456779833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400040739571092971186555 600061109356639456779833)
        ·
          refine ⟨450045832017479592584875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600061109356639456779833 450045832017479592584875)
          ·
            refine ⟨675068748026219388877313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450045832017479592584875 675068748026219388877313)
            ·
              refine ⟨506301561019664541657985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675068748026219388877313 506301561019664541657985)
              ·
                refine ⟨379726170764748406243489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506301561019664541657985 379726170764748406243489)
                ·
                  refine ⟨284794628073561304682617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379726170764748406243489 284794628073561304682617)
                  ·
                    rfl

theorem cell20_623965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_623965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623965 prefixEnd_623965 := by exact prefixLift 623965
  have htrace : WordTrace (prefixWord ++ tailWord_623965) baseStart_623965 baseEnd_623965 := by
    simpa [prefixWord, tailWord_623965, baseEnd_623965] using wordTrace_append hprefix tailTrace_623965
  have hstable : (prefixWord ++ tailWord_623965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623965).length < 2 ^ (prefixWord ++ tailWord_623965).sum := by decide
  have hdescent : baseEnd_623965 < baseStart_623965 := by decide
  rcases family_descends (prefixWord ++ tailWord_623965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623991 : List Nat := [1, 1, 3, 1, 1, 2, 3, 5, 3]
def baseStart_623991 : Nat := 118140960795 + 623991 * 2 ^ 59
def prefixEnd_623991 : Nat := 4983230072969 + 3 ^ 40 * 623991 * 2
def baseEnd_623991 : Nat := 284806495182020769815843

theorem tailTrace_623991 : CollatzResearch.WordTrace tailWord_623991 prefixEnd_623991 284806495182020769815843 := by
  unfold tailWord_623991
  simp only [CollatzResearch.WordTrace]
  refine ⟨22758821482394651023503827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15172547654929767349002551 22758821482394651023503827)
  ·
    refine ⟨34138232223591976535255741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22758821482394651023503827 34138232223591976535255741)
    ·
      refine ⟨12801837083846991200720903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34138232223591976535255741 12801837083846991200720903)
      ·
        refine ⟨19202755625770486801081355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12801837083846991200720903 19202755625770486801081355)
        ·
          refine ⟨28804133438655730201622033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19202755625770486801081355 28804133438655730201622033)
          ·
            refine ⟨21603100078991797651216525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28804133438655730201622033 21603100078991797651216525)
            ·
              refine ⟨8101162529621924119206197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21603100078991797651216525 8101162529621924119206197)
              ·
                refine ⟨759483987152055386175581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8101162529621924119206197 759483987152055386175581)
                ·
                  refine ⟨284806495182020769815843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759483987152055386175581 284806495182020769815843)
                  ·
                    rfl

theorem cell20_623991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_623991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_623991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_623991 prefixEnd_623991 := by exact prefixLift 623991
  have htrace : WordTrace (prefixWord ++ tailWord_623991) baseStart_623991 baseEnd_623991 := by
    simpa [prefixWord, tailWord_623991, baseEnd_623991] using wordTrace_append hprefix tailTrace_623991
  have hstable : (prefixWord ++ tailWord_623991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623991).length < 2 ^ (prefixWord ++ tailWord_623991).sum := by decide
  have hdescent : baseEnd_623991 < baseStart_623991 := by decide
  rcases family_descends (prefixWord ++ tailWord_623991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624005 : List Nat := [1, 3, 1, 1, 3, 1, 2, 8]
def baseStart_624005 : Nat := 118140960795 + 624005 * 2 ^ 59
def prefixEnd_624005 : Nat := 4983230072969 + 3 ^ 40 * 624005 * 2
def baseEnd_624005 : Nat := 94937628387832981116373

theorem tailTrace_624005 : CollatzResearch.WordTrace tailWord_624005 prefixEnd_624005 94937628387832981116373 := by
  unfold tailWord_624005
  simp only [CollatzResearch.WordTrace]
  refine ⟨22759332104343931414513469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15172888069562620943008979 22759332104343931414513469)
  ·
    refine ⟨8534749539128974280442551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22759332104343931414513469 8534749539128974280442551)
    ·
      refine ⟨12802124308693461420663827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8534749539128974280442551 12802124308693461420663827)
      ·
        refine ⟨19203186463040192130995741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12802124308693461420663827 19203186463040192130995741)
        ·
          refine ⟨7201194923640072049123403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19203186463040192130995741 7201194923640072049123403)
          ·
            refine ⟨10801792385460108073685105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7201194923640072049123403 10801792385460108073685105)
            ·
              refine ⟨8101344289095081055263829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10801792385460108073685105 8101344289095081055263829)
              ·
                refine ⟨94937628387832981116373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8101344289095081055263829 94937628387832981116373)
                ·
                  rfl

theorem cell20_624005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_624005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624005 prefixEnd_624005 := by exact prefixLift 624005
  have htrace : WordTrace (prefixWord ++ tailWord_624005) baseStart_624005 baseEnd_624005 := by
    simpa [prefixWord, tailWord_624005, baseEnd_624005] using wordTrace_append hprefix tailTrace_624005
  have hstable : (prefixWord ++ tailWord_624005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624005).length < 2 ^ (prefixWord ++ tailWord_624005).sum := by decide
  have hdescent : baseEnd_624005 < baseStart_624005 := by decide
  rcases family_descends (prefixWord ++ tailWord_624005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624053 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_624053 : Nat := 118140960795 + 624053 * 2 ^ 59
def prefixEnd_624053 : Nat := 4983230072969 + 3 ^ 40 * 624053 * 2
def baseEnd_624053 : Nat := 284834793671424109748923

theorem tailTrace_624053 : CollatzResearch.WordTrace tailWord_624053 prefixEnd_624053 284834793671424109748923 := by
  unfold tailWord_624053
  simp only [CollatzResearch.WordTrace]
  refine ⟨22761082808170035612260813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15174055205446690408173875 22761082808170035612260813)
  ·
    refine ⟨8535406053063763354597805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22761082808170035612260813 8535406053063763354597805)
    ·
      refine ⟨3200777269898911257974177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8535406053063763354597805 3200777269898911257974177)
      ·
        refine ⟨2400582952424183443480633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3200777269898911257974177 2400582952424183443480633)
        ·
          refine ⟨1800437214318137582610475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2400582952424183443480633 1800437214318137582610475)
          ·
            refine ⟨2700655821477206373915713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800437214318137582610475 2700655821477206373915713)
            ·
              refine ⟨2025491866107904780436785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2700655821477206373915713 2025491866107904780436785)
              ·
                refine ⟨1519118899580928585327589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2025491866107904780436785 1519118899580928585327589)
                ·
                  refine ⟨284834793671424109748923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1519118899580928585327589 284834793671424109748923)
                  ·
                    rfl

theorem cell20_624053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_624053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624053 prefixEnd_624053 := by exact prefixLift 624053
  have htrace : WordTrace (prefixWord ++ tailWord_624053) baseStart_624053 baseEnd_624053 := by
    simpa [prefixWord, tailWord_624053, baseEnd_624053] using wordTrace_append hprefix tailTrace_624053
  have hstable : (prefixWord ++ tailWord_624053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624053).length < 2 ^ (prefixWord ++ tailWord_624053).sum := by decide
  have hdescent : baseEnd_624053 < baseStart_624053 := by decide
  rcases family_descends (prefixWord ++ tailWord_624053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624101 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 3]
def baseStart_624101 : Nat := 118140960795 + 624101 * 2 ^ 59
def prefixEnd_624101 : Nat := 4983230072969 + 3 ^ 40 * 624101 * 2
def baseEnd_624101 : Nat := 284856702179349276148727

theorem tailTrace_624101 : CollatzResearch.WordTrace tailWord_624101 prefixEnd_624101 284856702179349276148727 := by
  unfold tailWord_624101
  simp only [CollatzResearch.WordTrace]
  refine ⟨22762833511996139810008157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15175222341330759873338771 22762833511996139810008157)
  ·
    refine ⟨8536062566998552428753059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22762833511996139810008157 8536062566998552428753059)
    ·
      refine ⟨12804093850497828643129589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8536062566998552428753059 12804093850497828643129589)
      ·
        refine ⟨1200383798484171435293399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12804093850497828643129589 1200383798484171435293399)
        ·
          refine ⟨1800575697726257152940099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200383798484171435293399 1800575697726257152940099)
          ·
            refine ⟨2700863546589385729410149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800575697726257152940099 2700863546589385729410149)
            ·
              refine ⟨506411914985509824264403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2700863546589385729410149 506411914985509824264403)
              ·
                refine ⟨759617872478264736396605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506411914985509824264403 759617872478264736396605)
                ·
                  refine ⟨284856702179349276148727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759617872478264736396605 284856702179349276148727)
                  ·
                    rfl

theorem cell20_624101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_624101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624101 prefixEnd_624101 := by exact prefixLift 624101
  have htrace : WordTrace (prefixWord ++ tailWord_624101) baseStart_624101 baseEnd_624101 := by
    simpa [prefixWord, tailWord_624101, baseEnd_624101] using wordTrace_append hprefix tailTrace_624101
  have hstable : (prefixWord ++ tailWord_624101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624101).length < 2 ^ (prefixWord ++ tailWord_624101).sum := by decide
  have hdescent : baseEnd_624101 < baseStart_624101 := by decide
  rcases family_descends (prefixWord ++ tailWord_624101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624142 : List Nat := [4, 1, 1, 2, 4, 2, 2, 2, 2]
def baseStart_624142 : Nat := 118140960795 + 624142 * 2 ^ 59
def prefixEnd_624142 : Nat := 4983230072969 + 3 ^ 40 * 624142 * 2
def baseEnd_624142 : Nat := 284875415696535355781893

theorem tailTrace_624142 : CollatzResearch.WordTrace tailWord_624142 prefixEnd_624142 284875415696535355781893 := by
  unfold tailWord_624142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2845541113105950476531335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15176219269898402541500453 2845541113105950476531335)
  ·
    refine ⟨4268311669658925714797003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2845541113105950476531335 4268311669658925714797003)
    ·
      refine ⟨6402467504488388572195505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4268311669658925714797003 6402467504488388572195505)
      ·
        refine ⟨4801850628366291429146629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6402467504488388572195505 4801850628366291429146629)
        ·
          refine ⟨900346992818679642964993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4801850628366291429146629 900346992818679642964993)
          ·
            refine ⟨675260244614009732223745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 900346992818679642964993 675260244614009732223745)
            ·
              refine ⟨506445183460507299167809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675260244614009732223745 506445183460507299167809)
              ·
                refine ⟨379833887595380474375857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506445183460507299167809 379833887595380474375857)
                ·
                  refine ⟨284875415696535355781893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379833887595380474375857 284875415696535355781893)
                  ·
                    rfl

theorem cell20_624142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_624142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624142 prefixEnd_624142 := by exact prefixLift 624142
  have htrace : WordTrace (prefixWord ++ tailWord_624142) baseStart_624142 baseEnd_624142 := by
    simpa [prefixWord, tailWord_624142, baseEnd_624142] using wordTrace_append hprefix tailTrace_624142
  have hstable : (prefixWord ++ tailWord_624142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624142).length < 2 ^ (prefixWord ++ tailWord_624142).sum := by decide
  have hdescent : baseEnd_624142 < baseStart_624142 := by decide
  rcases family_descends (prefixWord ++ tailWord_624142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624160 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_624160 : Nat := 118140960795 + 624160 * 2 ^ 59
def prefixEnd_624160 : Nat := 4983230072969 + 3 ^ 40 * 624160 * 2
def baseEnd_624160 : Nat := 284883631387007293181819

theorem tailTrace_624160 : CollatzResearch.WordTrace tailWord_624160 prefixEnd_624160 284883631387007293181819 := by
  unfold tailWord_624160
  simp only [CollatzResearch.WordTrace]
  refine ⟨11382492709391196443202967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15176656945854928590937289 11382492709391196443202967)
  ·
    refine ⟨17073739064086794664804451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11382492709391196443202967 17073739064086794664804451)
    ·
      refine ⟨25610608596130191997206677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17073739064086794664804451 25610608596130191997206677)
      ·
        refine ⟨1200497277943602749869063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25610608596130191997206677 1200497277943602749869063)
        ·
          refine ⟨1800745916915404124803595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200497277943602749869063 1800745916915404124803595)
          ·
            refine ⟨2701118875373106187205393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800745916915404124803595 2701118875373106187205393)
            ·
              refine ⟨2025839156529829640404045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2701118875373106187205393 2025839156529829640404045)
              ·
                refine ⟨759689683698686115151517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2025839156529829640404045 759689683698686115151517)
                ·
                  refine ⟨284883631387007293181819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759689683698686115151517 284883631387007293181819)
                  ·
                    rfl

theorem cell20_624160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_624160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624160 prefixEnd_624160 := by exact prefixLift 624160
  have htrace : WordTrace (prefixWord ++ tailWord_624160) baseStart_624160 baseEnd_624160 := by
    simpa [prefixWord, tailWord_624160, baseEnd_624160] using wordTrace_append hprefix tailTrace_624160
  have hstable : (prefixWord ++ tailWord_624160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624160).length < 2 ^ (prefixWord ++ tailWord_624160).sum := by decide
  have hdescent : baseEnd_624160 < baseStart_624160 := by decide
  rcases family_descends (prefixWord ++ tailWord_624160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624184 : List Nat := [2, 1, 2, 1, 4, 3, 2, 3, 2]
def baseStart_624184 : Nat := 118140960795 + 624184 * 2 ^ 59
def prefixEnd_624184 : Nat := 4983230072969 + 3 ^ 40 * 624184 * 2
def baseEnd_624184 : Nat := 284894585640969876381721

theorem tailTrace_624184 : CollatzResearch.WordTrace tailWord_624184 prefixEnd_624184 284894585640969876381721 := by
  unfold tailWord_624184
  simp only [CollatzResearch.WordTrace]
  refine ⟨11382930385347722492639803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15177240513796963323519737 11382930385347722492639803)
  ·
    refine ⟨17074395578021583738959705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11382930385347722492639803 17074395578021583738959705)
    ·
      refine ⟨12805796683516187804219779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17074395578021583738959705 12805796683516187804219779)
      ·
        refine ⟨19208695025274281706329669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12805796683516187804219779 19208695025274281706329669)
        ·
          refine ⟨3601630317238927819936813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19208695025274281706329669 3601630317238927819936813)
          ·
            refine ⟨1350611368964597932476305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3601630317238927819936813 1350611368964597932476305)
            ·
              refine ⟨1012958526723448449357229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350611368964597932476305 1012958526723448449357229)
              ·
                refine ⟨379859447521293168508961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1012958526723448449357229 379859447521293168508961)
                ·
                  refine ⟨284894585640969876381721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379859447521293168508961 284894585640969876381721)
                  ·
                    rfl

theorem cell20_624184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_624184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624184 prefixEnd_624184 := by exact prefixLift 624184
  have htrace : WordTrace (prefixWord ++ tailWord_624184) baseStart_624184 baseEnd_624184 := by
    simpa [prefixWord, tailWord_624184, baseEnd_624184] using wordTrace_append hprefix tailTrace_624184
  have hstable : (prefixWord ++ tailWord_624184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624184).length < 2 ^ (prefixWord ++ tailWord_624184).sum := by decide
  have hdescent : baseEnd_624184 < baseStart_624184 := by decide
  rcases family_descends (prefixWord ++ tailWord_624184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624229 : List Nat := [1, 3, 1, 3, 3, 3, 2, 4]
def baseStart_624229 : Nat := 118140960795 + 624229 * 2 ^ 59
def prefixEnd_624229 : Nat := 4983230072969 + 3 ^ 40 * 624229 * 2
def baseEnd_624229 : Nat := 94971708289049906627179

theorem tailTrace_624229 : CollatzResearch.WordTrace tailWord_624229 prefixEnd_624229 94971708289049906627179 := by
  unfold tailWord_624229
  simp only [CollatzResearch.WordTrace]
  refine ⟨22767502055532417670667741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15178334703688278447111827 22767502055532417670667741)
  ·
    refine ⟨8537813270824656626500403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22767502055532417670667741 8537813270824656626500403)
    ·
      refine ⟨12806719906236984939750605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8537813270824656626500403 12806719906236984939750605)
      ·
        refine ⟨4802519964838869352406477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12806719906236984939750605 4802519964838869352406477)
        ·
          refine ⟨1800944986814576007152429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4802519964838869352406477 1800944986814576007152429)
          ·
            refine ⟨675354370055466002682161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1800944986814576007152429 675354370055466002682161)
            ·
              refine ⟨506515777541599502011621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675354370055466002682161 506515777541599502011621)
              ·
                refine ⟨94971708289049906627179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 506515777541599502011621 94971708289049906627179)
                ·
                  rfl

theorem cell20_624229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 4].length) (baseStart_624229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624229 prefixEnd_624229 := by exact prefixLift 624229
  have htrace : WordTrace (prefixWord ++ tailWord_624229) baseStart_624229 baseEnd_624229 := by
    simpa [prefixWord, tailWord_624229, baseEnd_624229] using wordTrace_append hprefix tailTrace_624229
  have hstable : (prefixWord ++ tailWord_624229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624229).length < 2 ^ (prefixWord ++ tailWord_624229).sum := by decide
  have hdescent : baseEnd_624229 < baseStart_624229 := by decide
  rcases family_descends (prefixWord ++ tailWord_624229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624257 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_624257 : Nat := 118140960795 + 624257 * 2 ^ 59
def prefixEnd_624257 : Nat := 4983230072969 + 3 ^ 40 * 624257 * 2
def baseEnd_624257 : Nat := 284927904830106066948089

theorem tailTrace_624257 : CollatzResearch.WordTrace tailWord_624257 prefixEnd_624257 284927904830106066948089 := by
  unfold tailWord_624257
  simp only [CollatzResearch.WordTrace]
  refine ⟨22768523299430978452687025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15179015532953985635124683 22768523299430978452687025)
  ·
    refine ⟨17076392474573233839515269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22768523299430978452687025 17076392474573233839515269)
    ·
      refine ⟨3201823588982481344909113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17076392474573233839515269 3201823588982481344909113)
      ·
        refine ⟨2401367691736861008681835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3201823588982481344909113 2401367691736861008681835)
        ·
          refine ⟨3602051537605291513022753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401367691736861008681835 3602051537605291513022753)
          ·
            refine ⟨2701538653203968634767065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3602051537605291513022753 2701538653203968634767065)
            ·
              refine ⟨2026153989902976476075299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2701538653203968634767065 2026153989902976476075299)
              ·
                refine ⟨3039230984854464714112949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2026153989902976476075299 3039230984854464714112949)
                ·
                  refine ⟨284927904830106066948089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3039230984854464714112949 284927904830106066948089)
                  ·
                    rfl

theorem cell20_624257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_624257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624257 prefixEnd_624257 := by exact prefixLift 624257
  have htrace : WordTrace (prefixWord ++ tailWord_624257) baseStart_624257 baseEnd_624257 := by
    simpa [prefixWord, tailWord_624257, baseEnd_624257] using wordTrace_append hprefix tailTrace_624257
  have hstable : (prefixWord ++ tailWord_624257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624257).length < 2 ^ (prefixWord ++ tailWord_624257).sum := by decide
  have hdescent : baseEnd_624257 < baseStart_624257 := by decide
  rcases family_descends (prefixWord ++ tailWord_624257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624260 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 4]
def baseStart_624260 : Nat := 118140960795 + 624260 * 2 ^ 59
def prefixEnd_624260 : Nat := 4983230072969 + 3 ^ 40 * 624260 * 2
def baseEnd_624260 : Nat := 284929274111851389848077

theorem tailTrace_624260 : CollatzResearch.WordTrace tailWord_624260 prefixEnd_624260 284929274111851389848077 := by
  unfold tailWord_624260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11384316359210054982523117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15179088478946739976697489 11384316359210054982523117)
  ·
    refine ⟨4269118634703770618446169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11384316359210054982523117 4269118634703770618446169)
    ·
      refine ⟨3201838976027827963834627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4269118634703770618446169 3201838976027827963834627)
      ·
        refine ⟨4802758464041741945751941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201838976027827963834627 4802758464041741945751941)
        ·
          refine ⟨900517212007826614828489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4802758464041741945751941 900517212007826614828489)
          ·
            refine ⟨675387909005869961121367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 900517212007826614828489 675387909005869961121367)
            ·
              refine ⟨1013081863508804941682051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675387909005869961121367 1013081863508804941682051)
              ·
                refine ⟨1519622795263207412523077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013081863508804941682051 1519622795263207412523077)
                ·
                  refine ⟨284929274111851389848077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1519622795263207412523077 284929274111851389848077)
                  ·
                    rfl

theorem cell20_624260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_624260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624260 prefixEnd_624260 := by exact prefixLift 624260
  have htrace : WordTrace (prefixWord ++ tailWord_624260) baseStart_624260 baseEnd_624260 := by
    simpa [prefixWord, tailWord_624260, baseEnd_624260] using wordTrace_append hprefix tailTrace_624260
  have hstable : (prefixWord ++ tailWord_624260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624260).length < 2 ^ (prefixWord ++ tailWord_624260).sum := by decide
  have hdescent : baseEnd_624260 < baseStart_624260 := by decide
  rcases family_descends (prefixWord ++ tailWord_624260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624309 : List Nat := [1, 3, 3, 3, 10]
def baseStart_624309 : Nat := 118140960795 + 624309 * 2 ^ 59
def prefixEnd_624309 : Nat := 4983230072969 + 3 ^ 40 * 624309 * 2
def baseEnd_624309 : Nat := 3517921469716357990303

theorem tailTrace_624309 : CollatzResearch.WordTrace tailWord_624309 prefixEnd_624309 3517921469716357990303 := by
  unfold tailWord_624309
  simp only [CollatzResearch.WordTrace]
  refine ⟨22770419895242591333579981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15180279930161727555719987 22770419895242591333579981)
  ·
    refine ⟨8538907460715971750092493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22770419895242591333579981 8538907460715971750092493)
    ·
      refine ⟨3202090297768489406284685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8538907460715971750092493 3202090297768489406284685)
      ·
        refine ⟨1200783861663183527356757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3202090297768489406284685 1200783861663183527356757)
        ·
          refine ⟨3517921469716357990303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1200783861663183527356757 3517921469716357990303)
          ·
            rfl

theorem cell20_624309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 10].length) (baseStart_624309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624309 prefixEnd_624309 := by exact prefixLift 624309
  have htrace : WordTrace (prefixWord ++ tailWord_624309) baseStart_624309 baseEnd_624309 := by
    simpa [prefixWord, tailWord_624309, baseEnd_624309] using wordTrace_append hprefix tailTrace_624309
  have hstable : (prefixWord ++ tailWord_624309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624309).length < 2 ^ (prefixWord ++ tailWord_624309).sum := by decide
  have hdescent : baseEnd_624309 < baseStart_624309 := by decide
  rcases family_descends (prefixWord ++ tailWord_624309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624319 : List Nat := [1, 1, 2, 2, 2, 3, 3, 4, 2]
def baseStart_624319 : Nat := 118140960795 + 624319 * 2 ^ 59
def prefixEnd_624319 : Nat := 4983230072969 + 3 ^ 40 * 624319 * 2
def baseEnd_624319 : Nat := 284956203319509406881169

theorem tailTrace_624319 : CollatzResearch.WordTrace tailWord_624319 prefixEnd_624319 284956203319509406881169 := by
  unfold tailWord_624319
  simp only [CollatzResearch.WordTrace]
  refine ⟨22770784625206363041444011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15180523083470908694296007 22770784625206363041444011)
  ·
    refine ⟨34156176937809544562166017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22770784625206363041444011 34156176937809544562166017)
    ·
      refine ⟨25617132703357158421624513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34156176937809544562166017 25617132703357158421624513)
      ·
        refine ⟨19212849527517868816218385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25617132703357158421624513 19212849527517868816218385)
        ·
          refine ⟨14409637145638401612163789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19212849527517868816218385 14409637145638401612163789)
          ·
            refine ⟨5403613929614400604561421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14409637145638401612163789 5403613929614400604561421)
            ·
              refine ⟨2026355223605400226710533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5403613929614400604561421 2026355223605400226710533)
              ·
                refine ⟨379941604426012542508225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2026355223605400226710533 379941604426012542508225)
                ·
                  refine ⟨284956203319509406881169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379941604426012542508225 284956203319509406881169)
                  ·
                    rfl

theorem cell20_624319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 2].length) (baseStart_624319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624319 prefixEnd_624319 := by exact prefixLift 624319
  have htrace : WordTrace (prefixWord ++ tailWord_624319) baseStart_624319 baseEnd_624319 := by
    simpa [prefixWord, tailWord_624319, baseEnd_624319] using wordTrace_append hprefix tailTrace_624319
  have hstable : (prefixWord ++ tailWord_624319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624319).length < 2 ^ (prefixWord ++ tailWord_624319).sum := by decide
  have hdescent : baseEnd_624319 < baseStart_624319 := by decide
  rcases family_descends (prefixWord ++ tailWord_624319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624323 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_624323 : Nat := 118140960795 + 624323 * 2 ^ 59
def prefixEnd_624323 : Nat := 4983230072969 + 3 ^ 40 * 624323 * 2
def baseEnd_624323 : Nat := 284958029028503170747819

theorem tailTrace_624323 : CollatzResearch.WordTrace tailWord_624323 prefixEnd_624323 284958029028503170747819 := by
  unfold tailWord_624323
  simp only [CollatzResearch.WordTrace]
  refine ⟨22770930517191871724589623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15180620344794581149726415 22770930517191871724589623)
  ·
    refine ⟨34156395775787807586884435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22770930517191871724589623 34156395775787807586884435)
    ·
      refine ⟨51234593663681711380326653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34156395775787807586884435 51234593663681711380326653)
      ·
        refine ⟨19212972623880641767622495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51234593663681711380326653 19212972623880641767622495)
        ·
          refine ⟨28819458935820962651433743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19212972623880641767622495 28819458935820962651433743)
          ·
            refine ⟨43229188403731443977150615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28819458935820962651433743 43229188403731443977150615)
            ·
              refine ⟨64843782605597165965725923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43229188403731443977150615 64843782605597165965725923)
              ·
                refine ⟨97265673908395748948588885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64843782605597165965725923 97265673908395748948588885)
                ·
                  refine ⟨284958029028503170747819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 97265673908395748948588885 284958029028503170747819)
                  ·
                    rfl

theorem cell20_624323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_624323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624323 prefixEnd_624323 := by exact prefixLift 624323
  have htrace : WordTrace (prefixWord ++ tailWord_624323) baseStart_624323 baseEnd_624323 := by
    simpa [prefixWord, tailWord_624323, baseEnd_624323] using wordTrace_append hprefix tailTrace_624323
  have hstable : (prefixWord ++ tailWord_624323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624323).length < 2 ^ (prefixWord ++ tailWord_624323).sum := by decide
  have hdescent : baseEnd_624323 < baseStart_624323 := by decide
  rcases family_descends (prefixWord ++ tailWord_624323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624361 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_624361 : Nat := 118140960795 + 624361 * 2 ^ 59
def prefixEnd_624361 : Nat := 4983230072969 + 3 ^ 40 * 624361 * 2
def baseEnd_624361 : Nat := 284975373263943927480997

theorem tailTrace_624361 : CollatzResearch.WordTrace tailWord_624361 prefixEnd_624361 284975373263943927480997 := by
  unfold tailWord_624361
  simp only [CollatzResearch.WordTrace]
  refine ⟨22772316491054204214472937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15181544327369469476315291 22772316491054204214472937)
  ·
    refine ⟨17079237368290653160854703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22772316491054204214472937 17079237368290653160854703)
    ·
      refine ⟨25618856052435979741282055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17079237368290653160854703 25618856052435979741282055)
      ·
        refine ⟨38428284078653969611923083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25618856052435979741282055 38428284078653969611923083)
        ·
          refine ⟨57642426117980954417884625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38428284078653969611923083 57642426117980954417884625)
          ·
            refine ⟨43231819588485715813413469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57642426117980954417884625 43231819588485715813413469)
            ·
              refine ⟨16211932345682143430030051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43231819588485715813413469 16211932345682143430030051)
              ·
                refine ⟨24317898518523215145045077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16211932345682143430030051 24317898518523215145045077)
                ·
                  refine ⟨284975373263943927480997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24317898518523215145045077 284975373263943927480997)
                  ·
                    rfl

theorem cell20_624361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_624361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624361 prefixEnd_624361 := by exact prefixLift 624361
  have htrace : WordTrace (prefixWord ++ tailWord_624361) baseStart_624361 baseEnd_624361 := by
    simpa [prefixWord, tailWord_624361, baseEnd_624361] using wordTrace_append hprefix tailTrace_624361
  have hstable : (prefixWord ++ tailWord_624361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624361).length < 2 ^ (prefixWord ++ tailWord_624361).sum := by decide
  have hdescent : baseEnd_624361 < baseStart_624361 := by decide
  rcases family_descends (prefixWord ++ tailWord_624361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624371 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 3]
def baseStart_624371 : Nat := 118140960795 + 624371 * 2 ^ 59
def prefixEnd_624371 : Nat := 4983230072969 + 3 ^ 40 * 624371 * 2
def baseEnd_624371 : Nat := 284979937536428337147623

theorem tailTrace_624371 : CollatzResearch.WordTrace tailWord_624371 prefixEnd_624371 284979937536428337147623 := by
  unfold tailWord_624371
  simp only [CollatzResearch.WordTrace]
  refine ⟨22772681221017975922336967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15181787480678650614891311 22772681221017975922336967)
  ·
    refine ⟨34159021831526963883505451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22772681221017975922336967 34159021831526963883505451)
    ·
      refine ⟨51238532747290445825258177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34159021831526963883505451 51238532747290445825258177)
      ·
        refine ⟨38428899560467834368943633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51238532747290445825258177 38428899560467834368943633)
        ·
          refine ⟨28821674670350875776707725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38428899560467834368943633 28821674670350875776707725)
          ·
            refine ⟨10808128001381578416265397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28821674670350875776707725 10808128001381578416265397)
            ·
              refine ⟨1013262000129522976524881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10808128001381578416265397 1013262000129522976524881)
              ·
                refine ⟨759946500097142232393661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013262000129522976524881 759946500097142232393661)
                ·
                  refine ⟨284979937536428337147623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759946500097142232393661 284979937536428337147623)
                  ·
                    rfl

theorem cell20_624371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_624371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624371 prefixEnd_624371 := by exact prefixLift 624371
  have htrace : WordTrace (prefixWord ++ tailWord_624371) baseStart_624371 baseEnd_624371 := by
    simpa [prefixWord, tailWord_624371, baseEnd_624371] using wordTrace_append hprefix tailTrace_624371
  have hstable : (prefixWord ++ tailWord_624371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624371).length < 2 ^ (prefixWord ++ tailWord_624371).sum := by decide
  have hdescent : baseEnd_624371 < baseStart_624371 := by decide
  rcases family_descends (prefixWord ++ tailWord_624371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624374 : List Nat := [5, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_624374 : Nat := 118140960795 + 624374 * 2 ^ 59
def prefixEnd_624374 : Nat := 4983230072969 + 3 ^ 40 * 624374 * 2
def baseEnd_624374 : Nat := 284981306818173660047611

theorem tailTrace_624374 : CollatzResearch.WordTrace tailWord_624374 prefixEnd_624374 284981306818173660047611 := by
  unfold tailWord_624374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423299415000444214668511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15181860426671404956464117 1423299415000444214668511)
  ·
    refine ⟨2134949122500666322002767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1423299415000444214668511 2134949122500666322002767)
    ·
      refine ⟨3202423683750999483004151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2134949122500666322002767 3202423683750999483004151)
      ·
        refine ⟨4803635525626499224506227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3202423683750999483004151 4803635525626499224506227)
        ·
          refine ⟨7205453288439748836759341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4803635525626499224506227 7205453288439748836759341)
          ·
            refine ⟨2702044983164905813784753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7205453288439748836759341 2702044983164905813784753)
            ·
              refine ⟨2026533737373679360338565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2702044983164905813784753 2026533737373679360338565)
              ·
                refine ⟨379975075757564880063481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2026533737373679360338565 379975075757564880063481)
                ·
                  refine ⟨284981306818173660047611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379975075757564880063481 284981306818173660047611)
                  ·
                    rfl

theorem cell20_624374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_624374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624374 prefixEnd_624374 := by exact prefixLift 624374
  have htrace : WordTrace (prefixWord ++ tailWord_624374) baseStart_624374 baseEnd_624374 := by
    simpa [prefixWord, tailWord_624374, baseEnd_624374] using wordTrace_append hprefix tailTrace_624374
  have hstable : (prefixWord ++ tailWord_624374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624374).length < 2 ^ (prefixWord ++ tailWord_624374).sum := by decide
  have hdescent : baseEnd_624374 < baseStart_624374 := by decide
  rcases family_descends (prefixWord ++ tailWord_624374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624390 : List Nat := [6, 2, 2, 1, 2, 1, 2, 4]
def baseStart_624390 : Nat := 118140960795 + 624390 * 2 ^ 59
def prefixEnd_624390 : Nat := 4983230072969 + 3 ^ 40 * 624390 * 2
def baseEnd_624390 : Nat := 94996203218049571838071

theorem tailTrace_624390 : CollatzResearch.WordTrace tailWord_624390 prefixEnd_624390 94996203218049571838071 := by
  unfold tailWord_624390
  simp only [CollatzResearch.WordTrace]
  refine ⟨711667943998410692727457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15182249471966094778185749 711667943998410692727457)
  ·
    refine ⟨533750957998808019545593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 711667943998410692727457 533750957998808019545593)
    ·
      refine ⟨400313218499106014659195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 533750957998808019545593 400313218499106014659195)
      ·
        refine ⟨600469827748659021988793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400313218499106014659195 600469827748659021988793)
        ·
          refine ⟨450352370811494266491595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600469827748659021988793 450352370811494266491595)
          ·
            refine ⟨675528556217241399737393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450352370811494266491595 675528556217241399737393)
            ·
              refine ⟨506646417162931049803045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675528556217241399737393 506646417162931049803045)
              ·
                refine ⟨94996203218049571838071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 506646417162931049803045 94996203218049571838071)
                ·
                  rfl

theorem cell20_624390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_624390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624390 prefixEnd_624390 := by exact prefixLift 624390
  have htrace : WordTrace (prefixWord ++ tailWord_624390) baseStart_624390 baseEnd_624390 := by
    simpa [prefixWord, tailWord_624390, baseEnd_624390] using wordTrace_append hprefix tailTrace_624390
  have hstable : (prefixWord ++ tailWord_624390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624390).length < 2 ^ (prefixWord ++ tailWord_624390).sum := by decide
  have hdescent : baseEnd_624390 < baseStart_624390 := by decide
  rcases family_descends (prefixWord ++ tailWord_624390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624399 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_624399 : Nat := 118140960795 + 624399 * 2 ^ 59
def prefixEnd_624399 : Nat := 4983230072969 + 3 ^ 40 * 624399 * 2
def baseEnd_624399 : Nat := 284992717499384684214175

theorem tailTrace_624399 : CollatzResearch.WordTrace tailWord_624399 prefixEnd_624399 284992717499384684214175 := by
  unfold tailWord_624399
  simp only [CollatzResearch.WordTrace]
  refine ⟨22773702464916536704356251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15182468309944357802904167 22773702464916536704356251)
  ·
    refine ⟨34160553697374805056534377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22773702464916536704356251 34160553697374805056534377)
    ·
      refine ⟨25620415273031103792400783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34160553697374805056534377 25620415273031103792400783)
      ·
        refine ⟨38430622909546655688601175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25620415273031103792400783 38430622909546655688601175)
        ·
          refine ⟨57645934364319983532901763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38430622909546655688601175 57645934364319983532901763)
          ·
            refine ⟨86468901546479975299352645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57645934364319983532901763 86468901546479975299352645)
            ·
              refine ⟨16212919039964995368628621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86468901546479975299352645 16212919039964995368628621)
              ·
                refine ⟨6079844639986873263235733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16212919039964995368628621 6079844639986873263235733)
                ·
                  refine ⟨284992717499384684214175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6079844639986873263235733 284992717499384684214175)
                  ·
                    rfl

theorem cell20_624399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_624399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624399 prefixEnd_624399 := by exact prefixLift 624399
  have htrace : WordTrace (prefixWord ++ tailWord_624399) baseStart_624399 baseEnd_624399 := by
    simpa [prefixWord, tailWord_624399, baseEnd_624399] using wordTrace_append hprefix tailTrace_624399
  have hstable : (prefixWord ++ tailWord_624399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624399).length < 2 ^ (prefixWord ++ tailWord_624399).sum := by decide
  have hdescent : baseEnd_624399 < baseStart_624399 := by decide
  rcases family_descends (prefixWord ++ tailWord_624399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624404 : List Nat := [2, 4, 4, 1, 2, 1, 1, 3, 2]
def baseStart_624404 : Nat := 118140960795 + 624404 * 2 ^ 59
def prefixEnd_624404 : Nat := 4983230072969 + 3 ^ 40 * 624404 * 2
def baseEnd_624404 : Nat := 284994999635626889047489

theorem tailTrace_624404 : CollatzResearch.WordTrace tailWord_624404 prefixEnd_624404 284994999635626889047489 := by
  unfold tailWord_624404
  simp only [CollatzResearch.WordTrace]
  refine ⟨11386942414949211279144133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15182589886598948372192177 11386942414949211279144133)
  ·
    refine ⟨2135051702802977114839525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11386942414949211279144133 2135051702802977114839525)
    ·
      refine ⟨400322194275558209032411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2135051702802977114839525 400322194275558209032411)
      ·
        refine ⟨600483291413337313548617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400322194275558209032411 600483291413337313548617)
        ·
          refine ⟨450362468560002985161463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600483291413337313548617 450362468560002985161463)
          ·
            refine ⟨675543702840004477742195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450362468560002985161463 675543702840004477742195)
            ·
              refine ⟨1013315554260006716613293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675543702840004477742195 1013315554260006716613293)
              ·
                refine ⟨379993332847502518729985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1013315554260006716613293 379993332847502518729985)
                ·
                  refine ⟨284994999635626889047489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379993332847502518729985 284994999635626889047489)
                  ·
                    rfl

theorem cell20_624404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_624404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624404 prefixEnd_624404 := by exact prefixLift 624404
  have htrace : WordTrace (prefixWord ++ tailWord_624404) baseStart_624404 baseEnd_624404 := by
    simpa [prefixWord, tailWord_624404, baseEnd_624404] using wordTrace_append hprefix tailTrace_624404
  have hstable : (prefixWord ++ tailWord_624404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624404).length < 2 ^ (prefixWord ++ tailWord_624404).sum := by decide
  have hdescent : baseEnd_624404 < baseStart_624404 := by decide
  rcases family_descends (prefixWord ++ tailWord_624404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624433 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 4]
def baseStart_624433 : Nat := 118140960795 + 624433 * 2 ^ 59
def prefixEnd_624433 : Nat := 4983230072969 + 3 ^ 40 * 624433 * 2
def baseEnd_624433 : Nat := 285008236025831677080703

theorem tailTrace_624433 : CollatzResearch.WordTrace tailWord_624433 prefixEnd_624433 285008236025831677080703 := by
  unfold tailWord_624433
  simp only [CollatzResearch.WordTrace]
  refine ⟨22774942546793360511093953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15183295031195573674062635 22774942546793360511093953)
  ·
    refine ⟨17081206910095020383320465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22774942546793360511093953 17081206910095020383320465)
    ·
      refine ⟨12810905182571265287490349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17081206910095020383320465 12810905182571265287490349)
      ·
        refine ⟨4804089443464224482808881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12810905182571265287490349 4804089443464224482808881)
        ·
          refine ⟨3603067082598168362106661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4804089443464224482808881 3603067082598168362106661)
          ·
            refine ⟨675575077987156567894999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3603067082598168362106661 675575077987156567894999)
            ·
              refine ⟨1013362616980734851842499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675575077987156567894999 1013362616980734851842499)
              ·
                refine ⟨1520043925471102277763749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013362616980734851842499 1520043925471102277763749)
                ·
                  refine ⟨285008236025831677080703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520043925471102277763749 285008236025831677080703)
                  ·
                    rfl

theorem cell20_624433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_624433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624433 prefixEnd_624433 := by exact prefixLift 624433
  have htrace : WordTrace (prefixWord ++ tailWord_624433) baseStart_624433 baseEnd_624433 := by
    simpa [prefixWord, tailWord_624433, baseEnd_624433] using wordTrace_append hprefix tailTrace_624433
  have hstable : (prefixWord ++ tailWord_624433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624433).length < 2 ^ (prefixWord ++ tailWord_624433).sum := by decide
  have hdescent : baseEnd_624433 < baseStart_624433 := by decide
  rcases family_descends (prefixWord ++ tailWord_624433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624484 : List Nat := [2, 3, 1, 1, 6, 1, 2, 2, 2]
def baseStart_624484 : Nat := 118140960795 + 624484 * 2 ^ 59
def prefixEnd_624484 : Nat := 4983230072969 + 3 ^ 40 * 624484 * 2
def baseEnd_624484 : Nat := 285031513815502166380495

theorem tailTrace_624484 : CollatzResearch.WordTrace tailWord_624484 prefixEnd_624484 285031513815502166380495 := by
  unfold tailWord_624484
  simp only [CollatzResearch.WordTrace]
  refine ⟨11388401334804298110600253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15184535113072397480800337 11388401334804298110600253)
  ·
    refine ⟨4270650500551611791475095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11388401334804298110600253 4270650500551611791475095)
    ·
      refine ⟨6405975750827417687212643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4270650500551611791475095 6405975750827417687212643)
      ·
        refine ⟨9608963626241126530818965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6405975750827417687212643 9608963626241126530818965)
        ·
          refine ⟨450420169980052806132139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9608963626241126530818965 450420169980052806132139)
          ·
            refine ⟨675630254970079209198209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450420169980052806132139 675630254970079209198209)
            ·
              refine ⟨506722691227559406898657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675630254970079209198209 506722691227559406898657)
              ·
                refine ⟨380042018420669555173993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506722691227559406898657 380042018420669555173993)
                ·
                  refine ⟨285031513815502166380495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380042018420669555173993 285031513815502166380495)
                  ·
                    rfl

theorem cell20_624484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_624484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624484 prefixEnd_624484 := by exact prefixLift 624484
  have htrace : WordTrace (prefixWord ++ tailWord_624484) baseStart_624484 baseEnd_624484 := by
    simpa [prefixWord, tailWord_624484, baseEnd_624484] using wordTrace_append hprefix tailTrace_624484
  have hstable : (prefixWord ++ tailWord_624484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624484).length < 2 ^ (prefixWord ++ tailWord_624484).sum := by decide
  have hdescent : baseEnd_624484 < baseStart_624484 := by decide
  rcases family_descends (prefixWord ++ tailWord_624484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624536 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 3]
def baseStart_624536 : Nat := 118140960795 + 624536 * 2 ^ 59
def prefixEnd_624536 : Nat := 4983230072969 + 3 ^ 40 * 624536 * 2
def baseEnd_624536 : Nat := 285055248032421096646949

theorem tailTrace_624536 : CollatzResearch.WordTrace tailWord_624536 prefixEnd_624536 285055248032421096646949 := by
  unfold tailWord_624536
  simp only [CollatzResearch.WordTrace]
  refine ⟨11389349632710104551046731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15185799510280139401395641 11389349632710104551046731)
  ·
    refine ⟨17084024449065156826570097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11389349632710104551046731 17084024449065156826570097)
    ·
      refine ⟨12813018336798867619927573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17084024449065156826570097 12813018336798867619927573)
      ·
        refine ⟨600610234537446919684105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12813018336798867619927573 600610234537446919684105)
        ·
          refine ⟨450457675903085189763079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600610234537446919684105 450457675903085189763079)
          ·
            refine ⟨675686513854627784644619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450457675903085189763079 675686513854627784644619)
            ·
              refine ⟨1013529770781941676966929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675686513854627784644619 1013529770781941676966929)
              ·
                refine ⟨760147328086456257725197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013529770781941676966929 760147328086456257725197)
                ·
                  refine ⟨285055248032421096646949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760147328086456257725197 285055248032421096646949)
                  ·
                    rfl

theorem cell20_624536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_624536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624536 prefixEnd_624536 := by exact prefixLift 624536
  have htrace : WordTrace (prefixWord ++ tailWord_624536) baseStart_624536 baseEnd_624536 := by
    simpa [prefixWord, tailWord_624536, baseEnd_624536] using wordTrace_append hprefix tailTrace_624536
  have hstable : (prefixWord ++ tailWord_624536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624536).length < 2 ^ (prefixWord ++ tailWord_624536).sum := by decide
  have hdescent : baseEnd_624536 < baseStart_624536 := by decide
  rcases family_descends (prefixWord ++ tailWord_624536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624540 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_624540 : Nat := 118140960795 + 624540 * 2 ^ 59
def prefixEnd_624540 : Nat := 4983230072969 + 3 ^ 40 * 624540 * 2
def baseEnd_624540 : Nat := 285057073741414860513599

theorem tailTrace_624540 : CollatzResearch.WordTrace tailWord_624540 prefixEnd_624540 285057073741414860513599 := by
  unfold tailWord_624540
  simp only [CollatzResearch.WordTrace]
  refine ⟨11389422578702858892619537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15185896771603811856826049 11389422578702858892619537)
  ·
    refine ⟨8542066934027144169464653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11389422578702858892619537 8542066934027144169464653)
    ·
      refine ⟨3203275100260179063549245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8542066934027144169464653 3203275100260179063549245)
      ·
        refine ⟨1201228162597567148830967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3203275100260179063549245 1201228162597567148830967)
        ·
          refine ⟨1801842243896350723246451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201228162597567148830967 1801842243896350723246451)
          ·
            refine ⟨2702763365844526084869677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801842243896350723246451 2702763365844526084869677)
            ·
              refine ⟨1013536262191697281826129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2702763365844526084869677 1013536262191697281826129)
              ·
                refine ⟨760152196643772961369597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013536262191697281826129 760152196643772961369597)
                ·
                  refine ⟨285057073741414860513599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760152196643772961369597 285057073741414860513599)
                  ·
                    rfl

theorem cell20_624540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_624540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624540 prefixEnd_624540 := by exact prefixLift 624540
  have htrace : WordTrace (prefixWord ++ tailWord_624540) baseStart_624540 baseEnd_624540 := by
    simpa [prefixWord, tailWord_624540, baseEnd_624540] using wordTrace_append hprefix tailTrace_624540
  have hstable : (prefixWord ++ tailWord_624540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624540).length < 2 ^ (prefixWord ++ tailWord_624540).sum := by decide
  have hdescent : baseEnd_624540 < baseStart_624540 := by decide
  rcases family_descends (prefixWord ++ tailWord_624540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624598 : List Nat := [5, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_624598 : Nat := 118140960795 + 624598 * 2 ^ 59
def prefixEnd_624598 : Nat := 4983230072969 + 3 ^ 40 * 624598 * 2
def baseEnd_624598 : Nat := 285083546521824436580029

theorem tailTrace_624598 : CollatzResearch.WordTrace tailWord_624598 prefixEnd_624598 285083546521824436580029 := by
  unfold tailWord_624598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423810036949724605678153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15187307060797062460566965 1423810036949724605678153)
  ·
    refine ⟨1067857527712293454258615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1423810036949724605678153 1067857527712293454258615)
    ·
      refine ⟨1601786291568440181387923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1067857527712293454258615 1601786291568440181387923)
      ·
        refine ⟨2402679437352660272081885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601786291568440181387923 2402679437352660272081885)
        ·
          refine ⟨901004789007247602030707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2402679437352660272081885 901004789007247602030707)
          ·
            refine ⟨1351507183510871403046061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901004789007247602030707 1351507183510871403046061)
            ·
              refine ⟨506815193816576776142273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1351507183510871403046061 506815193816576776142273)
              ·
                refine ⟨380111395362432582106705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506815193816576776142273 380111395362432582106705)
                ·
                  refine ⟨285083546521824436580029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380111395362432582106705 285083546521824436580029)
                  ·
                    rfl

theorem cell20_624598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_624598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624598 prefixEnd_624598 := by exact prefixLift 624598
  have htrace : WordTrace (prefixWord ++ tailWord_624598) baseStart_624598 baseEnd_624598 := by
    simpa [prefixWord, tailWord_624598, baseEnd_624598] using wordTrace_append hprefix tailTrace_624598
  have hstable : (prefixWord ++ tailWord_624598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624598).length < 2 ^ (prefixWord ++ tailWord_624598).sum := by decide
  have hdescent : baseEnd_624598 < baseStart_624598 := by decide
  rcases family_descends (prefixWord ++ tailWord_624598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624602 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_624602 : Nat := 118140960795 + 624602 * 2 ^ 59
def prefixEnd_624602 : Nat := 4983230072969 + 3 ^ 40 * 624602 * 2
def baseEnd_624602 : Nat := 285085372230818200446679

theorem tailTrace_624602 : CollatzResearch.WordTrace tailWord_624602 prefixEnd_624602 285085372230818200446679 := by
  unfold tailWord_624602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5695276620795275593499015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15187404322120734915997373 5695276620795275593499015)
  ·
    refine ⟨8542914931192913390248523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5695276620795275593499015 8542914931192913390248523)
    ·
      refine ⟨12814372396789370085372785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8542914931192913390248523 12814372396789370085372785)
      ·
        refine ⟨9610779297592027564029589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12814372396789370085372785 9610779297592027564029589)
        ·
          refine ⟨450505279574626292063887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9610779297592027564029589 450505279574626292063887)
          ·
            refine ⟨675757919361939438095831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450505279574626292063887 675757919361939438095831)
            ·
              refine ⟨1013636879042909157143747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675757919361939438095831 1013636879042909157143747)
              ·
                refine ⟨1520455318564363735715621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013636879042909157143747 1520455318564363735715621)
                ·
                  refine ⟨285085372230818200446679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520455318564363735715621 285085372230818200446679)
                  ·
                    rfl

theorem cell20_624602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_624602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624602 prefixEnd_624602 := by exact prefixLift 624602
  have htrace : WordTrace (prefixWord ++ tailWord_624602) baseStart_624602 baseEnd_624602 := by
    simpa [prefixWord, tailWord_624602, baseEnd_624602] using wordTrace_append hprefix tailTrace_624602
  have hstable : (prefixWord ++ tailWord_624602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624602).length < 2 ^ (prefixWord ++ tailWord_624602).sum := by decide
  have hdescent : baseEnd_624602 < baseStart_624602 := by decide
  rcases family_descends (prefixWord ++ tailWord_624602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624627 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_624627 : Nat := 118140960795 + 624627 * 2 ^ 59
def prefixEnd_624627 : Nat := 4983230072969 + 3 ^ 40 * 624627 * 2
def baseEnd_624627 : Nat := 285096782912029224613243

theorem tailTrace_624627 : CollatzResearch.WordTrace tailWord_624627 prefixEnd_624627 285096782912029224613243 := by
  unfold tailWord_624627
  simp only [CollatzResearch.WordTrace]
  refine ⟨22782018308090531643656135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15188012205393687762437423 22782018308090531643656135)
  ·
    refine ⟨34173027462135797465484203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22782018308090531643656135 34173027462135797465484203)
    ·
      refine ⟨51259541193203696198226305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34173027462135797465484203 51259541193203696198226305)
      ·
        refine ⟨38444655894902772148669729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51259541193203696198226305 38444655894902772148669729)
        ·
          refine ⟨28833491921177079111502297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38444655894902772148669729 28833491921177079111502297)
          ·
            refine ⟨21625118940882809333626723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28833491921177079111502297 21625118940882809333626723)
            ·
              refine ⟨32437678411324214000440085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21625118940882809333626723 32437678411324214000440085)
              ·
                refine ⟨1520516175530822531270629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32437678411324214000440085 1520516175530822531270629)
                ·
                  refine ⟨285096782912029224613243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520516175530822531270629 285096782912029224613243)
                  ·
                    rfl

theorem cell20_624627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_624627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624627 prefixEnd_624627 := by exact prefixLift 624627
  have htrace : WordTrace (prefixWord ++ tailWord_624627) baseStart_624627 baseEnd_624627 := by
    simpa [prefixWord, tailWord_624627, baseEnd_624627] using wordTrace_append hprefix tailTrace_624627
  have hstable : (prefixWord ++ tailWord_624627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624627).length < 2 ^ (prefixWord ++ tailWord_624627).sum := by decide
  have hdescent : baseEnd_624627 < baseStart_624627 := by decide
  rcases family_descends (prefixWord ++ tailWord_624627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624665 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_624665 : Nat := 118140960795 + 624665 * 2 ^ 59
def prefixEnd_624665 : Nat := 4983230072969 + 3 ^ 40 * 624665 * 2
def baseEnd_624665 : Nat := 285114127147469981346421

theorem tailTrace_624665 : CollatzResearch.WordTrace tailWord_624665 prefixEnd_624665 285114127147469981346421 := by
  unfold tailWord_624665
  simp only [CollatzResearch.WordTrace]
  refine ⟨22783404281952864133539449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15188936187968576089026299 22783404281952864133539449)
  ·
    refine ⟨17087553211464648100154587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22783404281952864133539449 17087553211464648100154587)
    ·
      refine ⟨25631329817196972150231881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17087553211464648100154587 25631329817196972150231881)
      ·
        refine ⟨19223497362897729112673911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25631329817196972150231881 19223497362897729112673911)
        ·
          refine ⟨28835246044346593669010867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19223497362897729112673911 28835246044346593669010867)
          ·
            refine ⟨43252869066519890503516301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28835246044346593669010867 43252869066519890503516301)
            ·
              refine ⟨16219825899944958938818613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43252869066519890503516301 16219825899944958938818613)
              ·
                refine ⟨1520608678119839900514245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16219825899944958938818613 1520608678119839900514245)
                ·
                  refine ⟨285114127147469981346421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520608678119839900514245 285114127147469981346421)
                  ·
                    rfl

theorem cell20_624665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_624665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624665 prefixEnd_624665 := by exact prefixLift 624665
  have htrace : WordTrace (prefixWord ++ tailWord_624665) baseStart_624665 baseEnd_624665 := by
    simpa [prefixWord, tailWord_624665, baseEnd_624665] using wordTrace_append hprefix tailTrace_624665
  have hstable : (prefixWord ++ tailWord_624665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624665).length < 2 ^ (prefixWord ++ tailWord_624665).sum := by decide
  have hdescent : baseEnd_624665 < baseStart_624665 := by decide
  rcases family_descends (prefixWord ++ tailWord_624665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624668 : List Nat := [2, 2, 3, 1, 3, 3, 1, 5]
def baseStart_624668 : Nat := 118140960795 + 624668 * 2 ^ 59
def prefixEnd_624668 : Nat := 4983230072969 + 3 ^ 40 * 624668 * 2
def baseEnd_624668 : Nat := 95038498809738434748803

theorem tailTrace_624668 : CollatzResearch.WordTrace tailWord_624668 prefixEnd_624668 95038498809738434748803 := by
  unfold tailWord_624668
  simp only [CollatzResearch.WordTrace]
  refine ⟨11391756850470997822949329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15189009133961330430599105 11391756850470997822949329)
  ·
    refine ⟨8543817637853248367211997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11391756850470997822949329 8543817637853248367211997)
    ·
      refine ⟨3203931614194968137704499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8543817637853248367211997 3203931614194968137704499)
      ·
        refine ⟨4805897421292452206556749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3203931614194968137704499 4805897421292452206556749)
        ·
          refine ⟨1802211532984669577458781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4805897421292452206556749 1802211532984669577458781)
          ·
            refine ⟨675829324869251091547043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1802211532984669577458781 675829324869251091547043)
            ·
              refine ⟨1013743987303876637320565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675829324869251091547043 1013743987303876637320565)
              ·
                refine ⟨95038498809738434748803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1013743987303876637320565 95038498809738434748803)
                ·
                  rfl

theorem cell20_624668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_624668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624668 prefixEnd_624668 := by exact prefixLift 624668
  have htrace : WordTrace (prefixWord ++ tailWord_624668) baseStart_624668 baseEnd_624668 := by
    simpa [prefixWord, tailWord_624668, baseEnd_624668] using wordTrace_append hprefix tailTrace_624668
  have hstable : (prefixWord ++ tailWord_624668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624668).length < 2 ^ (prefixWord ++ tailWord_624668).sum := by decide
  have hdescent : baseEnd_624668 < baseStart_624668 := by decide
  rcases family_descends (prefixWord ++ tailWord_624668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624682 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_624682 : Nat := 118140960795 + 624682 * 2 ^ 59
def prefixEnd_624682 : Nat := 4983230072969 + 3 ^ 40 * 624682 * 2
def baseEnd_624682 : Nat := 285121886410693477779685

theorem tailTrace_624682 : CollatzResearch.WordTrace tailWord_624682 prefixEnd_624682 285121886410693477779685 := by
  unfold tailWord_624682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5696006080722819009227075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15189349548594184024605533 5696006080722819009227075)
  ·
    refine ⟨8544009121084228513840613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5696006080722819009227075 8544009121084228513840613)
    ·
      refine ⟨1602001710203292846345115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8544009121084228513840613 1602001710203292846345115)
      ·
        refine ⟨2403002565304939269517673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602001710203292846345115 2403002565304939269517673)
        ·
          refine ⟨1802251923978704452138255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2403002565304939269517673 1802251923978704452138255)
          ·
            refine ⟨2703377885968056678207383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802251923978704452138255 2703377885968056678207383)
            ·
              refine ⟨4055066828952085017311075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703377885968056678207383 4055066828952085017311075)
              ·
                refine ⟨6082600243428127525966613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4055066828952085017311075 6082600243428127525966613)
                ·
                  refine ⟨285121886410693477779685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6082600243428127525966613 285121886410693477779685)
                  ·
                    rfl

theorem cell20_624682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_624682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624682 prefixEnd_624682 := by exact prefixLift 624682
  have htrace : WordTrace (prefixWord ++ tailWord_624682) baseStart_624682 baseEnd_624682 := by
    simpa [prefixWord, tailWord_624682, baseEnd_624682] using wordTrace_append hprefix tailTrace_624682
  have hstable : (prefixWord ++ tailWord_624682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624682).length < 2 ^ (prefixWord ++ tailWord_624682).sum := by decide
  have hdescent : baseEnd_624682 < baseStart_624682 := by decide
  rcases family_descends (prefixWord ++ tailWord_624682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624726 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_624726 : Nat := 118140960795 + 624726 * 2 ^ 59
def prefixEnd_624726 : Nat := 4983230072969 + 3 ^ 40 * 624726 * 2
def baseEnd_624726 : Nat := 285141969209624880312839

theorem tailTrace_624726 : CollatzResearch.WordTrace tailWord_624726 prefixEnd_624726 285141969209624880312839 := by
  unfold tailWord_624726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424101820920741971969377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15190419423154581034340021 1424101820920741971969377)
  ·
    refine ⟨1068076365690556478977033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1424101820920741971969377 1068076365690556478977033)
    ·
      refine ⟨801057274267917359232775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1068076365690556478977033 801057274267917359232775)
      ·
        refine ⟨1201585911401876038849163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801057274267917359232775 1201585911401876038849163)
        ·
          refine ⟨1802378867102814058273745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201585911401876038849163 1802378867102814058273745)
          ·
            refine ⟨1351784150327110543705309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1802378867102814058273745 1351784150327110543705309)
            ·
              refine ⟨506919056372666453889491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1351784150327110543705309 506919056372666453889491)
              ·
                refine ⟨760378584558999680834237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506919056372666453889491 760378584558999680834237)
                ·
                  refine ⟨285141969209624880312839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760378584558999680834237 285141969209624880312839)
                  ·
                    rfl

theorem cell20_624726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_624726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624726 prefixEnd_624726 := by exact prefixLift 624726
  have htrace : WordTrace (prefixWord ++ tailWord_624726) baseStart_624726 baseEnd_624726 := by
    simpa [prefixWord, tailWord_624726, baseEnd_624726] using wordTrace_append hprefix tailTrace_624726
  have hstable : (prefixWord ++ tailWord_624726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624726).length < 2 ^ (prefixWord ++ tailWord_624726).sum := by decide
  have hdescent : baseEnd_624726 < baseStart_624726 := by decide
  rcases family_descends (prefixWord ++ tailWord_624726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624754 : List Nat := [3, 2, 1, 2, 2, 4, 1, 3, 2]
def baseStart_624754 : Nat := 118140960795 + 624754 * 2 ^ 59
def prefixEnd_624754 : Nat := 4983230072969 + 3 ^ 40 * 624754 * 2
def baseEnd_624754 : Nat := 285154749172581227379391

theorem tailTrace_624754 : CollatzResearch.WordTrace tailWord_624754 prefixEnd_624754 285154749172581227379391 := by
  unfold tailWord_624754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5696662594657608083382329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15191100252420288222352877 5696662594657608083382329)
  ·
    refine ⟨4272496945993206062536747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5696662594657608083382329 4272496945993206062536747)
    ·
      refine ⟨6408745418989809093805121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272496945993206062536747 6408745418989809093805121)
      ·
        refine ⟨4806559064242356820353841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6408745418989809093805121 4806559064242356820353841)
        ·
          refine ⟨3604919298181767615265381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4806559064242356820353841 3604919298181767615265381)
          ·
            refine ⟨675922368409081427862259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3604919298181767615265381 675922368409081427862259)
            ·
              refine ⟨1013883552613622141793389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675922368409081427862259 1013883552613622141793389)
              ·
                refine ⟨380206332230108303172521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1013883552613622141793389 380206332230108303172521)
                ·
                  refine ⟨285154749172581227379391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380206332230108303172521 285154749172581227379391)
                  ·
                    rfl

theorem cell20_624754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_624754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624754 prefixEnd_624754 := by exact prefixLift 624754
  have htrace : WordTrace (prefixWord ++ tailWord_624754) baseStart_624754 baseEnd_624754 := by
    simpa [prefixWord, tailWord_624754, baseEnd_624754] using wordTrace_append hprefix tailTrace_624754
  have hstable : (prefixWord ++ tailWord_624754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624754).length < 2 ^ (prefixWord ++ tailWord_624754).sum := by decide
  have hdescent : baseEnd_624754 < baseStart_624754 := by decide
  rcases family_descends (prefixWord ++ tailWord_624754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624765 : List Nat := [1, 4, 1, 1, 3, 4, 6]
def baseStart_624765 : Nat := 118140960795 + 624765 * 2 ^ 59
def prefixEnd_624765 : Nat := 4983230072969 + 3 ^ 40 * 624765 * 2
def baseEnd_624765 : Nat := 31684418874701564223631

theorem tailTrace_624765 : CollatzResearch.WordTrace tailWord_624765 prefixEnd_624765 31684418874701564223631 := by
  unfold tailWord_624765
  simp only [CollatzResearch.WordTrace]
  refine ⟨22787051581590581212179749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15191367721060387474786499 22787051581590581212179749)
  ·
    refine ⟨4272572171548233977283703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22787051581590581212179749 4272572171548233977283703)
    ·
      refine ⟨6408858257322350965925555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272572171548233977283703 6408858257322350965925555)
      ·
        refine ⟨9613287385983526448888333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408858257322350965925555 9613287385983526448888333)
        ·
          refine ⟨3604982769743822418333125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9613287385983526448888333 3604982769743822418333125)
          ·
            refine ⟨675934269326966703437461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3604982769743822418333125 675934269326966703437461)
            ·
              refine ⟨31684418874701564223631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 675934269326966703437461 31684418874701564223631)
              ·
                rfl

theorem cell20_624765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 6].length) (baseStart_624765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624765 prefixEnd_624765 := by exact prefixLift 624765
  have htrace : WordTrace (prefixWord ++ tailWord_624765) baseStart_624765 baseEnd_624765 := by
    simpa [prefixWord, tailWord_624765, baseEnd_624765] using wordTrace_append hprefix tailTrace_624765
  have hstable : (prefixWord ++ tailWord_624765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624765).length < 2 ^ (prefixWord ++ tailWord_624765).sum := by decide
  have hdescent : baseEnd_624765 < baseStart_624765 := by decide
  rcases family_descends (prefixWord ++ tailWord_624765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624772 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_624772 : Nat := 118140960795 + 624772 * 2 ^ 59
def prefixEnd_624772 : Nat := 4983230072969 + 3 ^ 40 * 624772 * 2
def baseEnd_624772 : Nat := 285162964863053164779317

theorem tailTrace_624772 : CollatzResearch.WordTrace tailWord_624772 prefixEnd_624772 285162964863053164779317 := by
  unfold tailWord_624772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11393653446282610703842285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15191537928376814271789713 11393653446282610703842285)
  ·
    refine ⟨4272620042355979013940857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11393653446282610703842285 4272620042355979013940857)
    ·
      refine ⟨3204465031766984260455643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4272620042355979013940857 3204465031766984260455643)
      ·
        refine ⟨4806697547650476390683465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204465031766984260455643 4806697547650476390683465)
        ·
          refine ⟨3605023160737857293012599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4806697547650476390683465 3605023160737857293012599)
          ·
            refine ⟨5407534741106785939518899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3605023160737857293012599 5407534741106785939518899)
            ·
              refine ⟨8111302111660178909278349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407534741106785939518899 8111302111660178909278349)
              ·
                refine ⟨3041738291872567090979381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8111302111660178909278349 3041738291872567090979381)
                ·
                  refine ⟨285162964863053164779317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3041738291872567090979381 285162964863053164779317)
                  ·
                    rfl

theorem cell20_624772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_624772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624772 prefixEnd_624772 := by exact prefixLift 624772
  have htrace : WordTrace (prefixWord ++ tailWord_624772) baseStart_624772 baseEnd_624772 := by
    simpa [prefixWord, tailWord_624772, baseEnd_624772] using wordTrace_append hprefix tailTrace_624772
  have hstable : (prefixWord ++ tailWord_624772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624772).length < 2 ^ (prefixWord ++ tailWord_624772).sum := by decide
  have hdescent : baseEnd_624772 < baseStart_624772 := by decide
  rcases family_descends (prefixWord ++ tailWord_624772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624782 : List Nat := [4, 1, 1, 3, 3, 1, 2, 5]
def baseStart_624782 : Nat := 118140960795 + 624782 * 2 ^ 59
def prefixEnd_624782 : Nat := 4983230072969 + 3 ^ 40 * 624782 * 2
def baseEnd_624782 : Nat := 95055843045179191481981

theorem tailTrace_624782 : CollatzResearch.WordTrace tailWord_624782 prefixEnd_624782 95055843045179191481981 := by
  unfold tailWord_624782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848458952816124139443575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15191781081685995410365733 2848458952816124139443575)
  ·
    refine ⟨4272688429224186209165363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2848458952816124139443575 4272688429224186209165363)
    ·
      refine ⟨6409032643836279313748045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272688429224186209165363 6409032643836279313748045)
      ·
        refine ⟨2403387241438604742655517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6409032643836279313748045 2403387241438604742655517)
        ·
          refine ⟨901270215539476778495819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2403387241438604742655517 901270215539476778495819)
          ·
            refine ⟨1351905323309215167743729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901270215539476778495819 1351905323309215167743729)
            ·
              refine ⟨1013928992481911375807797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351905323309215167743729 1013928992481911375807797)
              ·
                refine ⟨95055843045179191481981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1013928992481911375807797 95055843045179191481981)
                ·
                  rfl

theorem cell20_624782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_624782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624782 prefixEnd_624782 := by exact prefixLift 624782
  have htrace : WordTrace (prefixWord ++ tailWord_624782) baseStart_624782 baseEnd_624782 := by
    simpa [prefixWord, tailWord_624782, baseEnd_624782] using wordTrace_append hprefix tailTrace_624782
  have hstable : (prefixWord ++ tailWord_624782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624782).length < 2 ^ (prefixWord ++ tailWord_624782).sum := by decide
  have hdescent : baseEnd_624782 < baseStart_624782 := by decide
  rcases family_descends (prefixWord ++ tailWord_624782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624830 : List Nat := [4, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_624830 : Nat := 118140960795 + 624830 * 2 ^ 59
def prefixEnd_624830 : Nat := 4983230072969 + 3 ^ 40 * 624830 * 2
def baseEnd_624830 : Nat := 285189437643462740845747

theorem tailTrace_624830 : CollatzResearch.WordTrace tailWord_624830 prefixEnd_624830 285189437643462740845747 := by
  unfold tailWord_624830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848677790794387164161993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15192948217570064875530629 2848677790794387164161993)
  ·
    refine ⟨2136508343095790373121495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2848677790794387164161993 2136508343095790373121495)
    ·
      refine ⟨3204762514643685559682243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136508343095790373121495 3204762514643685559682243)
      ·
        refine ⟨4807143771965528339523365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204762514643685559682243 4807143771965528339523365)
        ·
          refine ⟨901339457243536563660631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4807143771965528339523365 901339457243536563660631)
          ·
            refine ⟨1352009185865304845490947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901339457243536563660631 1352009185865304845490947)
            ·
              refine ⟨2028013778797957268236421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352009185865304845490947 2028013778797957268236421)
              ·
                refine ⟨380252583524616987794329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2028013778797957268236421 380252583524616987794329)
                ·
                  refine ⟨285189437643462740845747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380252583524616987794329 285189437643462740845747)
                  ·
                    rfl

theorem cell20_624830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_624830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624830 prefixEnd_624830 := by exact prefixLift 624830
  have htrace : WordTrace (prefixWord ++ tailWord_624830) baseStart_624830 baseEnd_624830 := by
    simpa [prefixWord, tailWord_624830, baseEnd_624830] using wordTrace_append hprefix tailTrace_624830
  have hstable : (prefixWord ++ tailWord_624830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624830).length < 2 ^ (prefixWord ++ tailWord_624830).sum := by decide
  have hdescent : baseEnd_624830 < baseStart_624830 := by decide
  rcases family_descends (prefixWord ++ tailWord_624830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624882 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_624882 : Nat := 118140960795 + 624882 * 2 ^ 59
def prefixEnd_624882 : Nat := 4983230072969 + 3 ^ 40 * 624882 * 2
def baseEnd_624882 : Nat := 285213171860381671112201

theorem tailTrace_624882 : CollatzResearch.WordTrace tailWord_624882 prefixEnd_624882 285213171860381671112201 := by
  unfold tailWord_624882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5697829730541677548547225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15194212614777806796125933 5697829730541677548547225)
  ·
    refine ⟨4273372297906258161410419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5697829730541677548547225 4273372297906258161410419)
    ·
      refine ⟨6410058446859387242115629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4273372297906258161410419 6410058446859387242115629)
      ·
        refine ⟨2403771917572270215793361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6410058446859387242115629 2403771917572270215793361)
        ·
          refine ⟨1802828938179202661845021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2403771917572270215793361 1802828938179202661845021)
          ·
            refine ⟨676060851817200998191883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1802828938179202661845021 676060851817200998191883)
            ·
              refine ⟨1014091277725801497287825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676060851817200998191883 1014091277725801497287825)
              ·
                refine ⟨760568458294351122965869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014091277725801497287825 760568458294351122965869)
                ·
                  refine ⟨285213171860381671112201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760568458294351122965869 285213171860381671112201)
                  ·
                    rfl

theorem cell20_624882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_624882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624882 prefixEnd_624882 := by exact prefixLift 624882
  have htrace : WordTrace (prefixWord ++ tailWord_624882) baseStart_624882 baseEnd_624882 := by
    simpa [prefixWord, tailWord_624882, baseEnd_624882] using wordTrace_append hprefix tailTrace_624882
  have hstable : (prefixWord ++ tailWord_624882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624882).length < 2 ^ (prefixWord ++ tailWord_624882).sum := by decide
  have hdescent : baseEnd_624882 < baseStart_624882 := by decide
  rcases family_descends (prefixWord ++ tailWord_624882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624917 : List Nat := [1, 3, 2, 1, 2, 1, 6, 4]
def baseStart_624917 : Nat := 118140960795 + 624917 * 2 ^ 59
def prefixEnd_624917 : Nat := 4983230072969 + 3 ^ 40 * 624917 * 2
def baseEnd_624917 : Nat := 95076382271359034981797

theorem tailTrace_624917 : CollatzResearch.WordTrace tailWord_624917 prefixEnd_624917 95076382271359034981797 := by
  unfold tailWord_624917
  simp only [CollatzResearch.WordTrace]
  refine ⟨22792595477039911171713005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15195063651359940781142003 22792595477039911171713005)
  ·
    refine ⟨8547223303889966689392377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22792595477039911171713005 8547223303889966689392377)
    ·
      refine ⟨6410417477917475017044283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8547223303889966689392377 6410417477917475017044283)
      ·
        refine ⟨9615626216876212525566425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6410417477917475017044283 9615626216876212525566425)
        ·
          refine ⟨7211719662657159394174819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9615626216876212525566425 7211719662657159394174819)
          ·
            refine ⟨10817579493985739091262229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7211719662657159394174819 10817579493985739091262229)
            ·
              refine ⟨507074038780581519902917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10817579493985739091262229 507074038780581519902917)
              ·
                refine ⟨95076382271359034981797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 507074038780581519902917 95076382271359034981797)
                ·
                  rfl

theorem cell20_624917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 4].length) (baseStart_624917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624917 prefixEnd_624917 := by exact prefixLift 624917
  have htrace : WordTrace (prefixWord ++ tailWord_624917) baseStart_624917 baseEnd_624917 := by
    simpa [prefixWord, tailWord_624917, baseEnd_624917] using wordTrace_append hprefix tailTrace_624917
  have hstable : (prefixWord ++ tailWord_624917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624917).length < 2 ^ (prefixWord ++ tailWord_624917).sum := by decide
  have hdescent : baseEnd_624917 < baseStart_624917 := by decide
  rcases family_descends (prefixWord ++ tailWord_624917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624927 : List Nat := [1, 1, 2, 4, 3, 1, 3, 3, 2]
def baseStart_624927 : Nat := 118140960795 + 624927 * 2 ^ 59
def prefixEnd_624927 : Nat := 4983230072969 + 3 ^ 40 * 624927 * 2
def baseEnd_624927 : Nat := 285233711086561514612017

theorem tailTrace_624927 : CollatzResearch.WordTrace tailWord_624927 prefixEnd_624927 285233711086561514612017 := by
  unfold tailWord_624927
  simp only [CollatzResearch.WordTrace]
  refine ⟨22792960207003682879577035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15195306804669121919718023 22792960207003682879577035)
  ·
    refine ⟨34189440310505524319365553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22792960207003682879577035 34189440310505524319365553)
    ·
      refine ⟨25642080232879143239524165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34189440310505524319365553 25642080232879143239524165)
      ·
        refine ⟨4807890043664839357410781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25642080232879143239524165 4807890043664839357410781)
        ·
          refine ⟨1802958766374314759029043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4807890043664839357410781 1802958766374314759029043)
          ·
            refine ⟨2704438149561472138543565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802958766374314759029043 2704438149561472138543565)
            ·
              refine ⟨1014164306085552051953837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2704438149561472138543565 1014164306085552051953837)
              ·
                refine ⟨380311614782082019482689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1014164306085552051953837 380311614782082019482689)
                ·
                  refine ⟨285233711086561514612017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380311614782082019482689 285233711086561514612017)
                  ·
                    rfl

theorem cell20_624927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 3, 2].length) (baseStart_624927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624927 prefixEnd_624927 := by exact prefixLift 624927
  have htrace : WordTrace (prefixWord ++ tailWord_624927) baseStart_624927 baseEnd_624927 := by
    simpa [prefixWord, tailWord_624927, baseEnd_624927] using wordTrace_append hprefix tailTrace_624927
  have hstable : (prefixWord ++ tailWord_624927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624927).length < 2 ^ (prefixWord ++ tailWord_624927).sum := by decide
  have hdescent : baseEnd_624927 < baseStart_624927 := by decide
  rcases family_descends (prefixWord ++ tailWord_624927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624958 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_624958 : Nat := 118140960795 + 624958 * 2 ^ 59
def prefixEnd_624958 : Nat := 4983230072969 + 3 ^ 40 * 624958 * 2
def baseEnd_624958 : Nat := 285247860331263184578557

theorem tailTrace_624958 : CollatzResearch.WordTrace tailWord_624958 prefixEnd_624958 285247860331263184578557 := by
  unfold tailWord_624958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849261358736421896744441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15196060579927583449303685 2849261358736421896744441)
  ·
    refine ⟨2136946019052316422558331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2849261358736421896744441 2136946019052316422558331)
    ·
      refine ⟨3205419028578474633837497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136946019052316422558331 3205419028578474633837497)
      ·
        refine ⟨2404064271433855975378123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3205419028578474633837497 2404064271433855975378123)
        ·
          refine ⟨3606096407150783963067185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404064271433855975378123 3606096407150783963067185)
          ·
            refine ⟨2704572305363087972300389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3606096407150783963067185 2704572305363087972300389)
            ·
              refine ⟨507107307255578994806323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2704572305363087972300389 507107307255578994806323)
              ·
                refine ⟨760660960883368492209485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507107307255578994806323 760660960883368492209485)
                ·
                  refine ⟨285247860331263184578557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760660960883368492209485 285247860331263184578557)
                  ·
                    rfl

theorem cell20_624958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_624958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624958 prefixEnd_624958 := by exact prefixLift 624958
  have htrace : WordTrace (prefixWord ++ tailWord_624958) baseStart_624958 baseEnd_624958 := by
    simpa [prefixWord, tailWord_624958, baseEnd_624958] using wordTrace_append hprefix tailTrace_624958
  have hstable : (prefixWord ++ tailWord_624958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624958).length < 2 ^ (prefixWord ++ tailWord_624958).sum := by decide
  have hdescent : baseEnd_624958 < baseStart_624958 := by decide
  rcases family_descends (prefixWord ++ tailWord_624958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624976 : List Nat := [2, 1, 1, 1, 1, 6, 2, 6]
def baseStart_624976 : Nat := 118140960795 + 624976 * 2 ^ 59
def prefixEnd_624976 : Nat := 4983230072969 + 3 ^ 40 * 624976 * 2
def baseEnd_624976 : Nat := 95085358673911707326161

theorem tailTrace_624976 : CollatzResearch.WordTrace tailWord_624976 prefixEnd_624976 95085358673911707326161 := by
  unfold tailWord_624976
  simp only [CollatzResearch.WordTrace]
  refine ⟨11397373691913082124055391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15196498255884109498740521 11397373691913082124055391)
  ·
    refine ⟨17096060537869623186083087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11397373691913082124055391 17096060537869623186083087)
    ·
      refine ⟨25644090806804434779124631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17096060537869623186083087 25644090806804434779124631)
      ·
        refine ⟨38466136210206652168686947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25644090806804434779124631 38466136210206652168686947)
        ·
          refine ⟨57699204315309978253030421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38466136210206652168686947 57699204315309978253030421)
          ·
            refine ⟨2704650202280155230610801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57699204315309978253030421 2704650202280155230610801)
            ·
              refine ⟨2028487651710116422958101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2704650202280155230610801 2028487651710116422958101)
              ·
                refine ⟨95085358673911707326161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2028487651710116422958101 95085358673911707326161)
                ·
                  rfl

theorem cell20_624976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_624976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624976 prefixEnd_624976 := by exact prefixLift 624976
  have htrace : WordTrace (prefixWord ++ tailWord_624976) baseStart_624976 baseEnd_624976 := by
    simpa [prefixWord, tailWord_624976, baseEnd_624976] using wordTrace_append hprefix tailTrace_624976
  have hstable : (prefixWord ++ tailWord_624976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624976).length < 2 ^ (prefixWord ++ tailWord_624976).sum := by decide
  have hdescent : baseEnd_624976 < baseStart_624976 := by decide
  rcases family_descends (prefixWord ++ tailWord_624976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624986 : List Nat := [3, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_624986 : Nat := 118140960795 + 624986 * 2 ^ 59
def prefixEnd_624986 : Nat := 4983230072969 + 3 ^ 40 * 624986 * 2
def baseEnd_624986 : Nat := 285260640294219531645109

theorem tailTrace_624986 : CollatzResearch.WordTrace tailWord_624986 prefixEnd_624986 285260640294219531645109 := by
  unfold tailWord_624986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698778028447483988993703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15196741409193290637316541 5698778028447483988993703)
  ·
    refine ⟨8548167042671225983490555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5698778028447483988993703 8548167042671225983490555)
    ·
      refine ⟨12822250564006838975235833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8548167042671225983490555 12822250564006838975235833)
      ·
        refine ⟨9616687923005129231426875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12822250564006838975235833 9616687923005129231426875)
        ·
          refine ⟨14425031884507693847140313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9616687923005129231426875 14425031884507693847140313)
          ·
            refine ⟨10818773913380770385355235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14425031884507693847140313 10818773913380770385355235)
            ·
              refine ⟨16228160870071155578032853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10818773913380770385355235 16228160870071155578032853)
              ·
                refine ⟨380347520392292708860145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16228160870071155578032853 380347520392292708860145)
                ·
                  refine ⟨285260640294219531645109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380347520392292708860145 285260640294219531645109)
                  ·
                    rfl

theorem cell20_624986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_624986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_624986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_624986 prefixEnd_624986 := by exact prefixLift 624986
  have htrace : WordTrace (prefixWord ++ tailWord_624986) baseStart_624986 baseEnd_624986 := by
    simpa [prefixWord, tailWord_624986, baseEnd_624986] using wordTrace_append hprefix tailTrace_624986
  have hstable : (prefixWord ++ tailWord_624986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624986).length < 2 ^ (prefixWord ++ tailWord_624986).sum := by decide
  have hdescent : baseEnd_624986 < baseStart_624986 := by decide
  rcases family_descends (prefixWord ++ tailWord_624986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625031 : List Nat := [1, 1, 4, 2, 2, 1, 5, 4]
def baseStart_625031 : Nat := 118140960795 + 625031 * 2 ^ 59
def prefixEnd_625031 : Nat := 4983230072969 + 3 ^ 40 * 625031 * 2
def baseEnd_625031 : Nat := 95093726506799791714975

theorem tailTrace_625031 : CollatzResearch.WordTrace tailWord_625031 prefixEnd_625031 95093726506799791714975 := by
  unfold tailWord_625031
  simp only [CollatzResearch.WordTrace]
  refine ⟨22796753398626908641362947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15197835599084605760908631 22796753398626908641362947)
  ·
    refine ⟨34195130097940362962044421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22796753398626908641362947 34195130097940362962044421)
    ·
      refine ⟨6411586893363818055383329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34195130097940362962044421 6411586893363818055383329)
      ·
        refine ⟨4808690170022863541537497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6411586893363818055383329 4808690170022863541537497)
        ·
          refine ⟨3606517627517147656153123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4808690170022863541537497 3606517627517147656153123)
          ·
            refine ⟨5409776441275721484229685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606517627517147656153123 5409776441275721484229685)
            ·
              refine ⟨507166541369598889146533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5409776441275721484229685 507166541369598889146533)
              ·
                refine ⟨95093726506799791714975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 507166541369598889146533 95093726506799791714975)
                ·
                  rfl

theorem cell20_625031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 4].length) (baseStart_625031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625031 prefixEnd_625031 := by exact prefixLift 625031
  have htrace : WordTrace (prefixWord ++ tailWord_625031) baseStart_625031 baseEnd_625031 := by
    simpa [prefixWord, tailWord_625031, baseEnd_625031] using wordTrace_append hprefix tailTrace_625031
  have hstable : (prefixWord ++ tailWord_625031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625031).length < 2 ^ (prefixWord ++ tailWord_625031).sum := by decide
  have hdescent : baseEnd_625031 < baseStart_625031 := by decide
  rcases family_descends (prefixWord ++ tailWord_625031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625097 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_625097 : Nat := 118140960795 + 625097 * 2 ^ 59
def prefixEnd_625097 : Nat := 4983230072969 + 3 ^ 40 * 625097 * 2
def baseEnd_625097 : Nat := 285311303718796478944655

theorem tailTrace_625097 : CollatzResearch.WordTrace tailWord_625097 prefixEnd_625097 285311303718796478944655 := by
  unfold tailWord_625097
  simp only [CollatzResearch.WordTrace]
  refine ⟨22799160616387801913265545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15199440410925201275510363 22799160616387801913265545)
  ·
    refine ⟨17099370462290851434949159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22799160616387801913265545 17099370462290851434949159)
    ·
      refine ⟨25649055693436277152423739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17099370462290851434949159 25649055693436277152423739)
      ·
        refine ⟨38473583540154415728635609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25649055693436277152423739 38473583540154415728635609)
        ·
          refine ⟨28855187655115811796476707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38473583540154415728635609 28855187655115811796476707)
          ·
            refine ⟨43282781482673717694715061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28855187655115811796476707 43282781482673717694715061)
            ·
              refine ⟨4057760764000661033879537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43282781482673717694715061 4057760764000661033879537)
              ·
                refine ⟨3043320573000495775409653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4057760764000661033879537 3043320573000495775409653)
                ·
                  refine ⟨285311303718796478944655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3043320573000495775409653 285311303718796478944655)
                  ·
                    rfl

theorem cell20_625097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_625097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625097 prefixEnd_625097 := by exact prefixLift 625097
  have htrace : WordTrace (prefixWord ++ tailWord_625097) baseStart_625097 baseEnd_625097 := by
    simpa [prefixWord, tailWord_625097, baseEnd_625097] using wordTrace_append hprefix tailTrace_625097
  have hstable : (prefixWord ++ tailWord_625097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625097).length < 2 ^ (prefixWord ++ tailWord_625097).sum := by decide
  have hdescent : baseEnd_625097 < baseStart_625097 := by decide
  rcases family_descends (prefixWord ++ tailWord_625097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625114 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 3]
def baseStart_625114 : Nat := 118140960795 + 625114 * 2 ^ 59
def prefixEnd_625114 : Nat := 4983230072969 + 3 ^ 40 * 625114 * 2
def baseEnd_625114 : Nat := 285319062982019975377919

theorem tailTrace_625114 : CollatzResearch.WordTrace tailWord_625114 prefixEnd_625114 285319062982019975377919 := by
  unfold tailWord_625114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5699945164331553454158599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15199853771550809211089597 5699945164331553454158599)
  ·
    refine ⟨8549917746497330181237899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5699945164331553454158599 8549917746497330181237899)
    ·
      refine ⟨12824876619745995271856849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8549917746497330181237899 12824876619745995271856849)
      ·
        refine ⟨9618657464809496453892637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12824876619745995271856849 9618657464809496453892637)
        ·
          refine ⟨3606996549303561170209739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9618657464809496453892637 3606996549303561170209739)
          ·
            refine ⟨5410494823955341755314609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606996549303561170209739 5410494823955341755314609)
            ·
              refine ⟨4057871117966506316485957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5410494823955341755314609 4057871117966506316485957)
              ·
                refine ⟨760850834618719934341117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4057871117966506316485957 760850834618719934341117)
                ·
                  refine ⟨285319062982019975377919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760850834618719934341117 285319062982019975377919)
                  ·
                    rfl

theorem cell20_625114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_625114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625114 prefixEnd_625114 := by exact prefixLift 625114
  have htrace : WordTrace (prefixWord ++ tailWord_625114) baseStart_625114 baseEnd_625114 := by
    simpa [prefixWord, tailWord_625114, baseEnd_625114] using wordTrace_append hprefix tailTrace_625114
  have hstable : (prefixWord ++ tailWord_625114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625114).length < 2 ^ (prefixWord ++ tailWord_625114).sum := by decide
  have hdescent : baseEnd_625114 < baseStart_625114 := by decide
  rcases family_descends (prefixWord ++ tailWord_625114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625128 : List Nat := [2, 1, 4, 1, 1, 3, 1, 7]
def baseStart_625128 : Nat := 118140960795 + 625128 * 2 ^ 59
def prefixEnd_625128 : Nat := 4983230072969 + 3 ^ 40 * 625128 * 2
def baseEnd_625128 : Nat := 95108484321166049637065

theorem tailTrace_625128 : CollatzResearch.WordTrace tailWord_625128 prefixEnd_625128 95108484321166049637065 := by
  unfold tailWord_625128
  simp only [CollatzResearch.WordTrace]
  refine ⟨11400145639637747103822019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15200194186183662805096025 11400145639637747103822019)
  ·
    refine ⟨17100218459456620655733029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11400145639637747103822019 17100218459456620655733029)
    ·
      refine ⟨3206290961148116372949943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17100218459456620655733029 3206290961148116372949943)
      ·
        refine ⟨4809436441722174559424915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3206290961148116372949943 4809436441722174559424915)
        ·
          refine ⟨7214154662583261839137373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4809436441722174559424915 7214154662583261839137373)
          ·
            refine ⟨2705307998468723189676515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7214154662583261839137373 2705307998468723189676515)
            ·
              refine ⟨4057961997703084784514773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705307998468723189676515 4057961997703084784514773)
              ·
                refine ⟨95108484321166049637065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4057961997703084784514773 95108484321166049637065)
                ·
                  rfl

theorem cell20_625128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_625128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625128 prefixEnd_625128 := by exact prefixLift 625128
  have htrace : WordTrace (prefixWord ++ tailWord_625128) baseStart_625128 baseEnd_625128 := by
    simpa [prefixWord, tailWord_625128, baseEnd_625128] using wordTrace_append hprefix tailTrace_625128
  have hstable : (prefixWord ++ tailWord_625128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625128).length < 2 ^ (prefixWord ++ tailWord_625128).sum := by decide
  have hdescent : baseEnd_625128 < baseStart_625128 := by decide
  rcases family_descends (prefixWord ++ tailWord_625128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625165 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 3]
def baseStart_625165 : Nat := 118140960795 + 625165 * 2 ^ 59
def prefixEnd_625165 : Nat := 4983230072969 + 3 ^ 40 * 625165 * 2
def baseEnd_625165 : Nat := 285342340771690464677711

theorem tailTrace_625165 : CollatzResearch.WordTrace tailWord_625165 prefixEnd_625165 285342340771690464677711 := by
  unfold tailWord_625165
  simp only [CollatzResearch.WordTrace]
  refine ⟨22801640780141449526740949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15201093853427633017827299 22801640780141449526740949)
  ·
    refine ⟨534413455784565223282991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 22801640780141449526740949 534413455784565223282991)
    ·
      refine ⟨801620183676847834924487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534413455784565223282991 801620183676847834924487)
      ·
        refine ⟨1202430275515271752386731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801620183676847834924487 1202430275515271752386731)
        ·
          refine ⟨1803645413272907628580097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202430275515271752386731 1803645413272907628580097)
          ·
            refine ⟨1352734059954680721435073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803645413272907628580097 1352734059954680721435073)
            ·
              refine ⟨1014550544966010541076305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352734059954680721435073 1014550544966010541076305)
              ·
                refine ⟨760912908724507905807229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014550544966010541076305 760912908724507905807229)
                ·
                  refine ⟨285342340771690464677711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760912908724507905807229 285342340771690464677711)
                  ·
                    rfl

theorem cell20_625165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_625165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625165 prefixEnd_625165 := by exact prefixLift 625165
  have htrace : WordTrace (prefixWord ++ tailWord_625165) baseStart_625165 baseEnd_625165 := by
    simpa [prefixWord, tailWord_625165, baseEnd_625165] using wordTrace_append hprefix tailTrace_625165
  have hstable : (prefixWord ++ tailWord_625165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625165).length < 2 ^ (prefixWord ++ tailWord_625165).sum := by decide
  have hdescent : baseEnd_625165 < baseStart_625165 := by decide
  rcases family_descends (prefixWord ++ tailWord_625165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625166 : List Nat := [4, 1, 1, 2, 3, 9]
def baseStart_625166 : Nat := 118140960795 + 625166 * 2 ^ 59
def prefixEnd_625166 : Nat := 4983230072969 + 3 ^ 40 * 625166 * 2
def baseEnd_625166 : Nat := 10568251748108848357199

theorem tailTrace_625166 : CollatzResearch.WordTrace tailWord_625166 prefixEnd_625166 10568251748108848357199 := by
  unfold tailWord_625166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850209656642228337190919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15201118168758551131684901 2850209656642228337190919)
  ·
    refine ⟨4275314484963342505786379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2850209656642228337190919 4275314484963342505786379)
    ·
      refine ⟨6412971727445013758679569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4275314484963342505786379 6412971727445013758679569)
      ·
        refine ⟨4809728795583760319009677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6412971727445013758679569 4809728795583760319009677)
        ·
          refine ⟨1803648298343910119628629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4809728795583760319009677 1803648298343910119628629)
          ·
            refine ⟨10568251748108848357199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1803648298343910119628629 10568251748108848357199)
            ·
              rfl

theorem cell20_625166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 9].length) (baseStart_625166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625166 prefixEnd_625166 := by exact prefixLift 625166
  have htrace : WordTrace (prefixWord ++ tailWord_625166) baseStart_625166 baseEnd_625166 := by
    simpa [prefixWord, tailWord_625166, baseEnd_625166] using wordTrace_append hprefix tailTrace_625166
  have hstable : (prefixWord ++ tailWord_625166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625166).length < 2 ^ (prefixWord ++ tailWord_625166).sum := by decide
  have hdescent : baseEnd_625166 < baseStart_625166 := by decide
  rcases family_descends (prefixWord ++ tailWord_625166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625172 : List Nat := [2, 4, 3, 1, 1, 2, 1, 4, 2]
def baseStart_625172 : Nat := 118140960795 + 625172 * 2 ^ 59
def prefixEnd_625172 : Nat := 4983230072969 + 3 ^ 40 * 625172 * 2
def baseEnd_625172 : Nat := 285345535762429551444349

theorem tailTrace_625172 : CollatzResearch.WordTrace tailWord_625172 prefixEnd_625172 285345535762429551444349 := by
  unfold tailWord_625172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11400948045558044861122885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15201264060744059814830513 11400948045558044861122885)
  ·
    refine ⟨2137677758542133411460541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11400948045558044861122885 2137677758542133411460541)
    ·
      refine ⟨801629159453300029297703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2137677758542133411460541 801629159453300029297703)
      ·
        refine ⟨1202443739179950043946555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801629159453300029297703 1202443739179950043946555)
        ·
          refine ⟨1803665608769925065919833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202443739179950043946555 1803665608769925065919833)
          ·
            refine ⟨1352749206577443799439875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803665608769925065919833 1352749206577443799439875)
            ·
              refine ⟨2029123809866165699159813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352749206577443799439875 2029123809866165699159813)
              ·
                refine ⟨380460714349906068592465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2029123809866165699159813 380460714349906068592465)
                ·
                  refine ⟨285345535762429551444349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380460714349906068592465 285345535762429551444349)
                  ·
                    rfl

theorem cell20_625172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_625172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625172 prefixEnd_625172 := by exact prefixLift 625172
  have htrace : WordTrace (prefixWord ++ tailWord_625172) baseStart_625172 baseEnd_625172 := by
    simpa [prefixWord, tailWord_625172, baseEnd_625172] using wordTrace_append hprefix tailTrace_625172
  have hstable : (prefixWord ++ tailWord_625172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625172).length < 2 ^ (prefixWord ++ tailWord_625172).sum := by decide
  have hdescent : baseEnd_625172 < baseStart_625172 := by decide
  rcases family_descends (prefixWord ++ tailWord_625172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625220 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 3]
def baseStart_625220 : Nat := 118140960795 + 625220 * 2 ^ 59
def prefixEnd_625220 : Nat := 4983230072969 + 3 ^ 40 * 625220 * 2
def baseEnd_625220 : Nat := 285367444270354717844153

theorem tailTrace_625220 : CollatzResearch.WordTrace tailWord_625220 prefixEnd_625220 285367444270354717844153 := by
  unfold tailWord_625220
  simp only [CollatzResearch.WordTrace]
  refine ⟨11401823397471096959996557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15202431196628129279995409 11401823397471096959996557)
  ·
    refine ⟨4275683774051661359998709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11401823397471096959996557 4275683774051661359998709)
    ·
      refine ⟨400845353817343252499879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4275683774051661359998709 400845353817343252499879)
      ·
        refine ⟨601268030726014878749819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400845353817343252499879 601268030726014878749819)
        ·
          refine ⟨901902046089022318124729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601268030726014878749819 901902046089022318124729)
          ·
            refine ⟨676426534566766738593547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 901902046089022318124729 676426534566766738593547)
            ·
              refine ⟨1014639801850150107890321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676426534566766738593547 1014639801850150107890321)
              ·
                refine ⟨760979851387612580917741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014639801850150107890321 760979851387612580917741)
                ·
                  refine ⟨285367444270354717844153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760979851387612580917741 285367444270354717844153)
                  ·
                    rfl

theorem cell20_625220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_625220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625220 prefixEnd_625220 := by exact prefixLift 625220
  have htrace : WordTrace (prefixWord ++ tailWord_625220) baseStart_625220 baseEnd_625220 := by
    simpa [prefixWord, tailWord_625220, baseEnd_625220] using wordTrace_append hprefix tailTrace_625220
  have hstable : (prefixWord ++ tailWord_625220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625220).length < 2 ^ (prefixWord ++ tailWord_625220).sum := by decide
  have hdescent : baseEnd_625220 < baseStart_625220 := by decide
  rcases family_descends (prefixWord ++ tailWord_625220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625280 : List Nat := [2, 1, 1, 2, 1, 7, 6]
def baseStart_625280 : Nat := 118140960795 + 625280 * 2 ^ 59
def prefixEnd_625280 : Nat := 4983230072969 + 3 ^ 40 * 625280 * 2
def baseEnd_625280 : Nat := 31710536656140130649323

theorem tailTrace_625280 : CollatzResearch.WordTrace tailWord_625280 prefixEnd_625280 31710536656140130649323 := by
  unfold tailWord_625280
  simp only [CollatzResearch.WordTrace]
  refine ⟨11402917587362412083588647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15203890116483216111451529 11402917587362412083588647)
  ·
    refine ⟨17104376381043618125382971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11402917587362412083588647 17104376381043618125382971)
    ·
      refine ⟨25656564571565427188074457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17104376381043618125382971 25656564571565427188074457)
      ·
        refine ⟨19242423428674070391055843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25656564571565427188074457 19242423428674070391055843)
        ·
          refine ⟨28863635143011105586583765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19242423428674070391055843 28863635143011105586583765)
          ·
            refine ⟨676491448664322787185557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28863635143011105586583765 676491448664322787185557)
            ·
              refine ⟨31710536656140130649323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 676491448664322787185557 31710536656140130649323)
              ·
                rfl

theorem cell20_625280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 6].length) (baseStart_625280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625280 prefixEnd_625280 := by exact prefixLift 625280
  have htrace : WordTrace (prefixWord ++ tailWord_625280) baseStart_625280 baseEnd_625280 := by
    simpa [prefixWord, tailWord_625280, baseEnd_625280] using wordTrace_append hprefix tailTrace_625280
  have hstable : (prefixWord ++ tailWord_625280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625280).length < 2 ^ (prefixWord ++ tailWord_625280).sum := by decide
  have hdescent : baseEnd_625280 < baseStart_625280 := by decide
  rcases family_descends (prefixWord ++ tailWord_625280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625282 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_625282 : Nat := 118140960795 + 625282 * 2 ^ 59
def prefixEnd_625282 : Nat := 4983230072969 + 3 ^ 40 * 625282 * 2
def baseEnd_625282 : Nat := 285395742759758057777233

theorem tailTrace_625282 : CollatzResearch.WordTrace tailWord_625282 prefixEnd_625282 285395742759758057777233 := by
  unfold tailWord_625282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5701477030179394627187525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15203938747145052339166733 5701477030179394627187525)
  ·
    refine ⟨1069026943158636492597661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5701477030179394627187525 1069026943158636492597661)
    ·
      refine ⟨400885103684488684724123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1069026943158636492597661 400885103684488684724123)
      ·
        refine ⟨601327655526733027086185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400885103684488684724123 601327655526733027086185)
        ·
          refine ⟨450995741645049770314639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601327655526733027086185 450995741645049770314639)
          ·
            refine ⟨676493612467574655471959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450995741645049770314639 676493612467574655471959)
            ·
              refine ⟨1014740418701361983207939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676493612467574655471959 1014740418701361983207939)
              ·
                refine ⟨1522110628052042974811909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014740418701361983207939 1522110628052042974811909)
                ·
                  refine ⟨285395742759758057777233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1522110628052042974811909 285395742759758057777233)
                  ·
                    rfl

theorem cell20_625282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_625282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625282 prefixEnd_625282 := by exact prefixLift 625282
  have htrace : WordTrace (prefixWord ++ tailWord_625282) baseStart_625282 baseEnd_625282 := by
    simpa [prefixWord, tailWord_625282, baseEnd_625282] using wordTrace_append hprefix tailTrace_625282
  have hstable : (prefixWord ++ tailWord_625282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625282).length < 2 ^ (prefixWord ++ tailWord_625282).sum := by decide
  have hdescent : baseEnd_625282 < baseStart_625282 := by decide
  rcases family_descends (prefixWord ++ tailWord_625282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625287 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_625287 : Nat := 118140960795 + 625287 * 2 ^ 59
def prefixEnd_625287 : Nat := 4983230072969 + 3 ^ 40 * 625287 * 2
def baseEnd_625287 : Nat := 285398024896000262610545

theorem tailTrace_625287 : CollatzResearch.WordTrace tailWord_625287 prefixEnd_625287 285398024896000262610545 := by
  unfold tailWord_625287
  simp only [CollatzResearch.WordTrace]
  refine ⟨22806090485699464362682115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15204060323799642908454743 22806090485699464362682115)
  ·
    refine ⟨34209135728549196544023173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22806090485699464362682115 34209135728549196544023173)
    ·
      refine ⟨6414212949102974352004345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34209135728549196544023173 6414212949102974352004345)
      ·
        refine ⟨4810659711827230764003259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6414212949102974352004345 4810659711827230764003259)
        ·
          refine ⟨7215989567740846146004889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4810659711827230764003259 7215989567740846146004889)
          ·
            refine ⟨5411992175805634609503667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7215989567740846146004889 5411992175805634609503667)
            ·
              refine ⟨8117988263708451914255501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411992175805634609503667 8117988263708451914255501)
              ·
                refine ⟨3044245598890669467845813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8117988263708451914255501 3044245598890669467845813)
                ·
                  refine ⟨285398024896000262610545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3044245598890669467845813 285398024896000262610545)
                  ·
                    rfl

theorem cell20_625287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_625287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625287 prefixEnd_625287 := by exact prefixLift 625287
  have htrace : WordTrace (prefixWord ++ tailWord_625287) baseStart_625287 baseEnd_625287 := by
    simpa [prefixWord, tailWord_625287, baseEnd_625287] using wordTrace_append hprefix tailTrace_625287
  have hstable : (prefixWord ++ tailWord_625287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625287).length < 2 ^ (prefixWord ++ tailWord_625287).sum := by decide
  have hdescent : baseEnd_625287 < baseStart_625287 := by decide
  rcases family_descends (prefixWord ++ tailWord_625287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625300 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 3]
def baseStart_625300 : Nat := 118140960795 + 625300 * 2 ^ 59
def prefixEnd_625300 : Nat := 4983230072969 + 3 ^ 40 * 625300 * 2
def baseEnd_625300 : Nat := 285403958450229995177159

theorem tailTrace_625300 : CollatzResearch.WordTrace tailWord_625300 prefixEnd_625300 285403958450229995177159 := by
  unfold tailWord_625300
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403282317326183791452677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15204376423101578388603569 11403282317326183791452677)
  ·
    refine ⟨2138115434498659460897377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11403282317326183791452677 2138115434498659460897377)
    ·
      refine ⟨1603586575873994595673033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2138115434498659460897377 1603586575873994595673033)
      ·
        refine ⟨1202689931905495946754775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1603586575873994595673033 1202689931905495946754775)
        ·
          refine ⟨1804034897858243920132163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202689931905495946754775 1804034897858243920132163)
          ·
            refine ⟨2706052346787365880198245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804034897858243920132163 2706052346787365880198245)
            ·
              refine ⟨507384815022631102537171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2706052346787365880198245 507384815022631102537171)
              ·
                refine ⟨761077222533946653805757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507384815022631102537171 761077222533946653805757)
                ·
                  refine ⟨285403958450229995177159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761077222533946653805757 285403958450229995177159)
                  ·
                    rfl

theorem cell20_625300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_625300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625300 prefixEnd_625300 := by exact prefixLift 625300
  have htrace : WordTrace (prefixWord ++ tailWord_625300) baseStart_625300 baseEnd_625300 := by
    simpa [prefixWord, tailWord_625300, baseEnd_625300] using wordTrace_append hprefix tailTrace_625300
  have hstable : (prefixWord ++ tailWord_625300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625300).length < 2 ^ (prefixWord ++ tailWord_625300).sum := by decide
  have hdescent : baseEnd_625300 < baseStart_625300 := by decide
  rcases family_descends (prefixWord ++ tailWord_625300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625304 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_625304 : Nat := 118140960795 + 625304 * 2 ^ 59
def prefixEnd_625304 : Nat := 4983230072969 + 3 ^ 40 * 625304 * 2
def baseEnd_625304 : Nat := 285405784159223759043809

theorem tailTrace_625304 : CollatzResearch.WordTrace tailWord_625304 prefixEnd_625304 285405784159223759043809 := by
  unfold tailWord_625304
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403355263318938133025483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15204473684425250844033977 11403355263318938133025483)
  ·
    refine ⟨17105032894978407199538225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11403355263318938133025483 17105032894978407199538225)
    ·
      refine ⟨12828774671233805399653669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17105032894978407199538225 12828774671233805399653669)
      ·
        refine ⟨2405395250856338512435063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12828774671233805399653669 2405395250856338512435063)
        ·
          refine ⟨3608092876284507768652595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405395250856338512435063 3608092876284507768652595)
          ·
            refine ⟨5412139314426761652978893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608092876284507768652595 5412139314426761652978893)
            ·
              refine ⟨2029552242910035619867085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5412139314426761652978893 2029552242910035619867085)
              ·
                refine ⟨761082091091263357450157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2029552242910035619867085 761082091091263357450157)
                ·
                  refine ⟨285405784159223759043809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761082091091263357450157 285405784159223759043809)
                  ·
                    rfl

theorem cell20_625304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_625304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625304 prefixEnd_625304 := by exact prefixLift 625304
  have htrace : WordTrace (prefixWord ++ tailWord_625304) baseStart_625304 baseEnd_625304 := by
    simpa [prefixWord, tailWord_625304, baseEnd_625304] using wordTrace_append hprefix tailTrace_625304
  have hstable : (prefixWord ++ tailWord_625304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625304).length < 2 ^ (prefixWord ++ tailWord_625304).sum := by decide
  have hdescent : baseEnd_625304 < baseStart_625304 := by decide
  rcases family_descends (prefixWord ++ tailWord_625304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625394 : List Nat := [3, 2, 1, 3, 1, 3, 7]
def baseStart_625394 : Nat := 118140960795 + 625394 * 2 ^ 59
def prefixEnd_625394 : Nat := 4983230072969 + 3 ^ 40 * 625394 * 2
def baseEnd_625394 : Nat := 31716318067953716227049

theorem tailTrace_625394 : CollatzResearch.WordTrace tailWord_625394 prefixEnd_625394 31716318067953716227049 := by
  unfold tailWord_625394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702498274077955409206809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15206662064207881091218157 5702498274077955409206809)
  ·
    refine ⟨4276873705558466556905107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5702498274077955409206809 4276873705558466556905107)
    ·
      refine ⟨6415310558337699835357661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4276873705558466556905107 6415310558337699835357661)
      ·
        refine ⟨2405741459376637438259123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6415310558337699835357661 2405741459376637438259123)
        ·
          refine ⟨3608612189064956157388685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405741459376637438259123 3608612189064956157388685)
          ·
            refine ⟨1353229570899358559020757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3608612189064956157388685 1353229570899358559020757)
            ·
              refine ⟨31716318067953716227049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1353229570899358559020757 31716318067953716227049)
              ·
                rfl

theorem cell20_625394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 7].length) (baseStart_625394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625394 prefixEnd_625394 := by exact prefixLift 625394
  have htrace : WordTrace (prefixWord ++ tailWord_625394) baseStart_625394 baseEnd_625394 := by
    simpa [prefixWord, tailWord_625394, baseEnd_625394] using wordTrace_append hprefix tailTrace_625394
  have hstable : (prefixWord ++ tailWord_625394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625394).length < 2 ^ (prefixWord ++ tailWord_625394).sum := by decide
  have hdescent : baseEnd_625394 < baseStart_625394 := by decide
  rcases family_descends (prefixWord ++ tailWord_625394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625404 : List Nat := [2, 2, 2, 1, 3, 2, 2, 4, 2]
def baseStart_625404 : Nat := 118140960795 + 625404 * 2 ^ 59
def prefixEnd_625404 : Nat := 4983230072969 + 3 ^ 40 * 625404 * 2
def baseEnd_625404 : Nat := 285451426884067855710067

theorem tailTrace_625404 : CollatzResearch.WordTrace tailWord_625404 prefixEnd_625404 285451426884067855710067 := by
  unfold tailWord_625404
  simp only [CollatzResearch.WordTrace]
  refine ⟨11405178913137796672345633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15206905217517062229794177 11405178913137796672345633)
  ·
    refine ⟨8553884184853347504259225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11405178913137796672345633 8553884184853347504259225)
    ·
      refine ⟨6415413138640010628194419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8553884184853347504259225 6415413138640010628194419)
      ·
        refine ⟨9623119707960015942291629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6415413138640010628194419 9623119707960015942291629)
        ·
          refine ⟨3608669890485005978359361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9623119707960015942291629 3608669890485005978359361)
          ·
            refine ⟨2706502417863754483769521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3608669890485005978359361 2706502417863754483769521)
            ·
              refine ⟨2029876813397815862827141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2706502417863754483769521 2029876813397815862827141)
              ·
                refine ⟨380601902512090474280089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2029876813397815862827141 380601902512090474280089)
                ·
                  refine ⟨285451426884067855710067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380601902512090474280089 285451426884067855710067)
                  ·
                    rfl

theorem cell20_625404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_625404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625404 prefixEnd_625404 := by exact prefixLift 625404
  have htrace : WordTrace (prefixWord ++ tailWord_625404) baseStart_625404 baseEnd_625404 := by
    simpa [prefixWord, tailWord_625404, baseEnd_625404] using wordTrace_append hprefix tailTrace_625404
  have hstable : (prefixWord ++ tailWord_625404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625404).length < 2 ^ (prefixWord ++ tailWord_625404).sum := by decide
  have hdescent : baseEnd_625404 < baseStart_625404 := by decide
  rcases family_descends (prefixWord ++ tailWord_625404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625439 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_625439 : Nat := 118140960795 + 625439 * 2 ^ 59
def prefixEnd_625439 : Nat := 4983230072969 + 3 ^ 40 * 625439 * 2
def baseEnd_625439 : Nat := 285467401837763289543257

theorem tailTrace_625439 : CollatzResearch.WordTrace tailWord_625439 prefixEnd_625439 285467401837763289543257 := by
  unfold tailWord_625439
  simp only [CollatzResearch.WordTrace]
  refine ⟨22811634381148794322215371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15207756254099196214810247 22811634381148794322215371)
  ·
    refine ⟨34217451571723191483323057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22811634381148794322215371 34217451571723191483323057)
    ·
      refine ⟨25663088678792393612492293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34217451571723191483323057 25663088678792393612492293)
      ·
        refine ⟨4811829127273573802342305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25663088678792393612492293 4811829127273573802342305)
        ·
          refine ⟨3608871845455180351756729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4811829127273573802342305 3608871845455180351756729)
          ·
            refine ⟨2706653884091385263817547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3608871845455180351756729 2706653884091385263817547)
            ·
              refine ⟨4059980826137077895726321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706653884091385263817547 4059980826137077895726321)
              ·
                refine ⟨3044985619602808421794741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4059980826137077895726321 3044985619602808421794741)
                ·
                  refine ⟨285467401837763289543257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3044985619602808421794741 285467401837763289543257)
                  ·
                    rfl

theorem cell20_625439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_625439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625439 prefixEnd_625439 := by exact prefixLift 625439
  have htrace : WordTrace (prefixWord ++ tailWord_625439) baseStart_625439 baseEnd_625439 := by
    simpa [prefixWord, tailWord_625439, baseEnd_625439] using wordTrace_append hprefix tailTrace_625439
  have hstable : (prefixWord ++ tailWord_625439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625439).length < 2 ^ (prefixWord ++ tailWord_625439).sum := by decide
  have hdescent : baseEnd_625439 < baseStart_625439 := by decide
  rcases family_descends (prefixWord ++ tailWord_625439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625459 : List Nat := [1, 1, 1, 2, 6, 2, 3, 2, 2]
def baseStart_625459 : Nat := 118140960795 + 625459 * 2 ^ 59
def prefixEnd_625459 : Nat := 4983230072969 + 3 ^ 40 * 625459 * 2
def baseEnd_625459 : Nat := 285476530382732108876509

theorem tailTrace_625459 : CollatzResearch.WordTrace tailWord_625459 prefixEnd_625459 285476530382732108876509 := by
  unfold tailWord_625459
  simp only [CollatzResearch.WordTrace]
  refine ⟨22812363841076337737943431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15208242560717558491962287 22812363841076337737943431)
  ·
    refine ⟨34218545761614506606915147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22812363841076337737943431 34218545761614506606915147)
    ·
      refine ⟨51327818642421759910372721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34218545761614506606915147 51327818642421759910372721)
      ·
        refine ⟨38495863981816319932779541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51327818642421759910372721 38495863981816319932779541)
        ·
          refine ⟨1804493624147639996849041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38495863981816319932779541 1804493624147639996849041)
          ·
            refine ⟨1353370218110729997636781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804493624147639996849041 1353370218110729997636781)
            ·
              refine ⟨507513831791523749113793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1353370218110729997636781 507513831791523749113793)
              ·
                refine ⟨380635373843642811835345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507513831791523749113793 380635373843642811835345)
                ·
                  refine ⟨285476530382732108876509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380635373843642811835345 285476530382732108876509)
                  ·
                    rfl

theorem cell20_625459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 2].length) (baseStart_625459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625459 prefixEnd_625459 := by exact prefixLift 625459
  have htrace : WordTrace (prefixWord ++ tailWord_625459) baseStart_625459 baseEnd_625459 := by
    simpa [prefixWord, tailWord_625459, baseEnd_625459] using wordTrace_append hprefix tailTrace_625459
  have hstable : (prefixWord ++ tailWord_625459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625459).length < 2 ^ (prefixWord ++ tailWord_625459).sum := by decide
  have hdescent : baseEnd_625459 < baseStart_625459 := by decide
  rcases family_descends (prefixWord ++ tailWord_625459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625469 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 3]
def baseStart_625469 : Nat := 118140960795 + 625469 * 2 ^ 59
def prefixEnd_625469 : Nat := 4983230072969 + 3 ^ 40 * 625469 * 2
def baseEnd_625469 : Nat := 285481094655216518543135

theorem tailTrace_625469 : CollatzResearch.WordTrace tailWord_625469 prefixEnd_625469 285481094655216518543135 := by
  unfold tailWord_625469
  simp only [CollatzResearch.WordTrace]
  refine ⟨22812728571040109445807461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15208485714026739630538307 22812728571040109445807461)
  ·
    refine ⟨4277386607070020521088899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22812728571040109445807461 4277386607070020521088899)
    ·
      refine ⟨6416079910605030781633349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4277386607070020521088899 6416079910605030781633349)
      ·
        refine ⟨1203014983238443271556253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6416079910605030781633349 1203014983238443271556253)
        ·
          refine ⟨451130618714416226833595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1203014983238443271556253 451130618714416226833595)
          ·
            refine ⟨676695928071624340250393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451130618714416226833595 676695928071624340250393)
            ·
              refine ⟨507521946053718255187795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676695928071624340250393 507521946053718255187795)
              ·
                refine ⟨761282919080577382781693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507521946053718255187795 761282919080577382781693)
                ·
                  refine ⟨285481094655216518543135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761282919080577382781693 285481094655216518543135)
                  ·
                    rfl

theorem cell20_625469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_625469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625469 prefixEnd_625469 := by exact prefixLift 625469
  have htrace : WordTrace (prefixWord ++ tailWord_625469) baseStart_625469 baseEnd_625469 := by
    simpa [prefixWord, tailWord_625469, baseEnd_625469] using wordTrace_append hprefix tailTrace_625469
  have hstable : (prefixWord ++ tailWord_625469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625469).length < 2 ^ (prefixWord ++ tailWord_625469).sum := by decide
  have hdescent : baseEnd_625469 < baseStart_625469 := by decide
  rcases family_descends (prefixWord ++ tailWord_625469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625515 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 3]
def baseStart_625515 : Nat := 118140960795 + 625515 * 2 ^ 59
def prefixEnd_625515 : Nat := 4983230072969 + 3 ^ 40 * 625515 * 2
def baseEnd_625515 : Nat := 285502090308644803009613

theorem tailTrace_625515 : CollatzResearch.WordTrace tailWord_625515 prefixEnd_625515 285502090308644803009613 := by
  unfold tailWord_625515
  simp only [CollatzResearch.WordTrace]
  refine ⟨22814406328873459301981999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15209604219248972867987999 22814406328873459301981999)
  ·
    refine ⟨34221609493310188952972999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22814406328873459301981999 34221609493310188952972999)
    ·
      refine ⟨51332414239965283429459499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34221609493310188952972999 51332414239965283429459499)
      ·
        refine ⟨76998621359947925144189249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51332414239965283429459499 76998621359947925144189249)
        ·
          refine ⟨57748966019960943858141937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76998621359947925144189249 57748966019960943858141937)
          ·
            refine ⟨43311724514970707893606453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57748966019960943858141937 43311724514970707893606453)
            ·
              refine ⟨4060474173278503865025605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43311724514970707893606453 4060474173278503865025605)
              ·
                refine ⟨761338907489719474692301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4060474173278503865025605 761338907489719474692301)
                ·
                  refine ⟨285502090308644803009613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761338907489719474692301 285502090308644803009613)
                  ·
                    rfl

theorem cell20_625515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_625515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625515 prefixEnd_625515 := by exact prefixLift 625515
  have htrace : WordTrace (prefixWord ++ tailWord_625515) baseStart_625515 baseEnd_625515 := by
    simpa [prefixWord, tailWord_625515, baseEnd_625515] using wordTrace_append hprefix tailTrace_625515
  have hstable : (prefixWord ++ tailWord_625515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625515).length < 2 ^ (prefixWord ++ tailWord_625515).sum := by decide
  have hdescent : baseEnd_625515 < baseStart_625515 := by decide
  rcases family_descends (prefixWord ++ tailWord_625515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625525 : List Nat := [1, 3, 4, 1, 1, 4, 1, 5]
def baseStart_625525 : Nat := 118140960795 + 625525 * 2 ^ 59
def prefixEnd_625525 : Nat := 4983230072969 + 3 ^ 40 * 625525 * 2
def baseEnd_625525 : Nat := 95168884860376404225413

theorem tailTrace_625525 : CollatzResearch.WordTrace tailWord_625525 prefixEnd_625525 95168884860376404225413 := by
  unfold tailWord_625525
  simp only [CollatzResearch.WordTrace]
  refine ⟨22814771058837231009846029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15209847372558154006564019 22814771058837231009846029)
  ·
    refine ⟨8555539147063961628692261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22814771058837231009846029 8555539147063961628692261)
    ·
      refine ⟨1604163590074492805379799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8555539147063961628692261 1604163590074492805379799)
      ·
        refine ⟨2406245385111739208069699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604163590074492805379799 2406245385111739208069699)
        ·
          refine ⟨3609368077667608812104549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2406245385111739208069699 3609368077667608812104549)
          ·
            refine ⟨676756514562676652269603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3609368077667608812104549 676756514562676652269603)
            ·
              refine ⟨1015134771844014978404405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676756514562676652269603 1015134771844014978404405)
              ·
                refine ⟨95168884860376404225413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1015134771844014978404405 95168884860376404225413)
                ·
                  rfl

theorem cell20_625525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 5].length) (baseStart_625525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625525 prefixEnd_625525 := by exact prefixLift 625525
  have htrace : WordTrace (prefixWord ++ tailWord_625525) baseStart_625525 baseEnd_625525 := by
    simpa [prefixWord, tailWord_625525, baseEnd_625525] using wordTrace_append hprefix tailTrace_625525
  have hstable : (prefixWord ++ tailWord_625525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625525).length < 2 ^ (prefixWord ++ tailWord_625525).sum := by decide
  have hdescent : baseEnd_625525 < baseStart_625525 := by decide
  rcases family_descends (prefixWord ++ tailWord_625525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625570 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_625570 : Nat := 118140960795 + 625570 * 2 ^ 59
def prefixEnd_625570 : Nat := 4983230072969 + 3 ^ 40 * 625570 * 2
def baseEnd_625570 : Nat := 285527193807309056176055

theorem tailTrace_625570 : CollatzResearch.WordTrace tailWord_625570 prefixEnd_625570 285527193807309056176055 := by
  unfold tailWord_625570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5704103085918550923808541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15210941562449469130156109 5704103085918550923808541)
  ·
    refine ⟨2139038657219456596428203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5704103085918550923808541 2139038657219456596428203)
    ·
      refine ⟨3208557985829184894642305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2139038657219456596428203 3208557985829184894642305)
      ·
        refine ⟨2406418489371888670981729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3208557985829184894642305 2406418489371888670981729)
        ·
          refine ⟨1804813867028916503236297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2406418489371888670981729 1804813867028916503236297)
          ·
            refine ⟨1353610400271687377427223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804813867028916503236297 1353610400271687377427223)
            ·
              refine ⟨2030415600407531066140835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353610400271687377427223 2030415600407531066140835)
              ·
                refine ⟨3045623400611296599211253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030415600407531066140835 3045623400611296599211253)
                ·
                  refine ⟨285527193807309056176055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3045623400611296599211253 285527193807309056176055)
                  ·
                    rfl

theorem cell20_625570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_625570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625570 prefixEnd_625570 := by exact prefixLift 625570
  have htrace : WordTrace (prefixWord ++ tailWord_625570) baseStart_625570 baseEnd_625570 := by
    simpa [prefixWord, tailWord_625570, baseEnd_625570] using wordTrace_append hprefix tailTrace_625570
  have hstable : (prefixWord ++ tailWord_625570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625570).length < 2 ^ (prefixWord ++ tailWord_625570).sum := by decide
  have hdescent : baseEnd_625570 < baseStart_625570 := by decide
  rcases family_descends (prefixWord ++ tailWord_625570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625577 : List Nat := [1, 2, 1, 1, 1, 1, 5, 6, 2]
def baseStart_625577 : Nat := 118140960795 + 625577 * 2 ^ 59
def prefixEnd_625577 : Nat := 4983230072969 + 3 ^ 40 * 625577 * 2
def baseEnd_625577 : Nat := 285530388798048142942693

theorem tailTrace_625577 : CollatzResearch.WordTrace tailWord_625577 prefixEnd_625577 285530388798048142942693 := by
  unfold tailWord_625577
  simp only [CollatzResearch.WordTrace]
  refine ⟨22816667654648843890738985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15211111769765895927159323 22816667654648843890738985)
  ·
    refine ⟨17112500740986632918054239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22816667654648843890738985 17112500740986632918054239)
    ·
      refine ⟨25668751111479949377081359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17112500740986632918054239 25668751111479949377081359)
      ·
        refine ⟨38503126667219924065622039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25668751111479949377081359 38503126667219924065622039)
        ·
          refine ⟨57754690000829886098433059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38503126667219924065622039 57754690000829886098433059)
          ·
            refine ⟨86632035001244829147649589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57754690000829886098433059 86632035001244829147649589)
            ·
              refine ⟨8121753281366702732592149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86632035001244829147649589 8121753281366702732592149)
              ·
                refine ⟨380707185064064190590257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8121753281366702732592149 380707185064064190590257)
                ·
                  refine ⟨285530388798048142942693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380707185064064190590257 285530388798048142942693)
                  ·
                    rfl

theorem cell20_625577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_625577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625577 prefixEnd_625577 := by exact prefixLift 625577
  have htrace : WordTrace (prefixWord ++ tailWord_625577) baseStart_625577 baseEnd_625577 := by
    simpa [prefixWord, tailWord_625577, baseEnd_625577] using wordTrace_append hprefix tailTrace_625577
  have hstable : (prefixWord ++ tailWord_625577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625577).length < 2 ^ (prefixWord ++ tailWord_625577).sum := by decide
  have hdescent : baseEnd_625577 < baseStart_625577 := by decide
  rcases family_descends (prefixWord ++ tailWord_625577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625591 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 3]
def baseStart_625591 : Nat := 118140960795 + 625591 * 2 ^ 59
def prefixEnd_625591 : Nat := 4983230072969 + 3 ^ 40 * 625591 * 2
def baseEnd_625591 : Nat := 285536778779526316475969

theorem tailTrace_625591 : CollatzResearch.WordTrace tailWord_625591 prefixEnd_625591 285536778779526316475969 := by
  unfold tailWord_625591
  simp only [CollatzResearch.WordTrace]
  refine ⟨22817178276598124281748627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15211452184398749521165751 22817178276598124281748627)
  ·
    refine ⟨34225767414897186422622941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22817178276598124281748627 34225767414897186422622941)
    ·
      refine ⟨12834662780586444908483603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34225767414897186422622941 12834662780586444908483603)
      ·
        refine ⟨19251994170879667362725405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12834662780586444908483603 19251994170879667362725405)
        ·
          refine ⟨7219497814079875261022027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19251994170879667362725405 7219497814079875261022027)
          ·
            refine ⟨10829246721119812891533041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7219497814079875261022027 10829246721119812891533041)
            ·
              refine ⟨8121935040839859668649781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10829246721119812891533041 8121935040839859668649781)
              ·
                refine ⟨761431410078736843935917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8121935040839859668649781 761431410078736843935917)
                ·
                  refine ⟨285536778779526316475969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761431410078736843935917 285536778779526316475969)
                  ·
                    rfl

theorem cell20_625591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 3].length) (baseStart_625591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625591 prefixEnd_625591 := by exact prefixLift 625591
  have htrace : WordTrace (prefixWord ++ tailWord_625591) baseStart_625591 baseEnd_625591 := by
    simpa [prefixWord, tailWord_625591, baseEnd_625591] using wordTrace_append hprefix tailTrace_625591
  have hstable : (prefixWord ++ tailWord_625591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625591).length < 2 ^ (prefixWord ++ tailWord_625591).sum := by decide
  have hdescent : baseEnd_625591 < baseStart_625591 := by decide
  rcases family_descends (prefixWord ++ tailWord_625591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625636 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 4]
def baseStart_625636 : Nat := 118140960795 + 625636 * 2 ^ 59
def prefixEnd_625636 : Nat := 4983230072969 + 3 ^ 40 * 625636 * 2
def baseEnd_625636 : Nat := 285557318005706159975785

theorem tailTrace_625636 : CollatzResearch.WordTrace tailWord_625636 prefixEnd_625636 285557318005706159975785 := by
  unfold tailWord_625636
  simp only [CollatzResearch.WordTrace]
  refine ⟨11409409780717548483568381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15212546374290064644757841 11409409780717548483568381)
  ·
    refine ⟨4278528667769080681338143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11409409780717548483568381 4278528667769080681338143)
    ·
      refine ⟨6417793001653621022007215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4278528667769080681338143 6417793001653621022007215)
      ·
        refine ⟨9626689502480431533010823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417793001653621022007215 9626689502480431533010823)
        ·
          refine ⟨14440034253720647299516235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9626689502480431533010823 14440034253720647299516235)
          ·
            refine ⟨21660051380580970949274353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14440034253720647299516235 21660051380580970949274353)
            ·
              refine ⟨16245038535435728211955765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21660051380580970949274353 16245038535435728211955765)
              ·
                refine ⟨1522972362697099519870853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16245038535435728211955765 1522972362697099519870853)
                ·
                  refine ⟨285557318005706159975785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1522972362697099519870853 285557318005706159975785)
                  ·
                    rfl

theorem cell20_625636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_625636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625636 prefixEnd_625636 := by exact prefixLift 625636
  have htrace : WordTrace (prefixWord ++ tailWord_625636) baseStart_625636 baseEnd_625636 := by
    simpa [prefixWord, tailWord_625636, baseEnd_625636] using wordTrace_append hprefix tailTrace_625636
  have hstable : (prefixWord ++ tailWord_625636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625636).length < 2 ^ (prefixWord ++ tailWord_625636).sum := by decide
  have hdescent : baseEnd_625636 < baseStart_625636 := by decide
  rcases family_descends (prefixWord ++ tailWord_625636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625687 : List Nat := [1, 1, 3, 5, 1, 1, 4, 2, 2]
def baseStart_625687 : Nat := 118140960795 + 625687 * 2 ^ 59
def prefixEnd_625687 : Nat := 4983230072969 + 3 ^ 40 * 625687 * 2
def baseEnd_625687 : Nat := 285580595795376649275577

theorem tailTrace_625687 : CollatzResearch.WordTrace tailWord_625687 prefixEnd_625687 285580595795376649275577 := by
  unfold tailWord_625687
  simp only [CollatzResearch.WordTrace]
  refine ⟨22820679684250332677243315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15213786456166888451495543 22820679684250332677243315)
  ·
    refine ⟨34231019526375499015864973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22820679684250332677243315 34231019526375499015864973)
    ·
      refine ⟨12836632322390812130949365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34231019526375499015864973 12836632322390812130949365)
      ·
        refine ⟨1203434280224138637276503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12836632322390812130949365 1203434280224138637276503)
        ·
          refine ⟨1805151420336207955914755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203434280224138637276503 1805151420336207955914755)
          ·
            refine ⟨2707727130504311933872133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805151420336207955914755 2707727130504311933872133)
            ·
              refine ⟨507698836969558487601025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2707727130504311933872133 507698836969558487601025)
              ·
                refine ⟨380774127727168865700769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507698836969558487601025 380774127727168865700769)
                ·
                  refine ⟨285580595795376649275577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380774127727168865700769 285580595795376649275577)
                  ·
                    rfl

theorem cell20_625687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 2].length) (baseStart_625687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625687 prefixEnd_625687 := by exact prefixLift 625687
  have htrace : WordTrace (prefixWord ++ tailWord_625687) baseStart_625687 baseEnd_625687 := by
    simpa [prefixWord, tailWord_625687, baseEnd_625687] using wordTrace_append hprefix tailTrace_625687
  have hstable : (prefixWord ++ tailWord_625687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625687).length < 2 ^ (prefixWord ++ tailWord_625687).sum := by decide
  have hdescent : baseEnd_625687 < baseStart_625687 := by decide
  rcases family_descends (prefixWord ++ tailWord_625687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625698 : List Nat := [3, 3, 1, 1, 1, 3, 3, 5]
def baseStart_625698 : Nat := 118140960795 + 625698 * 2 ^ 59
def prefixEnd_625698 : Nat := 4983230072969 + 3 ^ 40 * 625698 * 2
def baseEnd_625698 : Nat := 95195205498369833302955

theorem tailTrace_625698 : CollatzResearch.WordTrace tailWord_625698 prefixEnd_625698 95195205498369833302955 := by
  unfold tailWord_625698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705270221802620388973437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15214053924806987703929165 5705270221802620388973437)
  ·
    refine ⟨2139476333175982645865039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5705270221802620388973437 2139476333175982645865039)
    ·
      refine ⟨3209214499763973968797559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2139476333175982645865039 3209214499763973968797559)
      ·
        refine ⟨4813821749645960953196339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3209214499763973968797559 4813821749645960953196339)
        ·
          refine ⟨7220732624468941429794509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4813821749645960953196339 7220732624468941429794509)
          ·
            refine ⟨2707774734175853036172941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7220732624468941429794509 2707774734175853036172941)
            ·
              refine ⟨1015415525315944888564853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2707774734175853036172941 1015415525315944888564853)
              ·
                refine ⟨95195205498369833302955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1015415525315944888564853 95195205498369833302955)
                ·
                  rfl

theorem cell20_625698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_625698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625698 prefixEnd_625698 := by exact prefixLift 625698
  have htrace : WordTrace (prefixWord ++ tailWord_625698) baseStart_625698 baseEnd_625698 := by
    simpa [prefixWord, tailWord_625698, baseEnd_625698] using wordTrace_append hprefix tailTrace_625698
  have hstable : (prefixWord ++ tailWord_625698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625698).length < 2 ^ (prefixWord ++ tailWord_625698).sum := by decide
  have hdescent : baseEnd_625698 < baseStart_625698 := by decide
  rcases family_descends (prefixWord ++ tailWord_625698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625712 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_625712 : Nat := 118140960795 + 625712 * 2 ^ 59
def prefixEnd_625712 : Nat := 4983230072969 + 3 ^ 40 * 625712 * 2
def baseEnd_625712 : Nat := 285592006476587673442141

theorem tailTrace_625712 : CollatzResearch.WordTrace tailWord_625712 prefixEnd_625712 285592006476587673442141 := by
  unfold tailWord_625712
  simp only [CollatzResearch.WordTrace]
  refine ⟨11410795754579880973451695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15214394339439841297935593 11410795754579880973451695)
  ·
    refine ⟨17116193631869821460177543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11410795754579880973451695 17116193631869821460177543)
    ·
      refine ⟨25674290447804732190266315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17116193631869821460177543 25674290447804732190266315)
      ·
        refine ⟨38511435671707098285399473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25674290447804732190266315 38511435671707098285399473)
        ·
          refine ⟨28883576753780323714049605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38511435671707098285399473 28883576753780323714049605)
          ·
            refine ⟨5415670641333810696384301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28883576753780323714049605 5415670641333810696384301)
            ·
              refine ⟨2030876490500179011144113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5415670641333810696384301 2030876490500179011144113)
              ·
                refine ⟨1523157367875134258358085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030876490500179011144113 1523157367875134258358085)
                ·
                  refine ⟨285592006476587673442141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523157367875134258358085 285592006476587673442141)
                  ·
                    rfl

theorem cell20_625712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_625712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625712 prefixEnd_625712 := by exact prefixLift 625712
  have htrace : WordTrace (prefixWord ++ tailWord_625712) baseStart_625712 baseEnd_625712 := by
    simpa [prefixWord, tailWord_625712, baseEnd_625712] using wordTrace_append hprefix tailTrace_625712
  have hstable : (prefixWord ++ tailWord_625712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625712).length < 2 ^ (prefixWord ++ tailWord_625712).sum := by decide
  have hdescent : baseEnd_625712 < baseStart_625712 := by decide
  rcases family_descends (prefixWord ++ tailWord_625712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625746 : List Nat := [3, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_625746 : Nat := 118140960795 + 625746 * 2 ^ 59
def prefixEnd_625746 : Nat := 4983230072969 + 3 ^ 40 * 625746 * 2
def baseEnd_625746 : Nat := 285607525003034666308669

theorem tailTrace_625746 : CollatzResearch.WordTrace tailWord_625746 prefixEnd_625746 285607525003034666308669 := by
  unfold tailWord_625746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705707897759146438410273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15215221060691057169094061 5705707897759146438410273)
  ·
    refine ⟨4279280923319359828807705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5705707897759146438410273 4279280923319359828807705)
    ·
      refine ⟨3209460692489519871605779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4279280923319359828807705 3209460692489519871605779)
      ·
        refine ⟨4814191038734279807408669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3209460692489519871605779 4814191038734279807408669)
        ·
          refine ⟨1805321639525354927778251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4814191038734279807408669 1805321639525354927778251)
          ·
            refine ⟨2707982459288032391667377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805321639525354927778251 2707982459288032391667377)
            ·
              refine ⟨2030986844466024293750533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2707982459288032391667377 2030986844466024293750533)
              ·
                refine ⟨380810033337379555078225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2030986844466024293750533 380810033337379555078225)
                ·
                  refine ⟨285607525003034666308669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380810033337379555078225 285607525003034666308669)
                  ·
                    rfl

theorem cell20_625746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_625746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625746 prefixEnd_625746 := by exact prefixLift 625746
  have htrace : WordTrace (prefixWord ++ tailWord_625746) baseStart_625746 baseEnd_625746 := by
    simpa [prefixWord, tailWord_625746, baseEnd_625746] using wordTrace_append hprefix tailTrace_625746
  have hstable : (prefixWord ++ tailWord_625746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625746).length < 2 ^ (prefixWord ++ tailWord_625746).sum := by decide
  have hdescent : baseEnd_625746 < baseStart_625746 := by decide
  rcases family_descends (prefixWord ++ tailWord_625746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625760 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 3]
def baseStart_625760 : Nat := 118140960795 + 625760 * 2 ^ 59
def prefixEnd_625760 : Nat := 4983230072969 + 3 ^ 40 * 625760 * 2
def baseEnd_625760 : Nat := 285613914984512839841945

theorem tailTrace_625760 : CollatzResearch.WordTrace tailWord_625760 prefixEnd_625760 285613914984512839841945 := by
  unfold tailWord_625760
  simp only [CollatzResearch.WordTrace]
  refine ⟨11411671106492933072325367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15215561475323910763100489 11411671106492933072325367)
  ·
    refine ⟨17117506659739399608488051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11411671106492933072325367 17117506659739399608488051)
    ·
      refine ⟨25676259989609099412732077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17117506659739399608488051 25676259989609099412732077)
      ·
        refine ⟨9628597496103412279774529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25676259989609099412732077 9628597496103412279774529)
        ·
          refine ⟨7221448122077559209830897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9628597496103412279774529 7221448122077559209830897)
          ·
            refine ⟨5416086091558169407373173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7221448122077559209830897 5416086091558169407373173)
            ·
              refine ⟨507758071083578381941235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5416086091558169407373173 507758071083578381941235)
              ·
                refine ⟨761637106625367572911853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507758071083578381941235 761637106625367572911853)
                ·
                  refine ⟨285613914984512839841945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761637106625367572911853 285613914984512839841945)
                  ·
                    rfl

theorem cell20_625760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_625760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625760 prefixEnd_625760 := by exact prefixLift 625760
  have htrace : WordTrace (prefixWord ++ tailWord_625760) baseStart_625760 baseEnd_625760 := by
    simpa [prefixWord, tailWord_625760, baseEnd_625760] using wordTrace_append hprefix tailTrace_625760
  have hstable : (prefixWord ++ tailWord_625760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625760).length < 2 ^ (prefixWord ++ tailWord_625760).sum := by decide
  have hdescent : baseEnd_625760 < baseStart_625760 := by decide
  rcases family_descends (prefixWord ++ tailWord_625760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625774 : List Nat := [4, 1, 2, 2, 1, 3, 1, 6]
def baseStart_625774 : Nat := 118140960795 + 625774 * 2 ^ 59
def prefixEnd_625774 : Nat := 4983230072969 + 3 ^ 40 * 625774 * 2
def baseEnd_625774 : Nat := 95206768321997004458407

theorem tailTrace_625774 : CollatzResearch.WordTrace tailWord_625774 prefixEnd_625774 95206768321997004458407 := by
  unfold tailWord_625774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852981604366893316957547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15215901889956764357106917 2852981604366893316957547)
  ·
    refine ⟨4279472406550339975436321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2852981604366893316957547 4279472406550339975436321)
    ·
      refine ⟨3209604304912754981577241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4279472406550339975436321 3209604304912754981577241)
      ·
        refine ⟨2407203228684566236182931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3209604304912754981577241 2407203228684566236182931)
        ·
          refine ⟨3610804843026849354274397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407203228684566236182931 3610804843026849354274397)
          ·
            refine ⟨1354051816135068507852899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3610804843026849354274397 1354051816135068507852899)
            ·
              refine ⟨2031077724202602761779349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354051816135068507852899 2031077724202602761779349)
              ·
                refine ⟨95206768321997004458407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2031077724202602761779349 95206768321997004458407)
                ·
                  rfl

theorem cell20_625774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_625774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625774 prefixEnd_625774 := by exact prefixLift 625774
  have htrace : WordTrace (prefixWord ++ tailWord_625774) baseStart_625774 baseEnd_625774 := by
    simpa [prefixWord, tailWord_625774, baseEnd_625774] using wordTrace_append hprefix tailTrace_625774
  have hstable : (prefixWord ++ tailWord_625774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625774).length < 2 ^ (prefixWord ++ tailWord_625774).sum := by decide
  have hdescent : baseEnd_625774 < baseStart_625774 := by decide
  rcases family_descends (prefixWord ++ tailWord_625774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625815 : List Nat := [1, 1, 3, 3, 3, 3, 2, 1, 3]
def baseStart_625815 : Nat := 118140960795 + 625815 * 2 ^ 59
def prefixEnd_625815 : Nat := 4983230072969 + 3 ^ 40 * 625815 * 2
def baseEnd_625815 : Nat := 285639018483177093008387

theorem tailTrace_625815 : CollatzResearch.WordTrace tailWord_625815 prefixEnd_625815 285639018483177093008387 := by
  unfold tailWord_625815
  simp only [CollatzResearch.WordTrace]
  refine ⟨22825348227786610537902899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15216898818524407025268599 22825348227786610537902899)
  ·
    refine ⟨34238022341679915806854349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22825348227786610537902899 34238022341679915806854349)
    ·
      refine ⟨12839258378129968427570381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34238022341679915806854349 12839258378129968427570381)
      ·
        refine ⟨4814721891798738160338893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12839258378129968427570381 4814721891798738160338893)
        ·
          refine ⟨1805520709424526810127085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4814721891798738160338893 1805520709424526810127085)
          ·
            refine ⟨677070266034197553797657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1805520709424526810127085 677070266034197553797657)
            ·
              refine ⟨507802699525648165348243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677070266034197553797657 507802699525648165348243)
              ·
                refine ⟨761704049288472248022365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507802699525648165348243 761704049288472248022365)
                ·
                  refine ⟨285639018483177093008387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761704049288472248022365 285639018483177093008387)
                  ·
                    rfl

theorem cell20_625815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 3].length) (baseStart_625815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625815 prefixEnd_625815 := by exact prefixLift 625815
  have htrace : WordTrace (prefixWord ++ tailWord_625815) baseStart_625815 baseEnd_625815 := by
    simpa [prefixWord, tailWord_625815, baseEnd_625815] using wordTrace_append hprefix tailTrace_625815
  have hstable : (prefixWord ++ tailWord_625815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625815).length < 2 ^ (prefixWord ++ tailWord_625815).sum := by decide
  have hdescent : baseEnd_625815 < baseStart_625815 := by decide
  rcases family_descends (prefixWord ++ tailWord_625815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625846 : List Nat := [5, 1, 3, 2, 2, 7]
def baseStart_625846 : Nat := 118140960795 + 625846 * 2 ^ 59
def prefixEnd_625846 : Nat := 4983230072969 + 3 ^ 40 * 625846 * 2
def baseEnd_625846 : Nat := 10579746952884398628701

theorem tailTrace_625846 : CollatzResearch.WordTrace tailWord_625846 prefixEnd_625846 10579746952884398628701 := by
  unfold tailWord_625846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426654930667143927017587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15217652593782868554854261 1426654930667143927017587)
  ·
    refine ⟨2139982396000715890526381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1426654930667143927017587 2139982396000715890526381)
    ·
      refine ⟨802493398500268458947393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2139982396000715890526381 802493398500268458947393)
      ·
        refine ⟨601870048875201344210545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 802493398500268458947393 601870048875201344210545)
        ·
          refine ⟨451402536656401008157909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601870048875201344210545 451402536656401008157909)
          ·
            refine ⟨10579746952884398628701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 451402536656401008157909 10579746952884398628701)
            ·
              rfl

theorem cell20_625846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 7].length) (baseStart_625846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625846 prefixEnd_625846 := by exact prefixLift 625846
  have htrace : WordTrace (prefixWord ++ tailWord_625846) baseStart_625846 baseEnd_625846 := by
    simpa [prefixWord, tailWord_625846, baseEnd_625846] using wordTrace_append hprefix tailTrace_625846
  have hstable : (prefixWord ++ tailWord_625846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625846).length < 2 ^ (prefixWord ++ tailWord_625846).sum := by decide
  have hdescent : baseEnd_625846 < baseStart_625846 := by decide
  rcases family_descends (prefixWord ++ tailWord_625846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625856 : List Nat := [2, 1, 1, 2, 7, 1, 2, 2, 2]
def baseStart_625856 : Nat := 118140960795 + 625856 * 2 ^ 59
def prefixEnd_625856 : Nat := 4983230072969 + 3 ^ 40 * 625856 * 2
def baseEnd_625856 : Nat := 285657732000363172641553

theorem tailTrace_625856 : CollatzResearch.WordTrace tailWord_625856 prefixEnd_625856 285657732000363172641553 := by
  unfold tailWord_625856
  simp only [CollatzResearch.WordTrace]
  refine ⟨11413421810319037270072711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15217895747092049693430281 11413421810319037270072711)
  ·
    refine ⟨17120132715478555905109067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11413421810319037270072711 17120132715478555905109067)
    ·
      refine ⟨25680199073217833857663601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17120132715478555905109067 25680199073217833857663601)
      ·
        refine ⟨19260149304913375393247701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25680199073217833857663601 19260149304913375393247701)
        ·
          refine ⟨451409749333907235779243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19260149304913375393247701 451409749333907235779243)
          ·
            refine ⟨677114624000860853668865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451409749333907235779243 677114624000860853668865)
            ·
              refine ⟨507835968000645640251649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677114624000860853668865 507835968000645640251649)
              ·
                refine ⟨380876976000484230188737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507835968000645640251649 380876976000484230188737)
                ·
                  refine ⟨285657732000363172641553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380876976000484230188737 285657732000363172641553)
                  ·
                    rfl

theorem cell20_625856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_625856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625856 prefixEnd_625856 := by exact prefixLift 625856
  have htrace : WordTrace (prefixWord ++ tailWord_625856) baseStart_625856 baseEnd_625856 := by
    simpa [prefixWord, tailWord_625856, baseEnd_625856] using wordTrace_append hprefix tailTrace_625856
  have hstable : (prefixWord ++ tailWord_625856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625856).length < 2 ^ (prefixWord ++ tailWord_625856).sum := by decide
  have hdescent : baseEnd_625856 < baseStart_625856 := by decide
  rcases family_descends (prefixWord ++ tailWord_625856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625888 : List Nat := [2, 1, 1, 3, 1, 5, 3, 4]
def baseStart_625888 : Nat := 118140960795 + 625888 * 2 ^ 59
def prefixEnd_625888 : Nat := 4983230072969 + 3 ^ 40 * 625888 * 2
def baseEnd_625888 : Nat := 95224112557437761191585

theorem tailTrace_625888 : CollatzResearch.WordTrace tailWord_625888 prefixEnd_625888 95224112557437761191585 := by
  unfold tailWord_625888
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414005378261072002655159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15218673837681429336873545 11414005378261072002655159)
  ·
    refine ⟨17121008067391608003982739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11414005378261072002655159 17121008067391608003982739)
    ·
      refine ⟨25681512101087412005974109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17121008067391608003982739 25681512101087412005974109)
      ·
        refine ⟨9630567037907779502240291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25681512101087412005974109 9630567037907779502240291)
        ·
          refine ⟨14445850556861669253360437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9630567037907779502240291 14445850556861669253360437)
          ·
            refine ⟨1354298489705781492502541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14445850556861669253360437 1354298489705781492502541)
            ·
              refine ⟨507861933639668059688453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1354298489705781492502541 507861933639668059688453)
              ·
                refine ⟨95224112557437761191585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 507861933639668059688453 95224112557437761191585)
                ·
                  rfl

theorem cell20_625888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_625888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625888 prefixEnd_625888 := by exact prefixLift 625888
  have htrace : WordTrace (prefixWord ++ tailWord_625888) baseStart_625888 baseEnd_625888 := by
    simpa [prefixWord, tailWord_625888, baseEnd_625888] using wordTrace_append hprefix tailTrace_625888
  have hstable : (prefixWord ++ tailWord_625888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625888).length < 2 ^ (prefixWord ++ tailWord_625888).sum := by decide
  have hdescent : baseEnd_625888 < baseStart_625888 := by decide
  rcases family_descends (prefixWord ++ tailWord_625888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625898 : List Nat := [3, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_625898 : Nat := 118140960795 + 625898 * 2 ^ 59
def prefixEnd_625898 : Nat := 4983230072969 + 3 ^ 40 * 625898 * 2
def baseEnd_625898 : Nat := 285676901944797693241381

theorem tailTrace_625898 : CollatzResearch.WordTrace tailWord_625898 prefixEnd_625898 285676901944797693241381 := by
  unfold tailWord_625898
  simp only [CollatzResearch.WordTrace]
  refine ⟨5707093871621478928293587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15218916990990610475449565 5707093871621478928293587)
  ·
    refine ⟨8560640807432218392440381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5707093871621478928293587 8560640807432218392440381)
    ·
      refine ⟨3210240302787081897165143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8560640807432218392440381 3210240302787081897165143)
      ·
        refine ⟨4815360454180622845747715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210240302787081897165143 4815360454180622845747715)
        ·
          refine ⟨7223040681270934268621573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4815360454180622845747715 7223040681270934268621573)
          ·
            refine ⟨1354320127738300175366545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7223040681270934268621573 1354320127738300175366545)
            ·
              refine ⟨1015740095803725131524909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354320127738300175366545 1015740095803725131524909)
              ·
                refine ⟨380902535926396924321841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1015740095803725131524909 380902535926396924321841)
                ·
                  refine ⟨285676901944797693241381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380902535926396924321841 285676901944797693241381)
                  ·
                    rfl

theorem cell20_625898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_625898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625898 prefixEnd_625898 := by exact prefixLift 625898
  have htrace : WordTrace (prefixWord ++ tailWord_625898) baseStart_625898 baseEnd_625898 := by
    simpa [prefixWord, tailWord_625898, baseEnd_625898] using wordTrace_append hprefix tailTrace_625898
  have hstable : (prefixWord ++ tailWord_625898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625898).length < 2 ^ (prefixWord ++ tailWord_625898).sum := by decide
  have hdescent : baseEnd_625898 < baseStart_625898 := by decide
  rcases family_descends (prefixWord ++ tailWord_625898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625908 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 5]
def baseStart_625908 : Nat := 118140960795 + 625908 * 2 ^ 59
def prefixEnd_625908 : Nat := 4983230072969 + 3 ^ 40 * 625908 * 2
def baseEnd_625908 : Nat := 285681466217282102908007

theorem tailTrace_625908 : CollatzResearch.WordTrace tailWord_625908 prefixEnd_625908 285681466217282102908007 := by
  unfold tailWord_625908
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414370108224843710519189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15219160144299791614025585 11414370108224843710519189)
  ·
    refine ⟨535048598823039548930587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11414370108224843710519189 535048598823039548930587)
    ·
      refine ⟨802572898234559323395881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535048598823039548930587 802572898234559323395881)
      ·
        refine ⟨601929673675919492546911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 802572898234559323395881 601929673675919492546911)
        ·
          refine ⟨902894510513879238820367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601929673675919492546911 902894510513879238820367)
          ·
            refine ⟨1354341765770818858230551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902894510513879238820367 1354341765770818858230551)
            ·
              refine ⟨2031512648656228287345827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354341765770818858230551 2031512648656228287345827)
              ·
                refine ⟨3047268972984342431018741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031512648656228287345827 3047268972984342431018741)
                ·
                  refine ⟨285681466217282102908007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3047268972984342431018741 285681466217282102908007)
                  ·
                    rfl

theorem cell20_625908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_625908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625908 prefixEnd_625908 := by exact prefixLift 625908
  have htrace : WordTrace (prefixWord ++ tailWord_625908) baseStart_625908 baseEnd_625908 := by
    simpa [prefixWord, tailWord_625908, baseEnd_625908] using wordTrace_append hprefix tailTrace_625908
  have hstable : (prefixWord ++ tailWord_625908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625908).length < 2 ^ (prefixWord ++ tailWord_625908).sum := by decide
  have hdescent : baseEnd_625908 < baseStart_625908 := by decide
  rcases family_descends (prefixWord ++ tailWord_625908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625919 : List Nat := [1, 1, 2, 2, 1, 5, 2, 4, 2]
def baseStart_625919 : Nat := 118140960795 + 625919 * 2 ^ 59
def prefixEnd_625919 : Nat := 4983230072969 + 3 ^ 40 * 625919 * 2
def baseEnd_625919 : Nat := 285686486917014953541295

theorem tailTrace_625919 : CollatzResearch.WordTrace tailWord_625919 prefixEnd_625919 285686486917014953541295 := by
  unfold tailWord_625919
  simp only [CollatzResearch.WordTrace]
  refine ⟨22829141419409836299688811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15219427612939890866459207 22829141419409836299688811)
  ·
    refine ⟨34243712129114754449533217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22829141419409836299688811 34243712129114754449533217)
    ·
      refine ⟨25682784096836065837149913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34243712129114754449533217 25682784096836065837149913)
      ·
        refine ⟨19262088072627049377862435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25682784096836065837149913 19262088072627049377862435)
        ·
          refine ⟨28893132108940574066793653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19262088072627049377862435 28893132108940574066793653)
          ·
            refine ⟨2708731135213178818761905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28893132108940574066793653 2708731135213178818761905)
            ·
              refine ⟨2031548351409884114071429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708731135213178818761905 2031548351409884114071429)
              ·
                refine ⟨380915315889353271388393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2031548351409884114071429 380915315889353271388393)
                ·
                  refine ⟨285686486917014953541295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380915315889353271388393 285686486917014953541295)
                  ·
                    rfl

theorem cell20_625919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 2].length) (baseStart_625919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625919 prefixEnd_625919 := by exact prefixLift 625919
  have htrace : WordTrace (prefixWord ++ tailWord_625919) baseStart_625919 baseEnd_625919 := by
    simpa [prefixWord, tailWord_625919, baseEnd_625919] using wordTrace_append hprefix tailTrace_625919
  have hstable : (prefixWord ++ tailWord_625919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625919).length < 2 ^ (prefixWord ++ tailWord_625919).sum := by decide
  have hdescent : baseEnd_625919 < baseStart_625919 := by decide
  rcases family_descends (prefixWord ++ tailWord_625919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625981 : List Nat := [1, 4, 1, 5, 1, 1, 2, 5]
def baseStart_625981 : Nat := 118140960795 + 625981 * 2 ^ 59
def prefixEnd_625981 : Nat := 4983230072969 + 3 ^ 40 * 625981 * 2
def baseEnd_625981 : Nat := 95238261802139431158125

theorem tailTrace_625981 : CollatzResearch.WordTrace tailWord_625981 prefixEnd_625981 95238261802139431158125 := by
  unfold tailWord_625981
  simp only [CollatzResearch.WordTrace]
  refine ⟨22831402745185220888445797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15220935163456813925630531 22831402745185220888445797)
  ·
    refine ⟨4280888014722228916583587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22831402745185220888445797 4280888014722228916583587)
    ·
      refine ⟨6421332022083343374875381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4280888014722228916583587 6421332022083343374875381)
      ·
        refine ⟨601999877070313441394567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6421332022083343374875381 601999877070313441394567)
        ·
          refine ⟨902999815605470162091851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601999877070313441394567 902999815605470162091851)
          ·
            refine ⟨1354499723408205243137777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902999815605470162091851 1354499723408205243137777)
            ·
              refine ⟨1015874792556153932353333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354499723408205243137777 1015874792556153932353333)
              ·
                refine ⟨95238261802139431158125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1015874792556153932353333 95238261802139431158125)
                ·
                  rfl

theorem cell20_625981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 5].length) (baseStart_625981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_625981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_625981 prefixEnd_625981 := by exact prefixLift 625981
  have htrace : WordTrace (prefixWord ++ tailWord_625981) baseStart_625981 baseEnd_625981 := by
    simpa [prefixWord, tailWord_625981, baseEnd_625981] using wordTrace_append hprefix tailTrace_625981
  have hstable : (prefixWord ++ tailWord_625981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625981).length < 2 ^ (prefixWord ++ tailWord_625981).sum := by decide
  have hdescent : baseEnd_625981 < baseStart_625981 := by decide
  rcases family_descends (prefixWord ++ tailWord_625981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626023 : List Nat := [1, 1, 5, 1, 4, 8]
def baseStart_626023 : Nat := 118140960795 + 626023 * 2 ^ 59
def prefixEnd_626023 : Nat := 4983230072969 + 3 ^ 40 * 626023 * 2
def baseEnd_626023 : Nat := 10582739087068622743489

theorem tailTrace_626023 : CollatzResearch.WordTrace tailWord_626023 prefixEnd_626023 10582739087068622743489 := by
  unfold tailWord_626023
  simp only [CollatzResearch.WordTrace]
  refine ⟨22832934611033062061474723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15221956407355374707649815 22832934611033062061474723)
  ·
    refine ⟨34249401916549593092212085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22832934611033062061474723 34249401916549593092212085)
    ·
      refine ⟨3210881429676524352394883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34249401916549593092212085 3210881429676524352394883)
      ·
        refine ⟨4816322144514786528592325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210881429676524352394883 4816322144514786528592325)
        ·
          refine ⟨903060402096522474111061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4816322144514786528592325 903060402096522474111061)
          ·
            refine ⟨10582739087068622743489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 903060402096522474111061 10582739087068622743489)
            ·
              rfl

theorem cell20_626023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 8].length) (baseStart_626023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626023 prefixEnd_626023 := by exact prefixLift 626023
  have htrace : WordTrace (prefixWord ++ tailWord_626023) baseStart_626023 baseEnd_626023 := by
    simpa [prefixWord, tailWord_626023, baseEnd_626023] using wordTrace_append hprefix tailTrace_626023
  have hstable : (prefixWord ++ tailWord_626023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626023).length < 2 ^ (prefixWord ++ tailWord_626023).sum := by decide
  have hdescent : baseEnd_626023 < baseStart_626023 := by decide
  rcases family_descends (prefixWord ++ tailWord_626023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626029 : List Nat := [1, 5, 1, 1, 1, 5, 2, 2, 2]
def baseStart_626029 : Nat := 118140960795 + 626029 * 2 ^ 59
def prefixEnd_626029 : Nat := 4983230072969 + 3 ^ 40 * 626029 * 2
def baseEnd_626029 : Nat := 285736693914343459874179

theorem tailTrace_626029 : CollatzResearch.WordTrace tailWord_626029 prefixEnd_626029 285736693914343459874179 := by
  unfold tailWord_626029
  simp only [CollatzResearch.WordTrace]
  refine ⟨22833153449011325086193141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15222102299340883390795427 22833153449011325086193141)
  ·
    refine ⟨2140608135844811726830607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22833153449011325086193141 2140608135844811726830607)
    ·
      refine ⟨3210912203767217590245911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2140608135844811726830607 3210912203767217590245911)
      ·
        refine ⟨4816368305650826385368867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210912203767217590245911 4816368305650826385368867)
        ·
          refine ⟨7224552458476239578053301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4816368305650826385368867 7224552458476239578053301)
          ·
            refine ⟨677301792982147460442497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7224552458476239578053301 677301792982147460442497)
            ·
              refine ⟨507976344736610595331873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677301792982147460442497 507976344736610595331873)
              ·
                refine ⟨380982258552457946498905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507976344736610595331873 380982258552457946498905)
                ·
                  refine ⟨285736693914343459874179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380982258552457946498905 285736693914343459874179)
                  ·
                    rfl

theorem cell20_626029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_626029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626029 prefixEnd_626029 := by exact prefixLift 626029
  have htrace : WordTrace (prefixWord ++ tailWord_626029) baseStart_626029 baseEnd_626029 := by
    simpa [prefixWord, tailWord_626029, baseEnd_626029] using wordTrace_append hprefix tailTrace_626029
  have hstable : (prefixWord ++ tailWord_626029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626029).length < 2 ^ (prefixWord ++ tailWord_626029).sum := by decide
  have hdescent : baseEnd_626029 < baseStart_626029 := by decide
  rcases family_descends (prefixWord ++ tailWord_626029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626050 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_626050 : Nat := 118140960795 + 626050 * 2 ^ 59
def prefixEnd_626050 : Nat := 4983230072969 + 3 ^ 40 * 626050 * 2
def baseEnd_626050 : Nat := 285746278886560720174093

theorem tailTrace_626050 : CollatzResearch.WordTrace tailWord_626050 prefixEnd_626050 285746278886560720174093 := by
  unfold tailWord_626050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708479845483811418176901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15222612921290163781805069 5708479845483811418176901)
  ·
    refine ⟨1070339971028214640908169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5708479845483811418176901 1070339971028214640908169)
    ·
      refine ⟨802754978271160980681127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1070339971028214640908169 802754978271160980681127)
      ·
        refine ⟨1204132467406741471021691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802754978271160980681127 1204132467406741471021691)
        ·
          refine ⟨1806198701110112206532537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204132467406741471021691 1806198701110112206532537)
          ·
            refine ⟨1354649025832584154899403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1806198701110112206532537 1354649025832584154899403)
            ·
              refine ⟨2031973538748876232349105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354649025832584154899403 2031973538748876232349105)
              ·
                refine ⟨1523980154061657174261829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031973538748876232349105 1523980154061657174261829)
                ·
                  refine ⟨285746278886560720174093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523980154061657174261829 285746278886560720174093)
                  ·
                    rfl

theorem cell20_626050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_626050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626050 prefixEnd_626050 := by exact prefixLift 626050
  have htrace : WordTrace (prefixWord ++ tailWord_626050) baseStart_626050 baseEnd_626050 := by
    simpa [prefixWord, tailWord_626050, baseEnd_626050] using wordTrace_append hprefix tailTrace_626050
  have hstable : (prefixWord ++ tailWord_626050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626050).length < 2 ^ (prefixWord ++ tailWord_626050).sum := by decide
  have hdescent : baseEnd_626050 < baseStart_626050 := by decide
  rcases family_descends (prefixWord ++ tailWord_626050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626088 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_626088 : Nat := 118140960795 + 626088 * 2 ^ 59
def prefixEnd_626088 : Nat := 4983230072969 + 3 ^ 40 * 626088 * 2
def baseEnd_626088 : Nat := 285763623122001476907271

theorem tailTrace_626088 : CollatzResearch.WordTrace tailWord_626088 prefixEnd_626088 285763623122001476907271 := by
  unfold tailWord_626088
  simp only [CollatzResearch.WordTrace]
  refine ⟨11417652677898789081295459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15223536903865052108393945 11417652677898789081295459)
  ·
    refine ⟨17126479016848183621943189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11417652677898789081295459 17126479016848183621943189)
    ·
      refine ⟨802803703914758607278587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17126479016848183621943189 802803703914758607278587)
      ·
        refine ⟨1204205555872137910917881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802803703914758607278587 1204205555872137910917881)
        ·
          refine ⟨903154166904103433188411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204205555872137910917881 903154166904103433188411)
          ·
            refine ⟨1354731250356155149782617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903154166904103433188411 1354731250356155149782617)
            ·
              refine ⟨1016048437767116362336963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354731250356155149782617 1016048437767116362336963)
              ·
                refine ⟨1524072656650674543505445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016048437767116362336963 1524072656650674543505445)
                ·
                  refine ⟨285763623122001476907271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1524072656650674543505445 285763623122001476907271)
                  ·
                    rfl

theorem cell20_626088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_626088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626088 prefixEnd_626088 := by exact prefixLift 626088
  have htrace : WordTrace (prefixWord ++ tailWord_626088) baseStart_626088 baseEnd_626088 := by
    simpa [prefixWord, tailWord_626088, baseEnd_626088] using wordTrace_append hprefix tailTrace_626088
  have hstable : (prefixWord ++ tailWord_626088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626088).length < 2 ^ (prefixWord ++ tailWord_626088).sum := by decide
  have hdescent : baseEnd_626088 < baseStart_626088 := by decide
  rcases family_descends (prefixWord ++ tailWord_626088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626116 : List Nat := [2, 3, 3, 2, 1, 2, 1, 6]
def baseStart_626116 : Nat := 118140960795 + 626116 * 2 ^ 59
def prefixEnd_626116 : Nat := 4983230072969 + 3 ^ 40 * 626116 * 2
def baseEnd_626116 : Nat := 95258801028319274657941

theorem tailTrace_626116 : CollatzResearch.WordTrace tailWord_626116 prefixEnd_626116 95258801028319274657941 := by
  unfold tailWord_626116
  simp only [CollatzResearch.WordTrace]
  refine ⟨11418163299848069472305101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15224217733130759296406801 11418163299848069472305101)
  ·
    refine ⟨4281811237443026052114413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11418163299848069472305101 4281811237443026052114413)
    ·
      refine ⟨1605679214041134769542905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4281811237443026052114413 1605679214041134769542905)
      ·
        refine ⟨1204259410530851077157179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1605679214041134769542905 1204259410530851077157179)
        ·
          refine ⟨1806389115796276615735769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204259410530851077157179 1806389115796276615735769)
          ·
            refine ⟨1354791836847207461801827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1806389115796276615735769 1354791836847207461801827)
            ·
              refine ⟨2032187755270811192702741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354791836847207461801827 2032187755270811192702741)
              ·
                refine ⟨95258801028319274657941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2032187755270811192702741 95258801028319274657941)
                ·
                  rfl

theorem cell20_626116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_626116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626116 prefixEnd_626116 := by exact prefixLift 626116
  have htrace : WordTrace (prefixWord ++ tailWord_626116) baseStart_626116 baseEnd_626116 := by
    simpa [prefixWord, tailWord_626116, baseEnd_626116] using wordTrace_append hprefix tailTrace_626116
  have hstable : (prefixWord ++ tailWord_626116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626116).length < 2 ^ (prefixWord ++ tailWord_626116).sum := by decide
  have hdescent : baseEnd_626116 < baseStart_626116 := by decide
  rcases family_descends (prefixWord ++ tailWord_626116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626137 : List Nat := [1, 2, 1, 2, 4, 4, 6]
def baseStart_626137 : Nat := 118140960795 + 626137 * 2 ^ 59
def prefixEnd_626137 : Nat := 4983230072969 + 3 ^ 40 * 626137 * 2
def baseEnd_626137 : Nat := 31753998673019453808193

theorem tailTrace_626137 : CollatzResearch.WordTrace tailWord_626137 prefixEnd_626137 31753998673019453808193 := by
  unfold tailWord_626137
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837092532620059531124665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15224728355080039687416443 22837092532620059531124665)
  ·
    refine ⟨17127819399465044648343499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22837092532620059531124665 17127819399465044648343499)
    ·
      refine ⟨25691729099197566972515249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17127819399465044648343499 25691729099197566972515249)
      ·
        refine ⟨19268796824398175229386437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25691729099197566972515249 19268796824398175229386437)
        ·
          refine ⟨3612899404574657855509957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19268796824398175229386437 3612899404574657855509957)
          ·
            refine ⟨677418638357748347908117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3612899404574657855509957 677418638357748347908117)
            ·
              refine ⟨31753998673019453808193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 677418638357748347908117 31753998673019453808193)
              ·
                rfl

theorem cell20_626137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 6].length) (baseStart_626137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626137 prefixEnd_626137 := by exact prefixLift 626137
  have htrace : WordTrace (prefixWord ++ tailWord_626137) baseStart_626137 baseEnd_626137 := by
    simpa [prefixWord, tailWord_626137, baseEnd_626137] using wordTrace_append hprefix tailTrace_626137
  have hstable : (prefixWord ++ tailWord_626137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626137).length < 2 ^ (prefixWord ++ tailWord_626137).sum := by decide
  have hdescent : baseEnd_626137 < baseStart_626137 := by decide
  rcases family_descends (prefixWord ++ tailWord_626137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626147 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 4]
def baseStart_626147 : Nat := 118140960795 + 626147 * 2 ^ 59
def prefixEnd_626147 : Nat := 4983230072969 + 3 ^ 40 * 626147 * 2
def baseEnd_626147 : Nat := 285790552329659493940363

theorem tailTrace_626147 : CollatzResearch.WordTrace tailWord_626147 prefixEnd_626147 285790552329659493940363 := by
  unfold tailWord_626147
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837457262583831238988695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15224971508389220825992463 22837457262583831238988695)
  ·
    refine ⟨34256185893875746858483043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22837457262583831238988695 34256185893875746858483043)
    ·
      refine ⟨51384278840813620287724565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34256185893875746858483043 51384278840813620287724565)
      ·
        refine ⟨2408638070663138450987089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51384278840813620287724565 2408638070663138450987089)
        ·
          refine ⟨1806478552997353838240317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2408638070663138450987089 1806478552997353838240317)
          ·
            refine ⟨677429457374007689340119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1806478552997353838240317 677429457374007689340119)
            ·
              refine ⟨1016144186061011534010179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677429457374007689340119 1016144186061011534010179)
              ·
                refine ⟨1524216279091517301015269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016144186061011534010179 1524216279091517301015269)
                ·
                  refine ⟨285790552329659493940363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1524216279091517301015269 285790552329659493940363)
                  ·
                    rfl

theorem cell20_626147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 4].length) (baseStart_626147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626147 prefixEnd_626147 := by exact prefixLift 626147
  have htrace : WordTrace (prefixWord ++ tailWord_626147) baseStart_626147 baseEnd_626147 := by
    simpa [prefixWord, tailWord_626147, baseEnd_626147] using wordTrace_append hprefix tailTrace_626147
  have hstable : (prefixWord ++ tailWord_626147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626147).length < 2 ^ (prefixWord ++ tailWord_626147).sum := by decide
  have hdescent : baseEnd_626147 < baseStart_626147 := by decide
  rcases family_descends (prefixWord ++ tailWord_626147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626154 : List Nat := [3, 1, 3, 1, 4, 1, 2, 5]
def baseStart_626154 : Nat := 118140960795 + 626154 * 2 ^ 59
def prefixEnd_626154 : Nat := 4983230072969 + 3 ^ 40 * 626154 * 2
def baseEnd_626154 : Nat := 95264582440132860235667

theorem tailTrace_626154 : CollatzResearch.WordTrace tailWord_626154 prefixEnd_626154 95264582440132860235667 := by
  unfold tailWord_626154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709428143389617858623379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15225141715705647622995677 5709428143389617858623379)
  ·
    refine ⟨8564142215084426787935069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5709428143389617858623379 8564142215084426787935069)
    ·
      refine ⟨3211553330656660045475651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8564142215084426787935069 3211553330656660045475651)
      ·
        refine ⟨4817329995984990068213477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3211553330656660045475651 4817329995984990068213477)
        ·
          refine ⟨903249374247185637790027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4817329995984990068213477 903249374247185637790027)
          ·
            refine ⟨1354874061370778456685041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903249374247185637790027 1354874061370778456685041)
            ·
              refine ⟨1016155546028083842513781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354874061370778456685041 1016155546028083842513781)
              ·
                refine ⟨95264582440132860235667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1016155546028083842513781 95264582440132860235667)
                ·
                  rfl

theorem cell20_626154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_626154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626154 prefixEnd_626154 := by exact prefixLift 626154
  have htrace : WordTrace (prefixWord ++ tailWord_626154) baseStart_626154 baseEnd_626154 := by
    simpa [prefixWord, tailWord_626154, baseEnd_626154] using wordTrace_append hprefix tailTrace_626154
  have hstable : (prefixWord ++ tailWord_626154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626154).length < 2 ^ (prefixWord ++ tailWord_626154).sum := by decide
  have hdescent : baseEnd_626154 < baseStart_626154 := by decide
  rcases family_descends (prefixWord ++ tailWord_626154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626161 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 3]
def baseStart_626161 : Nat := 118140960795 + 626161 * 2 ^ 59
def prefixEnd_626161 : Nat := 4983230072969 + 3 ^ 40 * 626161 * 2
def baseEnd_626161 : Nat := 285796942311137667473639

theorem tailTrace_626161 : CollatzResearch.WordTrace tailWord_626161 prefixEnd_626161 285796942311137667473639 := by
  unfold tailWord_626161
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837967884533111629998337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15225311923022074419998891 22837967884533111629998337)
  ·
    refine ⟨17128475913399833722498753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22837967884533111629998337 17128475913399833722498753)
    ·
      refine ⟨12846356935049875291874065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17128475913399833722498753 12846356935049875291874065)
      ·
        refine ⟨9634767701287406468905549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12846356935049875291874065 9634767701287406468905549)
        ·
          refine ⟨3613037887982777425839581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9634767701287406468905549 3613037887982777425839581)
          ·
            refine ⟨1354889207993541534689843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3613037887982777425839581 1354889207993541534689843)
            ·
              refine ⟨2032333811990312302034765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354889207993541534689843 2032333811990312302034765)
              ·
                refine ⟨762125179496367113263037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2032333811990312302034765 762125179496367113263037)
                ·
                  refine ⟨285796942311137667473639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762125179496367113263037 285796942311137667473639)
                  ·
                    rfl

theorem cell20_626161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_626161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626161 prefixEnd_626161 := by exact prefixLift 626161
  have htrace : WordTrace (prefixWord ++ tailWord_626161) baseStart_626161 baseEnd_626161 := by
    simpa [prefixWord, tailWord_626161, baseEnd_626161] using wordTrace_append hprefix tailTrace_626161
  have hstable : (prefixWord ++ tailWord_626161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626161).length < 2 ^ (prefixWord ++ tailWord_626161).sum := by decide
  have hdescent : baseEnd_626161 < baseStart_626161 := by decide
  rcases family_descends (prefixWord ++ tailWord_626161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626227 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_626227 : Nat := 118140960795 + 626227 * 2 ^ 59
def prefixEnd_626227 : Nat := 4983230072969 + 3 ^ 40 * 626227 * 2
def baseEnd_626227 : Nat := 285827066509534771273369

theorem tailTrace_626227 : CollatzResearch.WordTrace tailWord_626227 prefixEnd_626227 285827066509534771273369 := by
  unfold tailWord_626227
  simp only [CollatzResearch.WordTrace]
  refine ⟨22840375102294004901900935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15226916734862669934600623 22840375102294004901900935)
  ·
    refine ⟨34260562653441007352851403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22840375102294004901900935 34260562653441007352851403)
    ·
      refine ⟨51390843980161511029277105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34260562653441007352851403 51390843980161511029277105)
      ·
        refine ⟨38543132985121133271957829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51390843980161511029277105 38543132985121133271957829)
        ·
          refine ⟨7226837434710212488492093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38543132985121133271957829 7226837434710212488492093)
          ·
            refine ⟨2710064038016329683184535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7226837434710212488492093 2710064038016329683184535)
            ·
              refine ⟨4065096057024494524776803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710064038016329683184535 4065096057024494524776803)
              ·
                refine ⟨6097644085536741787165205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4065096057024494524776803 6097644085536741787165205)
                ·
                  refine ⟨285827066509534771273369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6097644085536741787165205 285827066509534771273369)
                  ·
                    rfl

theorem cell20_626227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_626227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626227 prefixEnd_626227 := by exact prefixLift 626227
  have htrace : WordTrace (prefixWord ++ tailWord_626227) baseStart_626227 baseEnd_626227 := by
    simpa [prefixWord, tailWord_626227, baseEnd_626227] using wordTrace_append hprefix tailTrace_626227
  have hstable : (prefixWord ++ tailWord_626227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626227).length < 2 ^ (prefixWord ++ tailWord_626227).sum := by decide
  have hdescent : baseEnd_626227 < baseStart_626227 := by decide
  rcases family_descends (prefixWord ++ tailWord_626227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626272 : List Nat := [2, 1, 1, 3, 2, 1, 1, 9]
def baseStart_626272 : Nat := 118140960795 + 626272 * 2 ^ 59
def prefixEnd_626272 : Nat := 4983230072969 + 3 ^ 40 * 626272 * 2
def baseEnd_626272 : Nat := 95282535245238204924395

theorem tailTrace_626272 : CollatzResearch.WordTrace tailWord_626272 prefixEnd_626272 95282535245238204924395 := by
  unfold tailWord_626272
  simp only [CollatzResearch.WordTrace]
  refine ⟨11421008193565488793644535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15228010924753985058192713 11421008193565488793644535)
  ·
    refine ⟨17131512290348233190466803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11421008193565488793644535 17131512290348233190466803)
    ·
      refine ⟨25697268435522349785700205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17131512290348233190466803 25697268435522349785700205)
      ·
        refine ⟨9636475663320881169637577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25697268435522349785700205 9636475663320881169637577)
        ·
          refine ⟨7227356747490660877228183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9636475663320881169637577 7227356747490660877228183)
          ·
            refine ⟨10841035121235991315842275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7227356747490660877228183 10841035121235991315842275)
            ·
              refine ⟨16261552681853986973763413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10841035121235991315842275 16261552681853986973763413)
              ·
                refine ⟨95282535245238204924395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16261552681853986973763413 95282535245238204924395)
                ·
                  rfl

theorem cell20_626272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_626272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626272 prefixEnd_626272 := by exact prefixLift 626272
  have htrace : WordTrace (prefixWord ++ tailWord_626272) baseStart_626272 baseEnd_626272 := by
    simpa [prefixWord, tailWord_626272, baseEnd_626272] using wordTrace_append hprefix tailTrace_626272
  have hstable : (prefixWord ++ tailWord_626272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626272).length < 2 ^ (prefixWord ++ tailWord_626272).sum := by decide
  have hdescent : baseEnd_626272 < baseStart_626272 := by decide
  rcases family_descends (prefixWord ++ tailWord_626272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626282 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_626282 : Nat := 118140960795 + 626282 * 2 ^ 59
def prefixEnd_626282 : Nat := 4983230072969 + 3 ^ 40 * 626282 * 2
def baseEnd_626282 : Nat := 285852170008199024439811

theorem tailTrace_626282 : CollatzResearch.WordTrace tailWord_626282 prefixEnd_626282 285852170008199024439811 := by
  unfold tailWord_626282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5710595279273687323788275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15228254078063166196768733 5710595279273687323788275)
  ·
    refine ⟨8565892918910530985682413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5710595279273687323788275 8565892918910530985682413)
    ·
      refine ⟨3212209844591449119630905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8565892918910530985682413 3212209844591449119630905)
      ·
        refine ⟨2409157383443586839723179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3212209844591449119630905 2409157383443586839723179)
        ·
          refine ⟨3613736075165380259584769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409157383443586839723179 3613736075165380259584769)
          ·
            refine ⟨2710302056374035194688577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3613736075165380259584769 2710302056374035194688577)
            ·
              refine ⟨2032726542280526396016433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2710302056374035194688577 2032726542280526396016433)
              ·
                refine ⟨1524544906710394797012325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2032726542280526396016433 1524544906710394797012325)
                ·
                  refine ⟨285852170008199024439811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1524544906710394797012325 285852170008199024439811)
                  ·
                    rfl

theorem cell20_626282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_626282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626282 prefixEnd_626282 := by exact prefixLift 626282
  have htrace : WordTrace (prefixWord ++ tailWord_626282) baseStart_626282 baseEnd_626282 := by
    simpa [prefixWord, tailWord_626282, baseEnd_626282] using wordTrace_append hprefix tailTrace_626282
  have hstable : (prefixWord ++ tailWord_626282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626282).length < 2 ^ (prefixWord ++ tailWord_626282).sum := by decide
  have hdescent : baseEnd_626282 < baseStart_626282 := by decide
  rcases family_descends (prefixWord ++ tailWord_626282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626285 : List Nat := [1, 5, 1, 1, 4, 2, 2, 4]
def baseStart_626285 : Nat := 118140960795 + 626285 * 2 ^ 59
def prefixEnd_626285 : Nat := 4983230072969 + 3 ^ 40 * 626285 * 2
def baseEnd_626285 : Nat := 95284513096648115779933

theorem tailTrace_626285 : CollatzResearch.WordTrace tailWord_626285 prefixEnd_626285 95284513096648115779933 := by
  unfold tailWord_626285
  simp only [CollatzResearch.WordTrace]
  refine ⟨22842490536083880807512309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15228327024055920538341539 22842490536083880807512309)
  ·
    refine ⟨2141483487757863825704279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22842490536083880807512309 2141483487757863825704279)
    ·
      refine ⟨3212225231636795738556419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2141483487757863825704279 3212225231636795738556419)
      ·
        refine ⟨4818337847455193607834629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3212225231636795738556419 4818337847455193607834629)
        ·
          refine ⟨903438346397848801468993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4818337847455193607834629 903438346397848801468993)
          ·
            refine ⟨677578759798386601101745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903438346397848801468993 677578759798386601101745)
            ·
              refine ⟨508184069848789950826309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677578759798386601101745 508184069848789950826309)
              ·
                refine ⟨95284513096648115779933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 508184069848789950826309 95284513096648115779933)
                ·
                  rfl

theorem cell20_626285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 4].length) (baseStart_626285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626285 prefixEnd_626285 := by exact prefixLift 626285
  have htrace : WordTrace (prefixWord ++ tailWord_626285) baseStart_626285 baseEnd_626285 := by
    simpa [prefixWord, tailWord_626285, baseEnd_626285] using wordTrace_append hprefix tailTrace_626285
  have hstable : (prefixWord ++ tailWord_626285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626285).length < 2 ^ (prefixWord ++ tailWord_626285).sum := by decide
  have hdescent : baseEnd_626285 < baseStart_626285 := by decide
  rcases family_descends (prefixWord ++ tailWord_626285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626320 : List Nat := [2, 1, 1, 1, 1, 1, 3, 8, 2]
def baseStart_626320 : Nat := 118140960795 + 626320 * 2 ^ 59
def prefixEnd_626320 : Nat := 4983230072969 + 3 ^ 40 * 626320 * 2
def baseEnd_626320 : Nat := 285869514243639781172989

theorem tailTrace_626320 : CollatzResearch.WordTrace tailWord_626320 prefixEnd_626320 285869514243639781172989 := by
  unfold tailWord_626320
  simp only [CollatzResearch.WordTrace]
  refine ⟨11421883545478540892518207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15229178060638054523357609 11421883545478540892518207)
  ·
    refine ⟨17132825318217811338777311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11421883545478540892518207 17132825318217811338777311)
    ·
      refine ⟨25699237977326717008165967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17132825318217811338777311 25699237977326717008165967)
      ·
        refine ⟨38548856965990075512248951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25699237977326717008165967 38548856965990075512248951)
        ·
          refine ⟨57823285448985113268373427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38548856965990075512248951 57823285448985113268373427)
          ·
            refine ⟨86734928173477669902560141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57823285448985113268373427 86734928173477669902560141)
            ·
              refine ⟨32525598065054126213460053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86734928173477669902560141 32525598065054126213460053)
              ·
                refine ⟨381159352324853041563985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 32525598065054126213460053 381159352324853041563985)
                ·
                  refine ⟨285869514243639781172989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381159352324853041563985 285869514243639781172989)
                  ·
                    rfl

theorem cell20_626320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_626320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626320 prefixEnd_626320 := by exact prefixLift 626320
  have htrace : WordTrace (prefixWord ++ tailWord_626320) baseStart_626320 baseEnd_626320 := by
    simpa [prefixWord, tailWord_626320, baseEnd_626320] using wordTrace_append hprefix tailTrace_626320
  have hstable : (prefixWord ++ tailWord_626320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626320).length < 2 ^ (prefixWord ++ tailWord_626320).sum := by decide
  have hdescent : baseEnd_626320 < baseStart_626320 := by decide
  rcases family_descends (prefixWord ++ tailWord_626320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626327 : List Nat := [1, 1, 3, 3, 2, 3, 2, 5]
def baseStart_626327 : Nat := 118140960795 + 626327 * 2 ^ 59
def prefixEnd_626327 : Nat := 4983230072969 + 3 ^ 40 * 626327 * 2
def baseEnd_626327 : Nat := 95290903078126289313209

theorem tailTrace_626327 : CollatzResearch.WordTrace tailWord_626327 prefixEnd_626327 95290903078126289313209 := by
  unfold tailWord_626327
  simp only [CollatzResearch.WordTrace]
  refine ⟨22844022401931721980541235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15229348267954481320360823 22844022401931721980541235)
  ·
    refine ⟨34266033602897582970811853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22844022401931721980541235 34266033602897582970811853)
    ·
      refine ⟨12849762601086593614054445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34266033602897582970811853 12849762601086593614054445)
      ·
        refine ⟨4818660975407472605270417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12849762601086593614054445 4818660975407472605270417)
        ·
          refine ⟨3613995731555604453952813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4818660975407472605270417 3613995731555604453952813)
          ·
            refine ⟨1355248399333351670232305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3613995731555604453952813 1355248399333351670232305)
            ·
              refine ⟨1016436299500013752674229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1355248399333351670232305 1016436299500013752674229)
              ·
                refine ⟨95290903078126289313209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1016436299500013752674229 95290903078126289313209)
                ·
                  rfl

theorem cell20_626327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_626327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626327 prefixEnd_626327 := by exact prefixLift 626327
  have htrace : WordTrace (prefixWord ++ tailWord_626327) baseStart_626327 baseEnd_626327 := by
    simpa [prefixWord, tailWord_626327, baseEnd_626327] using wordTrace_append hprefix tailTrace_626327
  have hstable : (prefixWord ++ tailWord_626327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626327).length < 2 ^ (prefixWord ++ tailWord_626327).sum := by decide
  have hdescent : baseEnd_626327 < baseStart_626327 := by decide
  rcases family_descends (prefixWord ++ tailWord_626327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626341 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_626341 : Nat := 118140960795 + 626341 * 2 ^ 59
def prefixEnd_626341 : Nat := 4983230072969 + 3 ^ 40 * 626341 * 2
def baseEnd_626341 : Nat := 285879099215857041472903

theorem tailTrace_626341 : CollatzResearch.WordTrace tailWord_626341 prefixEnd_626341 285879099215857041472903 := by
  unfold tailWord_626341
  simp only [CollatzResearch.WordTrace]
  refine ⟨22844533023881002371550877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15229688682587334914367251 22844533023881002371550877)
  ·
    refine ⟨8566699883955375889331579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22844533023881002371550877 8566699883955375889331579)
    ·
      refine ⟨12850049825933063833997369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8566699883955375889331579 12850049825933063833997369)
      ·
        refine ⟨9637537369449797875498027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12850049825933063833997369 9637537369449797875498027)
        ·
          refine ⟨14456306054174696813247041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9637537369449797875498027 14456306054174696813247041)
          ·
            refine ⟨10842229540631022609935281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14456306054174696813247041 10842229540631022609935281)
            ·
              refine ⟨8131672155473266957451461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10842229540631022609935281 8131672155473266957451461)
              ·
                refine ⟨1524688529151237554522149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8131672155473266957451461 1524688529151237554522149)
                ·
                  refine ⟨285879099215857041472903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1524688529151237554522149 285879099215857041472903)
                  ·
                    rfl

theorem cell20_626341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_626341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626341 prefixEnd_626341 := by exact prefixLift 626341
  have htrace : WordTrace (prefixWord ++ tailWord_626341) baseStart_626341 baseEnd_626341 := by
    simpa [prefixWord, tailWord_626341, baseEnd_626341] using wordTrace_append hprefix tailTrace_626341
  have hstable : (prefixWord ++ tailWord_626341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626341).length < 2 ^ (prefixWord ++ tailWord_626341).sum := by decide
  have hdescent : baseEnd_626341 < baseStart_626341 := by decide
  rcases family_descends (prefixWord ++ tailWord_626341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626413 : List Nat := [1, 5, 1, 2, 1, 2, 1, 5, 2]
def baseStart_626413 : Nat := 118140960795 + 626413 * 2 ^ 59
def prefixEnd_626413 : Nat := 4983230072969 + 3 ^ 40 * 626413 * 2
def baseEnd_626413 : Nat := 285911961977744791072609

theorem tailTrace_626413 : CollatzResearch.WordTrace tailWord_626413 prefixEnd_626413 285911961977744791072609 := by
  unfold tailWord_626413
  simp only [CollatzResearch.WordTrace]
  refine ⟨22847159079620158668171893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15231439386413439112114595 22847159079620158668171893)
  ·
    refine ⟨2141921163714389875141115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22847159079620158668171893 2141921163714389875141115)
    ·
      refine ⟨3212881745571584812711673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2141921163714389875141115 3212881745571584812711673)
      ·
        refine ⟨2409661309178688609533755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3212881745571584812711673 2409661309178688609533755)
        ·
          refine ⟨3614491963768032914300633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409661309178688609533755 3614491963768032914300633)
          ·
            refine ⟨2710868972826024685725475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3614491963768032914300633 2710868972826024685725475)
            ·
              refine ⟨4066303459239037028588213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710868972826024685725475 4066303459239037028588213)
              ·
                refine ⟨381215949303659721430145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4066303459239037028588213 381215949303659721430145)
                ·
                  refine ⟨285911961977744791072609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381215949303659721430145 285911961977744791072609)
                  ·
                    rfl

theorem cell20_626413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_626413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_626413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_626413 prefixEnd_626413 := by exact prefixLift 626413
  have htrace : WordTrace (prefixWord ++ tailWord_626413) baseStart_626413 baseEnd_626413 := by
    simpa [prefixWord, tailWord_626413, baseEnd_626413] using wordTrace_append hprefix tailTrace_626413
  have hstable : (prefixWord ++ tailWord_626413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626413).length < 2 ^ (prefixWord ++ tailWord_626413).sum := by decide
  have hdescent : baseEnd_626413 < baseStart_626413 := by decide
  rcases family_descends (prefixWord ++ tailWord_626413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
