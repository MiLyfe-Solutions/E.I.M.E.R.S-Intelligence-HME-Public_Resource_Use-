import V185TrunkScan22Chunk359

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3211895 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 3, 4]
def baseStart_3211895 : Nat := 118140960795 + 3211895 * 2 ^ 59
def prefixEnd_3211895 : Nat := 4983230072969 + 3 ^ 40 * 3211895 * 2
def baseEnd_3211895 : Nat := 1099497297848544119827513

theorem tailTrace_3211895 : CollatzResearch.WordTrace tailWord_3211895 prefixEnd_3211895 1099497297848544119827513 := by
  unfold tailWord_3211895
  simp only [CollatzResearch.WordTrace]
  refine ⟨117147434698860437838973139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78098289799240291892648759 117147434698860437838973139)
  ·
    refine ⟨175721152048290656758459709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117147434698860437838973139 175721152048290656758459709)
    ·
      refine ⟨65895432018108996284422391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175721152048290656758459709 65895432018108996284422391)
      ·
        refine ⟨98843148027163494426633587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65895432018108996284422391 98843148027163494426633587)
        ·
          refine ⟨148264722040745241639950381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98843148027163494426633587 148264722040745241639950381)
          ·
            refine ⟨55599270765279465614981393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148264722040745241639950381 55599270765279465614981393)
            ·
              refine ⟨41699453073959599211236045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55599270765279465614981393 41699453073959599211236045)
              ·
                refine ⟨15637294902734849704213517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41699453073959599211236045 15637294902734849704213517)
                ·
                  refine ⟨5863985588525568639080069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15637294902734849704213517 5863985588525568639080069)
                  ·
                    refine ⟨1099497297848544119827513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5863985588525568639080069 1099497297848544119827513)
                    ·
                      rfl

theorem cell22_3211895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_3211895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211895 prefixEnd_3211895 := by exact prefixLift 3211895
  have htrace : WordTrace (prefixWord ++ tailWord_3211895) baseStart_3211895 baseEnd_3211895 := by
    simpa [prefixWord, tailWord_3211895, baseEnd_3211895] using wordTrace_append hprefix tailTrace_3211895
  have hstable : (prefixWord ++ tailWord_3211895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211895).length < 2 ^ (prefixWord ++ tailWord_3211895).sum := by decide
  have hdescent : baseEnd_3211895 < baseStart_3211895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211946 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3211946 : Nat := 118140960795 + 3211946 * 2 ^ 59
def prefixEnd_3211946 : Nat := 4983230072969 + 3 ^ 40 * 3211946 * 2
def baseEnd_3211946 : Nat := 1099514756190796986802357

theorem tailTrace_3211946 : CollatzResearch.WordTrace tailWord_3211946 prefixEnd_3211946 1099514756190796986802357 := by
  unfold tailWord_3211946
  simp only [CollatzResearch.WordTrace]
  refine ⟨29287323705418918387269923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78099529881117115699386461 29287323705418918387269923)
  ·
    refine ⟨43930985558128377580904885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29287323705418918387269923 43930985558128377580904885)
    ·
      refine ⟨4118529896074535398209833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43930985558128377580904885 4118529896074535398209833)
      ·
        refine ⟨3088897422055901548657375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4118529896074535398209833 3088897422055901548657375)
        ·
          refine ⟨4633346133083852322986063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088897422055901548657375 4633346133083852322986063)
          ·
            refine ⟨6950019199625778484479095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633346133083852322986063 6950019199625778484479095)
            ·
              refine ⟨10425028799438667726718643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6950019199625778484479095 10425028799438667726718643)
              ·
                refine ⟨15637543199158001590077965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10425028799438667726718643 15637543199158001590077965)
                ·
                  refine ⟨5864078699684250596279237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15637543199158001590077965 5864078699684250596279237)
                  ·
                    refine ⟨1099514756190796986802357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5864078699684250596279237 1099514756190796986802357)
                    ·
                      rfl

theorem cell22_3211946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3211946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211946 prefixEnd_3211946 := by exact prefixLift 3211946
  have htrace : WordTrace (prefixWord ++ tailWord_3211946) baseStart_3211946 baseEnd_3211946 := by
    simpa [prefixWord, tailWord_3211946, baseEnd_3211946] using wordTrace_append hprefix tailTrace_3211946
  have hstable : (prefixWord ++ tailWord_3211946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211946).length < 2 ^ (prefixWord ++ tailWord_3211946).sum := by decide
  have hdescent : baseEnd_3211946 < baseStart_3211946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211955 : List Nat := [1, 1, 1, 2, 3, 4, 2, 8]
def baseStart_3211955 : Nat := 118140960795 + 3211955 * 2 ^ 59
def prefixEnd_3211955 : Nat := 4983230072969 + 3 ^ 40 * 3211955 * 2
def baseEnd_3211955 : Nat := 122168648563858218147481

theorem tailTrace_3211955 : CollatzResearch.WordTrace tailWord_3211955 prefixEnd_3211955 122168648563858218147481 := by
  unfold tailWord_3211955
  simp only [CollatzResearch.WordTrace]
  refine ⟨117149623078643068086157319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78099748719095378724104879 117149623078643068086157319)
  ·
    refine ⟨175724434617964602129235979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117149623078643068086157319 175724434617964602129235979)
    ·
      refine ⟨263586651926946903193853969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175724434617964602129235979 263586651926946903193853969)
      ·
        refine ⟨197689988945210177395390477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263586651926946903193853969 197689988945210177395390477)
        ·
          refine ⟨74133745854453816523271429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197689988945210177395390477 74133745854453816523271429)
          ·
            refine ⟨13900077347710090598113393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74133745854453816523271429 13900077347710090598113393)
            ·
              refine ⟨10425058010782567948585045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13900077347710090598113393 10425058010782567948585045)
              ·
                refine ⟨122168648563858218147481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10425058010782567948585045 122168648563858218147481)
                ·
                  rfl

theorem cell22_3211955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 8].length) (baseStart_3211955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211955 prefixEnd_3211955 := by exact prefixLift 3211955
  have htrace : WordTrace (prefixWord ++ tailWord_3211955) baseStart_3211955 baseEnd_3211955 := by
    simpa [prefixWord, tailWord_3211955, baseEnd_3211955] using wordTrace_append hprefix tailTrace_3211955
  have hstable : (prefixWord ++ tailWord_3211955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211955).length < 2 ^ (prefixWord ++ tailWord_3211955).sum := by decide
  have hdescent : baseEnd_3211955 < baseStart_3211955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211985 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3211985 : Nat := 118140960795 + 3211985 * 2 ^ 59
def prefixEnd_3211985 : Nat := 4983230072969 + 3 ^ 40 * 3211985 * 2
def baseEnd_3211985 : Nat := 1099528106687813885077237

theorem tailTrace_3211985 : CollatzResearch.WordTrace tailWord_3211985 prefixEnd_3211985 1099528106687813885077237 := by
  unfold tailWord_3211985
  simp only [CollatzResearch.WordTrace]
  refine ⟨117150717268534383209749409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78100478179022922139832939 117150717268534383209749409)
  ·
    refine ⟨87863037951400787407312057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117150717268534383209749409 87863037951400787407312057)
    ·
      refine ⟨65897278463550590555484043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87863037951400787407312057 65897278463550590555484043)
      ·
        refine ⟨98845917695325885833226065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65897278463550590555484043 98845917695325885833226065)
        ·
          refine ⟨74134438271494414374919549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98845917695325885833226065 74134438271494414374919549)
          ·
            refine ⟨27800414351810405390594831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74134438271494414374919549 27800414351810405390594831)
            ·
              refine ⟨41700621527715608085892247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27800414351810405390594831 41700621527715608085892247)
              ·
                refine ⟨62550932291573412128838371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41700621527715608085892247 62550932291573412128838371)
                ·
                  refine ⟨93826398437360118193257557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62550932291573412128838371 93826398437360118193257557)
                  ·
                    refine ⟨1099528106687813885077237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93826398437360118193257557 1099528106687813885077237)
                    ·
                      rfl

theorem cell22_3211985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3211985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3211985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3211985 prefixEnd_3211985 := by exact prefixLift 3211985
  have htrace : WordTrace (prefixWord ++ tailWord_3211985) baseStart_3211985 baseEnd_3211985 := by
    simpa [prefixWord, tailWord_3211985, baseEnd_3211985] using wordTrace_append hprefix tailTrace_3211985
  have hstable : (prefixWord ++ tailWord_3211985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211985).length < 2 ^ (prefixWord ++ tailWord_3211985).sum := by decide
  have hdescent : baseEnd_3211985 < baseStart_3211985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212000 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 9]
def baseStart_3212000 : Nat := 118140960795 + 3212000 * 2 ^ 59
def prefixEnd_3212000 : Nat := 4983230072969 + 3 ^ 40 * 3212000 * 2
def baseEnd_3212000 : Nat := 366511080498119615317397

theorem tailTrace_3212000 : CollatzResearch.WordTrace tailWord_3212000 prefixEnd_3212000 366511080498119615317397 := by
  unfold tailWord_3212000
  simp only [CollatzResearch.WordTrace]
  refine ⟨58575632181740020385772727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78100842908986693847696969 58575632181740020385772727)
  ·
    refine ⟨87863448272610030578659091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58575632181740020385772727 87863448272610030578659091)
    ·
      refine ⟨131795172408915045867988637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87863448272610030578659091 131795172408915045867988637)
      ·
        refine ⟨49423189653343142200495739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131795172408915045867988637 49423189653343142200495739)
        ·
          refine ⟨74134784480014713300743609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49423189653343142200495739 74134784480014713300743609)
          ·
            refine ⟨55601088360011034975557707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74134784480014713300743609 55601088360011034975557707)
            ·
              refine ⟨83401632540016552463336561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55601088360011034975557707 83401632540016552463336561)
              ·
                refine ⟨62551224405012414347502421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83401632540016552463336561 62551224405012414347502421)
                ·
                  refine ⟨366511080498119615317397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62551224405012414347502421 366511080498119615317397)
                  ·
                    rfl

theorem cell22_3212000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_3212000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212000 prefixEnd_3212000 := by exact prefixLift 3212000
  have htrace : WordTrace (prefixWord ++ tailWord_3212000) baseStart_3212000 baseEnd_3212000 := by
    simpa [prefixWord, tailWord_3212000, baseEnd_3212000] using wordTrace_append hprefix tailTrace_3212000
  have hstable : (prefixWord ++ tailWord_3212000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212000).length < 2 ^ (prefixWord ++ tailWord_3212000).sum := by decide
  have hdescent : baseEnd_3212000 < baseStart_3212000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212004 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_3212004 : Nat := 118140960795 + 3212004 * 2 ^ 59
def prefixEnd_3212004 : Nat := 4983230072969 + 3 ^ 40 * 3212004 * 2
def baseEnd_3212004 : Nat := 1099534610776104168852179

theorem tailTrace_3212004 : CollatzResearch.WordTrace tailWord_3212004 prefixEnd_3212004 1099534610776104168852179 := by
  unfold tailWord_3212004
  simp only [CollatzResearch.WordTrace]
  refine ⟨58575705127732774727345533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78100940170310366303127377 58575705127732774727345533)
  ·
    refine ⟨21965889422899790522754575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58575705127732774727345533 21965889422899790522754575)
    ·
      refine ⟨32948834134349685784131863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21965889422899790522754575 32948834134349685784131863)
      ·
        refine ⟨49423251201524528676197795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32948834134349685784131863 49423251201524528676197795)
        ·
          refine ⟨74134876802286793014296693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49423251201524528676197795 74134876802286793014296693)
          ·
            refine ⟨6950144700214386845090315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74134876802286793014296693 6950144700214386845090315)
            ·
              refine ⟨10425217050321580267635473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6950144700214386845090315 10425217050321580267635473)
              ·
                refine ⟨7818912787741185200726605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10425217050321580267635473 7818912787741185200726605)
                ·
                  refine ⟨2932092295402944450272477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7818912787741185200726605 2932092295402944450272477)
                  ·
                    refine ⟨1099534610776104168852179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2932092295402944450272477 1099534610776104168852179)
                    ·
                      rfl

theorem cell22_3212004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_3212004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212004 prefixEnd_3212004 := by exact prefixLift 3212004
  have htrace : WordTrace (prefixWord ++ tailWord_3212004) baseStart_3212004 baseEnd_3212004 := by
    simpa [prefixWord, tailWord_3212004, baseEnd_3212004] using wordTrace_append hprefix tailTrace_3212004
  have hstable : (prefixWord ++ tailWord_3212004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212004).length < 2 ^ (prefixWord ++ tailWord_3212004).sum := by decide
  have hdescent : baseEnd_3212004 < baseStart_3212004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212034 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3212034 : Nat := 118140960795 + 3212034 * 2 ^ 59
def prefixEnd_3212034 : Nat := 4983230072969 + 3 ^ 40 * 3212034 * 2
def baseEnd_3212034 : Nat := 366514960129731363534029

theorem tailTrace_3212034 : CollatzResearch.WordTrace tailWord_3212034 prefixEnd_3212034 366514960129731363534029 := by
  unfold tailWord_3212034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29288126111339216144570789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78101669630237909718855437 29288126111339216144570789)
  ·
    refine ⟨5491523645876103027107023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29288126111339216144570789 5491523645876103027107023)
    ·
      refine ⟨8237285468814154540660535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5491523645876103027107023 8237285468814154540660535)
      ·
        refine ⟨12355928203221231810990803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8237285468814154540660535 12355928203221231810990803)
        ·
          refine ⟨18533892304831847716486205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12355928203221231810990803 18533892304831847716486205)
          ·
            refine ⟨6950209614311942893682327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18533892304831847716486205 6950209614311942893682327)
            ·
              refine ⟨10425314421467914340523491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6950209614311942893682327 10425314421467914340523491)
              ·
                refine ⟨15637971632201871510785237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10425314421467914340523491 15637971632201871510785237)
                ·
                  refine ⟨366514960129731363534029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15637971632201871510785237 366514960129731363534029)
                  ·
                    rfl

theorem cell22_3212034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3212034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212034 prefixEnd_3212034 := by exact prefixLift 3212034
  have htrace : WordTrace (prefixWord ++ tailWord_3212034) baseStart_3212034 baseEnd_3212034 := by
    simpa [prefixWord, tailWord_3212034, baseEnd_3212034] using wordTrace_append hprefix tailTrace_3212034
  have hstable : (prefixWord ++ tailWord_3212034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212034).length < 2 ^ (prefixWord ++ tailWord_3212034).sum := by decide
  have hdescent : baseEnd_3212034 < baseStart_3212034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212064 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_3212064 : Nat := 118140960795 + 3212064 * 2 ^ 59
def prefixEnd_3212064 : Nat := 4983230072969 + 3 ^ 40 * 3212064 * 2
def baseEnd_3212064 : Nat := 1099555150002284012351995

theorem tailTrace_3212064 : CollatzResearch.WordTrace tailWord_3212064 prefixEnd_3212064 1099555150002284012351995 := by
  unfold tailWord_3212064
  simp only [CollatzResearch.WordTrace]
  refine ⟨58576799317624089850937623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78102399090165453134583497 58576799317624089850937623)
  ·
    refine ⟨87865198976436134776406435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58576799317624089850937623 87865198976436134776406435)
    ·
      refine ⟨131797798464654202164609653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87865198976436134776406435 131797798464654202164609653)
      ·
        refine ⟨12356043606061331452932155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131797798464654202164609653 12356043606061331452932155)
        ·
          refine ⟨18534065409091997179398233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12356043606061331452932155 18534065409091997179398233)
          ·
            refine ⟨13900549056818997884548675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18534065409091997179398233 13900549056818997884548675)
            ·
              refine ⟨20850823585228496826823013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13900549056818997884548675 20850823585228496826823013)
              ·
                refine ⟨3909529422230343155029315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20850823585228496826823013 3909529422230343155029315)
                ·
                  refine ⟨5864294133345514732543973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909529422230343155029315 5864294133345514732543973)
                  ·
                    refine ⟨1099555150002284012351995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5864294133345514732543973 1099555150002284012351995)
                    ·
                      rfl

theorem cell22_3212064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_3212064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212064 prefixEnd_3212064 := by exact prefixLift 3212064
  have htrace : WordTrace (prefixWord ++ tailWord_3212064) baseStart_3212064 baseEnd_3212064 := by
    simpa [prefixWord, tailWord_3212064, baseEnd_3212064] using wordTrace_append hprefix tailTrace_3212064
  have hstable : (prefixWord ++ tailWord_3212064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212064).length < 2 ^ (prefixWord ++ tailWord_3212064).sum := by decide
  have hdescent : baseEnd_3212064 < baseStart_3212064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212102 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_3212102 : Nat := 118140960795 + 3212102 * 2 ^ 59
def prefixEnd_3212102 : Nat := 4983230072969 + 3 ^ 40 * 3212102 * 2
def baseEnd_3212102 : Nat := 366522719392954859967293

theorem tailTrace_3212102 : CollatzResearch.WordTrace tailWord_3212102 prefixEnd_3212102 366522719392954859967293 := by
  unfold tailWord_3212102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661093269034703505992455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78103323072740341461172373 3661093269034703505992455)
  ·
    refine ⟨5491639903552055258988683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3661093269034703505992455 5491639903552055258988683)
    ·
      refine ⟨8237459855328082888483025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5491639903552055258988683 8237459855328082888483025)
      ·
        refine ⟨6178094891496062166362269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8237459855328082888483025 6178094891496062166362269)
        ·
          refine ⟨2316785584311023312385851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6178094891496062166362269 2316785584311023312385851)
          ·
            refine ⟨3475178376466534968578777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316785584311023312385851 3475178376466534968578777)
            ·
              refine ⟨2606383782349901226434083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3475178376466534968578777 2606383782349901226434083)
              ·
                refine ⟨3909575673524851839651125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606383782349901226434083 3909575673524851839651125)
                ·
                  refine ⟨366522719392954859967293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3909575673524851839651125 366522719392954859967293)
                  ·
                    rfl

theorem cell22_3212102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_3212102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212102 prefixEnd_3212102 := by exact prefixLift 3212102
  have htrace : WordTrace (prefixWord ++ tailWord_3212102) baseStart_3212102 baseEnd_3212102 := by
    simpa [prefixWord, tailWord_3212102, baseEnd_3212102] using wordTrace_append hprefix tailTrace_3212102
  have hstable : (prefixWord ++ tailWord_3212102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212102).length < 2 ^ (prefixWord ++ tailWord_3212102).sum := by decide
  have hdescent : baseEnd_3212102 < baseStart_3212102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212124 : List Nat := [2, 2, 4, 2, 1, 1, 2, 8]
def baseStart_3212124 : Nat := 118140960795 + 3212124 * 2 ^ 59
def prefixEnd_3212124 : Nat := 4983230072969 + 3 ^ 40 * 3212124 * 2
def baseEnd_3212124 : Nat := 122175076580940428427979

theorem tailTrace_3212124 : CollatzResearch.WordTrace tailWord_3212124 prefixEnd_3212124 122175076580940428427979 := by
  unfold tailWord_3212124
  simp only [CollatzResearch.WordTrace]
  refine ⟨58577893507515404974529713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78103858010020539966039617 58577893507515404974529713)
  ·
    refine ⟨43933420130636553730897285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58577893507515404974529713 43933420130636553730897285)
    ·
      refine ⟨8237516274494353824543241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43933420130636553730897285 8237516274494353824543241)
      ·
        refine ⟨6178137205870765368407431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8237516274494353824543241 6178137205870765368407431)
        ·
          refine ⟨9267205808806148052611147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178137205870765368407431 9267205808806148052611147)
          ·
            refine ⟨13900808713209222078916721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9267205808806148052611147 13900808713209222078916721)
            ·
              refine ⟨10425606534906916559187541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13900808713209222078916721 10425606534906916559187541)
              ·
                refine ⟨122175076580940428427979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10425606534906916559187541 122175076580940428427979)
                ·
                  rfl

theorem cell22_3212124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 8].length) (baseStart_3212124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212124 prefixEnd_3212124 := by exact prefixLift 3212124
  have htrace : WordTrace (prefixWord ++ tailWord_3212124) baseStart_3212124 baseEnd_3212124 := by
    simpa [prefixWord, tailWord_3212124, baseEnd_3212124] using wordTrace_append hprefix tailTrace_3212124
  have hstable : (prefixWord ++ tailWord_3212124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212124).length < 2 ^ (prefixWord ++ tailWord_3212124).sum := by decide
  have hdescent : baseEnd_3212124 < baseStart_3212124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212158 : List Nat := [4, 2, 3, 1, 2, 2, 1, 7]
def baseStart_3212158 : Nat := 118140960795 + 3212158 * 2 ^ 59
def prefixEnd_3212158 : Nat := 4983230072969 + 3 ^ 40 * 3212158 * 2
def baseEnd_3212158 : Nat := 122176369791477677833523

theorem tailTrace_3212158 : CollatzResearch.WordTrace tailWord_3212158 prefixEnd_3212158 122176369791477677833523 := by
  unfold tailWord_3212158
  simp only [CollatzResearch.WordTrace]
  refine ⟨14644628387113454219474641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78104684731271755837198085 14644628387113454219474641)
  ·
    refine ⟨10983471290335090664605981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14644628387113454219474641 10983471290335090664605981)
    ·
      refine ⟨4118801733875658999227243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10983471290335090664605981 4118801733875658999227243)
      ·
        refine ⟨6178202600813488498840865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4118801733875658999227243 6178202600813488498840865)
        ·
          refine ⟨4633651950610116374130649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6178202600813488498840865 4633651950610116374130649)
          ·
            refine ⟨3475238962957587280597987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4633651950610116374130649 3475238962957587280597987)
            ·
              refine ⟨5212858444436380920896981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475238962957587280597987 5212858444436380920896981)
              ·
                refine ⟨122176369791477677833523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5212858444436380920896981 122176369791477677833523)
                ·
                  rfl

theorem cell22_3212158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_3212158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212158 prefixEnd_3212158 := by exact prefixLift 3212158
  have htrace : WordTrace (prefixWord ++ tailWord_3212158) baseStart_3212158 baseEnd_3212158 := by
    simpa [prefixWord, tailWord_3212158, baseEnd_3212158] using wordTrace_append hprefix tailTrace_3212158
  have hstable : (prefixWord ++ tailWord_3212158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212158).length < 2 ^ (prefixWord ++ tailWord_3212158).sum := by decide
  have hdescent : baseEnd_3212158 < baseStart_3212158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212169 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 5]
def baseStart_3212169 : Nat := 118140960795 + 3212169 * 2 ^ 59
def prefixEnd_3212169 : Nat := 4983230072969 + 3 ^ 40 * 3212169 * 2
def baseEnd_3212169 : Nat := 366530364549366246158891

theorem tailTrace_3212169 : CollatzResearch.WordTrace tailWord_3212169 prefixEnd_3212169 366530364549366246158891 := by
  unfold tailWord_3212169
  simp only [CollatzResearch.WordTrace]
  refine ⟨117157428299867782634447561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78104952199911855089631707 117157428299867782634447561)
  ·
    refine ⟨87868071224900836975835671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117157428299867782634447561 87868071224900836975835671)
    ·
      refine ⟨131802106837351255463753507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87868071224900836975835671 131802106837351255463753507)
      ·
        refine ⟨197703160256026883195630261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131802106837351255463753507 197703160256026883195630261)
        ·
          refine ⟨18534671274002520299590337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197703160256026883195630261 18534671274002520299590337)
          ·
            refine ⟨13901003455501890224692753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18534671274002520299590337 13901003455501890224692753)
            ·
              refine ⟨10425752591626417668519565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13901003455501890224692753 10425752591626417668519565)
              ·
                refine ⟨3909657221859906625694837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10425752591626417668519565 3909657221859906625694837)
                ·
                  refine ⟨366530364549366246158891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3909657221859906625694837 366530364549366246158891)
                  ·
                    rfl

theorem cell22_3212169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_3212169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212169 prefixEnd_3212169 := by exact prefixLift 3212169
  have htrace : WordTrace (prefixWord ++ tailWord_3212169) baseStart_3212169 baseEnd_3212169 := by
    simpa [prefixWord, tailWord_3212169, baseEnd_3212169] using wordTrace_append hprefix tailTrace_3212169
  have hstable : (prefixWord ++ tailWord_3212169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212169).length < 2 ^ (prefixWord ++ tailWord_3212169).sum := by decide
  have hdescent : baseEnd_3212169 < baseStart_3212169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212248 : List Nat := [2, 1, 2, 2, 2, 5, 1, 3, 4]
def baseStart_3212248 : Nat := 118140960795 + 3212248 * 2 ^ 59
def prefixEnd_3212248 : Nat := 4983230072969 + 3 ^ 40 * 3212248 * 2
def baseEnd_3212248 : Nat := 366539378987522955250477

theorem tailTrace_3212248 : CollatzResearch.WordTrace tailWord_3212248 prefixEnd_3212248 366539378987522955250477 := by
  unfold tailWord_3212248
  simp only [CollatzResearch.WordTrace]
  refine ⟨58580154833290789563286699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78106873111054386084382265 58580154833290789563286699)
  ·
    refine ⟨87870232249936184344930049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58580154833290789563286699 87870232249936184344930049)
    ·
      refine ⟨65902674187452138258697537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87870232249936184344930049 65902674187452138258697537)
      ·
        refine ⟨49427005640589103694023153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65902674187452138258697537 49427005640589103694023153)
        ·
          refine ⟨37070254230441827770517365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49427005640589103694023153 37070254230441827770517365)
          ·
            refine ⟨3475336334103921353486003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37070254230441827770517365 3475336334103921353486003)
            ·
              refine ⟨5213004501155882030229005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475336334103921353486003 5213004501155882030229005)
              ·
                refine ⟨1954876687933455761335877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5213004501155882030229005 1954876687933455761335877)
                ·
                  refine ⟨366539378987522955250477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1954876687933455761335877 366539378987522955250477)
                  ·
                    rfl

theorem cell22_3212248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 4].length) (baseStart_3212248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212248 prefixEnd_3212248 := by exact prefixLift 3212248
  have htrace : WordTrace (prefixWord ++ tailWord_3212248) baseStart_3212248 baseEnd_3212248 := by
    simpa [prefixWord, tailWord_3212248, baseEnd_3212248] using wordTrace_append hprefix tailTrace_3212248
  have hstable : (prefixWord ++ tailWord_3212248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212248).length < 2 ^ (prefixWord ++ tailWord_3212248).sum := by decide
  have hdescent : baseEnd_3212248 < baseStart_3212248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212321 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 5]
def baseStart_3212321 : Nat := 118140960795 + 3212321 * 2 ^ 59
def prefixEnd_3212321 : Nat := 4983230072969 + 3 ^ 40 * 3212321 * 2
def baseEnd_3212321 : Nat := 366547708784807002892069

theorem tailTrace_3212321 : CollatzResearch.WordTrace tailWord_3212321 prefixEnd_3212321 366547708784807002892069 := by
  unfold tailWord_3212321
  simp only [CollatzResearch.WordTrace]
  refine ⟨117162972195317112593980817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78108648130211408395987211 117162972195317112593980817)
  ·
    refine ⟨87872229146487834445485613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117162972195317112593980817 87872229146487834445485613)
    ·
      refine ⟨32952085929932937917057105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87872229146487834445485613 32952085929932937917057105)
      ·
        refine ⟨24714064447449703437792829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32952085929932937917057105 24714064447449703437792829)
        ·
          refine ⟨9267774167793638789172311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24714064447449703437792829 9267774167793638789172311)
          ·
            refine ⟨13901661251690458183758467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9267774167793638789172311 13901661251690458183758467)
            ·
              refine ⟨20852491877535687275637701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13901661251690458183758467 20852491877535687275637701)
              ·
                refine ⟨3909842227037941364182069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20852491877535687275637701 3909842227037941364182069)
                ·
                  refine ⟨366547708784807002892069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3909842227037941364182069 366547708784807002892069)
                  ·
                    rfl

theorem cell22_3212321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_3212321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212321 prefixEnd_3212321 := by exact prefixLift 3212321
  have htrace : WordTrace (prefixWord ++ tailWord_3212321) baseStart_3212321 baseEnd_3212321 := by
    simpa [prefixWord, tailWord_3212321, baseEnd_3212321] using wordTrace_append hprefix tailTrace_3212321
  have hstable : (prefixWord ++ tailWord_3212321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212321).length < 2 ^ (prefixWord ++ tailWord_3212321).sum := by decide
  have hdescent : baseEnd_3212321 < baseStart_3212321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212351 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 1, 4]
def baseStart_3212351 : Nat := 118140960795 + 3212351 * 2 ^ 59
def prefixEnd_3212351 : Nat := 4983230072969 + 3 ^ 40 * 3212351 * 2
def baseEnd_3212351 : Nat := 1099653395967510930426115

theorem tailTrace_3212351 : CollatzResearch.WordTrace tailWord_3212351 prefixEnd_3212351 1099653395967510930426115 := by
  unfold tailWord_3212351
  simp only [CollatzResearch.WordTrace]
  refine ⟨117164066385208427717572907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78109377590138951811715271 117164066385208427717572907)
  ·
    refine ⟨175746099577812641576359361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117164066385208427717572907 175746099577812641576359361)
    ·
      refine ⟨131809574683359481182269521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175746099577812641576359361 131809574683359481182269521)
      ·
        refine ⟨98857181012519610886702141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131809574683359481182269521 98857181012519610886702141)
        ·
          refine ⟨37071442879694854082513303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98857181012519610886702141 37071442879694854082513303)
          ·
            refine ⟨55607164319542281123769955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37071442879694854082513303 55607164319542281123769955)
            ·
              refine ⟨83410746479313421685654933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55607164319542281123769955 83410746479313421685654933)
              ·
                refine ⟨3909878741217816641515075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83410746479313421685654933 3909878741217816641515075)
                ·
                  refine ⟨5864818111826724962272613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909878741217816641515075 5864818111826724962272613)
                  ·
                    refine ⟨1099653395967510930426115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5864818111826724962272613 1099653395967510930426115)
                    ·
                      rfl

theorem cell22_3212351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_3212351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212351 prefixEnd_3212351 := by exact prefixLift 3212351
  have htrace : WordTrace (prefixWord ++ tailWord_3212351) baseStart_3212351 baseEnd_3212351 := by
    simpa [prefixWord, tailWord_3212351, baseEnd_3212351] using wordTrace_append hprefix tailTrace_3212351
  have hstable : (prefixWord ++ tailWord_3212351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212351).length < 2 ^ (prefixWord ++ tailWord_3212351).sum := by decide
  have hdescent : baseEnd_3212351 < baseStart_3212351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212398 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3212398 : Nat := 118140960795 + 3212398 * 2 ^ 59
def prefixEnd_3212398 : Nat := 4983230072969 + 3 ^ 40 * 3212398 * 2
def baseEnd_3212398 : Nat := 1099669485028018474500971

theorem tailTrace_3212398 : CollatzResearch.WordTrace tailWord_3212398 prefixEnd_3212398 1099669485028018474500971 := by
  unfold tailWord_3212398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14645722577004769343066731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78110520410692103163022565 14645722577004769343066731)
  ·
    refine ⟨21968583865507154014600097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14645722577004769343066731 21968583865507154014600097)
    ·
      refine ⟨16476437899130365510950073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21968583865507154014600097 16476437899130365510950073)
      ·
        refine ⟨12357328424347774133212555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16476437899130365510950073 12357328424347774133212555)
        ·
          refine ⟨18535992636521661199818833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12357328424347774133212555 18535992636521661199818833)
          ·
            refine ⟨13901994477391245899864125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18535992636521661199818833 13901994477391245899864125)
            ·
              refine ⟨5213247929021717212449047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13901994477391245899864125 5213247929021717212449047)
              ·
                refine ⟨7819871893532575818673571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213247929021717212449047 7819871893532575818673571)
                ·
                  refine ⟨11729807840298863728010357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7819871893532575818673571 11729807840298863728010357)
                  ·
                    refine ⟨1099669485028018474500971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11729807840298863728010357 1099669485028018474500971)
                    ·
                      rfl

theorem cell22_3212398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3212398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212398 prefixEnd_3212398 := by exact prefixLift 3212398
  have htrace : WordTrace (prefixWord ++ tailWord_3212398) baseStart_3212398 baseEnd_3212398 := by
    simpa [prefixWord, tailWord_3212398, baseEnd_3212398] using wordTrace_append hprefix tailTrace_3212398
  have hstable : (prefixWord ++ tailWord_3212398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212398).length < 2 ^ (prefixWord ++ tailWord_3212398).sum := by decide
  have hdescent : baseEnd_3212398 < baseStart_3212398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212567 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 2, 3]
def baseStart_3212567 : Nat := 118140960795 + 3212567 * 2 ^ 59
def prefixEnd_3212567 : Nat := 4983230072969 + 3 ^ 40 * 3212567 * 2
def baseEnd_3212567 : Nat := 1099727337181758367025453

theorem tailTrace_3212567 : CollatzResearch.WordTrace tailWord_3212567 prefixEnd_3212567 1099727337181758367025453 := by
  unfold tailWord_3212567
  simp only [CollatzResearch.WordTrace]
  refine ⟨117171944552425896607435955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78114629701617264404957303 117171944552425896607435955)
  ·
    refine ⟨175757916828638844911153933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117171944552425896607435955 175757916828638844911153933)
    ·
      refine ⟨65909218810739566841682725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175757916828638844911153933 65909218810739566841682725)
      ·
        refine ⟨12357978527013668782815511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65909218810739566841682725 12357978527013668782815511)
        ·
          refine ⟨18536967790520503174223267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12357978527013668782815511 18536967790520503174223267)
          ·
            refine ⟨27805451685780754761334901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18536967790520503174223267 27805451685780754761334901)
            ·
              refine ⟨2606761095541945758875147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27805451685780754761334901 2606761095541945758875147)
              ·
                refine ⟨3910141643312918638312721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606761095541945758875147 3910141643312918638312721)
                ·
                  refine ⟨2932606232484688978734541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3910141643312918638312721 2932606232484688978734541)
                  ·
                    refine ⟨1099727337181758367025453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2932606232484688978734541 1099727337181758367025453)
                    ·
                      rfl

theorem cell22_3212567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_3212567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212567 prefixEnd_3212567 := by exact prefixLift 3212567
  have htrace : WordTrace (prefixWord ++ tailWord_3212567) baseStart_3212567 baseEnd_3212567 := by
    simpa [prefixWord, tailWord_3212567, baseEnd_3212567] using wordTrace_append hprefix tailTrace_3212567
  have hstable : (prefixWord ++ tailWord_3212567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212567).length < 2 ^ (prefixWord ++ tailWord_3212567).sum := by decide
  have hdescent : baseEnd_3212567 < baseStart_3212567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212608 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 5]
def baseStart_3212608 : Nat := 118140960795 + 3212608 * 2 ^ 59
def prefixEnd_3212608 : Nat := 4983230072969 + 3 ^ 40 * 3212608 * 2
def baseEnd_3212608 : Nat := 366580457439882642250109

theorem tailTrace_3212608 : CollatzResearch.WordTrace tailWord_3212608 prefixEnd_3212608 366580457439882642250109 := by
  unfold tailWord_3212608
  simp only [CollatzResearch.WordTrace]
  refine ⟨58586719972638680304839239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78115626630184907073118985 58586719972638680304839239)
  ·
    refine ⟨87880079958958020457258859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58586719972638680304839239 87880079958958020457258859)
    ·
      refine ⟨131820119938437030685888289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87880079958958020457258859 131820119938437030685888289)
      ·
        refine ⟨98865089953827773014416217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131820119938437030685888289 98865089953827773014416217)
        ·
          refine ⟨74148817465370829760812163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98865089953827773014416217 74148817465370829760812163)
          ·
            refine ⟨111223226198056244641218245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74148817465370829760812163 111223226198056244641218245)
            ·
              refine ⟨20854354912135545870228421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111223226198056244641218245 20854354912135545870228421)
              ·
                refine ⟨3910191546025414850667829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20854354912135545870228421 3910191546025414850667829)
                ·
                  refine ⟨366580457439882642250109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3910191546025414850667829 366580457439882642250109)
                  ·
                    rfl

theorem cell22_3212608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_3212608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212608 prefixEnd_3212608 := by exact prefixLift 3212608
  have htrace : WordTrace (prefixWord ++ tailWord_3212608) baseStart_3212608 baseEnd_3212608 := by
    simpa [prefixWord, tailWord_3212608, baseEnd_3212608] using wordTrace_append hprefix tailTrace_3212608
  have hstable : (prefixWord ++ tailWord_3212608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212608).length < 2 ^ (prefixWord ++ tailWord_3212608).sum := by decide
  have hdescent : baseEnd_3212608 < baseStart_3212608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212614 : List Nat := [6, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3212614 : Nat := 118140960795 + 3212614 * 2 ^ 59
def prefixEnd_3212614 : Nat := 4983230072969 + 3 ^ 40 * 3212614 * 2
def baseEnd_3212614 : Nat := 122193714026918434566701

theorem tailTrace_3212614 : CollatzResearch.WordTrace tailWord_3212614 prefixEnd_3212614 122193714026918434566701 := by
  unfold tailWord_3212614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661676836976738238574903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78115772522170415756264597 3661676836976738238574903)
  ·
    refine ⟨5492515255465107357862355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3661676836976738238574903 5492515255465107357862355)
    ·
      refine ⟨8238772883197661036793533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5492515255465107357862355 8238772883197661036793533)
      ·
        refine ⟨3089539831199122888797575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8238772883197661036793533 3089539831199122888797575)
        ·
          refine ⟨4634309746798684333196363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089539831199122888797575 4634309746798684333196363)
          ·
            refine ⟨6951464620198026499794545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4634309746798684333196363 6951464620198026499794545)
            ·
              refine ⟨5213598465148519874845909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6951464620198026499794545 5213598465148519874845909)
              ·
                refine ⟨122193714026918434566701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5213598465148519874845909 122193714026918434566701)
                ·
                  rfl

theorem cell22_3212614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3212614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212614 prefixEnd_3212614 := by exact prefixLift 3212614
  have htrace : WordTrace (prefixWord ++ tailWord_3212614) baseStart_3212614 baseEnd_3212614 := by
    simpa [prefixWord, tailWord_3212614, baseEnd_3212614] using wordTrace_append hprefix tailTrace_3212614
  have hstable : (prefixWord ++ tailWord_3212614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212614).length < 2 ^ (prefixWord ++ tailWord_3212614).sum := by decide
  have hdescent : baseEnd_3212614 < baseStart_3212614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212668 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_3212668 : Nat := 118140960795 + 3212668 * 2 ^ 59
def prefixEnd_3212668 : Nat := 4983230072969 + 3 ^ 40 * 3212668 * 2
def baseEnd_3212668 : Nat := 1099761911545827770250143

theorem tailTrace_3212668 : CollatzResearch.WordTrace tailWord_3212668 prefixEnd_3212668 1099761911545827770250143 := by
  unfold tailWord_3212668
  simp only [CollatzResearch.WordTrace]
  refine ⟨58587814162529995428431329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78117085550039993904575105 58587814162529995428431329)
  ·
    refine ⟨43940860621897496571323497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58587814162529995428431329 43940860621897496571323497)
    ·
      refine ⟨32955645466423122428492623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43940860621897496571323497 32955645466423122428492623)
      ·
        refine ⟨49433468199634683642738935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32955645466423122428492623 49433468199634683642738935)
        ·
          refine ⟨74150202299452025464108403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49433468199634683642738935 74150202299452025464108403)
          ·
            refine ⟨111225303449178038196162605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74150202299452025464108403 111225303449178038196162605)
            ·
              refine ⟨41709488793441764323560977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111225303449178038196162605 41709488793441764323560977)
              ·
                refine ⟨31282116595081323242670733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41709488793441764323560977 31282116595081323242670733)
                ·
                  refine ⟨11730793723155496216001525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31282116595081323242670733 11730793723155496216001525)
                  ·
                    refine ⟨1099761911545827770250143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11730793723155496216001525 1099761911545827770250143)
                    ·
                      rfl

theorem cell22_3212668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_3212668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212668 prefixEnd_3212668 := by exact prefixLift 3212668
  have htrace : WordTrace (prefixWord ++ tailWord_3212668) baseStart_3212668 baseEnd_3212668 := by
    simpa [prefixWord, tailWord_3212668, baseEnd_3212668] using wordTrace_append hprefix tailTrace_3212668
  have hstable : (prefixWord ++ tailWord_3212668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212668).length < 2 ^ (prefixWord ++ tailWord_3212668).sum := by decide
  have hdescent : baseEnd_3212668 < baseStart_3212668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212683 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 1, 6]
def baseStart_3212683 : Nat := 118140960795 + 3212683 * 2 ^ 59
def prefixEnd_3212683 : Nat := 4983230072969 + 3 ^ 40 * 3212683 * 2
def baseEnd_3212683 : Nat := 1099767046352372731125097

theorem tailTrace_3212683 : CollatzResearch.WordTrace tailWord_3212683 prefixEnd_3212683 1099767046352372731125097 := by
  unfold tailWord_3212683
  simp only [CollatzResearch.WordTrace]
  refine ⟨117176175420005648418658703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78117450280003765612439135 117176175420005648418658703)
  ·
    refine ⟨175764263130008472627988055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117176175420005648418658703 175764263130008472627988055)
    ·
      refine ⟨263646394695012708941982083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175764263130008472627988055 263646394695012708941982083)
      ·
        refine ⟨395469592042519063412973125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263646394695012708941982083 395469592042519063412973125)
        ·
          refine ⟨74150548507972324389932461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395469592042519063412973125 74150548507972324389932461)
          ·
            refine ⟨27806455690489621646224673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74150548507972324389932461 27806455690489621646224673)
            ·
              refine ⟨20854841767867216234668505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27806455690489621646224673 20854841767867216234668505)
              ·
                refine ⟨15641131325900412176001379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20854841767867216234668505 15641131325900412176001379)
                ·
                  refine ⟨23461696988850618264002069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15641131325900412176001379 23461696988850618264002069)
                  ·
                    refine ⟨1099767046352372731125097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23461696988850618264002069 1099767046352372731125097)
                    ·
                      rfl

theorem cell22_3212683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_3212683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212683 prefixEnd_3212683 := by exact prefixLift 3212683
  have htrace : WordTrace (prefixWord ++ tailWord_3212683) baseStart_3212683 baseEnd_3212683 := by
    simpa [prefixWord, tailWord_3212683, baseEnd_3212683] using wordTrace_append hprefix tailTrace_3212683
  have hstable : (prefixWord ++ tailWord_3212683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212683).length < 2 ^ (prefixWord ++ tailWord_3212683).sum := by decide
  have hdescent : baseEnd_3212683 < baseStart_3212683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212728 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_3212728 : Nat := 118140960795 + 3212728 * 2 ^ 59
def prefixEnd_3212728 : Nat := 4983230072969 + 3 ^ 40 * 3212728 * 2
def baseEnd_3212728 : Nat := 1099782450772007613749959

theorem tailTrace_3212728 : CollatzResearch.WordTrace tailWord_3212728 prefixEnd_3212728 1099782450772007613749959 := by
  unfold tailWord_3212728
  simp only [CollatzResearch.WordTrace]
  refine ⟨58588908352421310552023419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78118544469895080736031225 58588908352421310552023419)
  ·
    refine ⟨87883362528631965828035129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58588908352421310552023419 87883362528631965828035129)
    ·
      refine ⟨65912521896473974371026347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87883362528631965828035129 65912521896473974371026347)
      ·
        refine ⟨98868782844710961556539521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65912521896473974371026347 98868782844710961556539521)
        ·
          refine ⟨74151587133533221167404641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98868782844710961556539521 74151587133533221167404641)
          ·
            refine ⟨55613690350149915875553481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74151587133533221167404641 55613690350149915875553481)
            ·
              refine ⟨41710267762612436906665111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55613690350149915875553481 41710267762612436906665111)
              ·
                refine ⟨62565401643918655359997667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41710267762612436906665111 62565401643918655359997667)
                ·
                  refine ⟨93848102465877983039996501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62565401643918655359997667 93848102465877983039996501)
                  ·
                    refine ⟨1099782450772007613749959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93848102465877983039996501 1099782450772007613749959)
                    ·
                      rfl

theorem cell22_3212728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_3212728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212728 prefixEnd_3212728 := by exact prefixLift 3212728
  have htrace : WordTrace (prefixWord ++ tailWord_3212728) baseStart_3212728 baseEnd_3212728 := by
    simpa [prefixWord, tailWord_3212728, baseEnd_3212728] using wordTrace_append hprefix tailTrace_3212728
  have hstable : (prefixWord ++ tailWord_3212728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212728).length < 2 ^ (prefixWord ++ tailWord_3212728).sum := by decide
  have hdescent : baseEnd_3212728 < baseStart_3212728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212781 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_3212781 : Nat := 118140960795 + 3212781 * 2 ^ 59
def prefixEnd_3212781 : Nat := 4983230072969 + 3 ^ 40 * 3212781 * 2
def baseEnd_3212781 : Nat := 1099800593755133142174797

theorem tailTrace_3212781 : CollatzResearch.WordTrace tailWord_3212781 prefixEnd_3212781 1099800593755133142174797 := by
  unfold tailWord_3212781
  simp only [CollatzResearch.WordTrace]
  refine ⟨117179749773650611155726197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78119833182433740770484131 117179749773650611155726197)
  ·
    refine ⟨10985601541279744795849331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117179749773650611155726197 10985601541279744795849331)
    ·
      refine ⟨16478402311919617193773997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10985601541279744795849331 16478402311919617193773997)
      ·
        refine ⟨6179400866969856447665249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16478402311919617193773997 6179400866969856447665249)
        ·
          refine ⟨4634550650227392335748937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6179400866969856447665249 4634550650227392335748937)
          ·
            refine ⟨3475912987670544251811703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4634550650227392335748937 3475912987670544251811703)
            ·
              refine ⟨5213869481505816377717555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475912987670544251811703 5213869481505816377717555)
              ·
                refine ⟨7820804222258724566576333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213869481505816377717555 7820804222258724566576333)
                ·
                  refine ⟨2932801583347021712466125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7820804222258724566576333 2932801583347021712466125)
                  ·
                    refine ⟨1099800593755133142174797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2932801583347021712466125 1099800593755133142174797)
                    ·
                      rfl

theorem cell22_3212781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_3212781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212781 prefixEnd_3212781 := by exact prefixLift 3212781
  have htrace : WordTrace (prefixWord ++ tailWord_3212781) baseStart_3212781 baseEnd_3212781 := by
    simpa [prefixWord, tailWord_3212781, baseEnd_3212781] using wordTrace_append hprefix tailTrace_3212781
  have hstable : (prefixWord ++ tailWord_3212781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212781).length < 2 ^ (prefixWord ++ tailWord_3212781).sum := by decide
  have hdescent : baseEnd_3212781 < baseStart_3212781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212807 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3212807 : Nat := 118140960795 + 3212807 * 2 ^ 59
def prefixEnd_3212807 : Nat := 4983230072969 + 3 ^ 40 * 3212807 * 2
def baseEnd_3212807 : Nat := 1099809494086477741024717

theorem tailTrace_3212807 : CollatzResearch.WordTrace tailWord_3212807 prefixEnd_3212807 1099809494086477741024717 := by
  unfold tailWord_3212807
  simp only [CollatzResearch.WordTrace]
  refine ⟨117180698071556417596172675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78120465381037611730781783 117180698071556417596172675)
  ·
    refine ⟨175771047107334626394259013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117180698071556417596172675 175771047107334626394259013)
    ·
      refine ⟨32957071332625242448923565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175771047107334626394259013 32957071332625242448923565)
      ·
        refine ⟨12358901749734465918346337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32957071332625242448923565 12358901749734465918346337)
        ·
          refine ⟨9269176312300849438759753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12358901749734465918346337 9269176312300849438759753)
          ·
            refine ⟨6951882234225637079069815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269176312300849438759753 6951882234225637079069815)
            ·
              refine ⟨10427823351338455618604723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6951882234225637079069815 10427823351338455618604723)
              ·
                refine ⟨15641735027007683427907085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10427823351338455618604723 15641735027007683427907085)
                ·
                  refine ⟨5865650635127881285465157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15641735027007683427907085 5865650635127881285465157)
                  ·
                    refine ⟨1099809494086477741024717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5865650635127881285465157 1099809494086477741024717)
                    ·
                      rfl

theorem cell22_3212807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3212807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212807 prefixEnd_3212807 := by exact prefixLift 3212807
  have htrace : WordTrace (prefixWord ++ tailWord_3212807) baseStart_3212807 baseEnd_3212807 := by
    simpa [prefixWord, tailWord_3212807, baseEnd_3212807] using wordTrace_append hprefix tailTrace_3212807
  have hstable : (prefixWord ++ tailWord_3212807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212807).length < 2 ^ (prefixWord ++ tailWord_3212807).sum := by decide
  have hdescent : baseEnd_3212807 < baseStart_3212807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3212899 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 3, 3]
def baseStart_3212899 : Nat := 118140960795 + 3212899 * 2 ^ 59
def prefixEnd_3212899 : Nat := 4983230072969 + 3 ^ 40 * 3212899 * 2
def baseEnd_3212899 : Nat := 1099840987566620167724435

theorem tailTrace_3212899 : CollatzResearch.WordTrace tailWord_3212899 prefixEnd_3212899 1099840987566620167724435 := by
  unfold tailWord_3212899
  simp only [CollatzResearch.WordTrace]
  refine ⟨117184053587223117308521751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78122702391482078205681167 117184053587223117308521751)
  ·
    refine ⟨175776080380834675962782627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117184053587223117308521751 175776080380834675962782627)
    ·
      refine ⟨263664120571252013944173941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175776080380834675962782627 263664120571252013944173941)
      ·
        refine ⟨24718511303554876307266307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263664120571252013944173941 24718511303554876307266307)
        ·
          refine ⟨37077766955332314460899461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24718511303554876307266307 37077766955332314460899461)
          ·
            refine ⟨6952081304124808961418649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37077766955332314460899461 6952081304124808961418649)
            ·
              refine ⟨5214060978093606721063987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6952081304124808961418649 5214060978093606721063987)
              ·
                refine ⟨7821091467140410081595981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5214060978093606721063987 7821091467140410081595981)
                ·
                  refine ⟨2932909300177653780598493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7821091467140410081595981 2932909300177653780598493)
                  ·
                    refine ⟨1099840987566620167724435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2932909300177653780598493 1099840987566620167724435)
                    ·
                      rfl

theorem cell22_3212899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 3].length) (baseStart_3212899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3212899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3212899 prefixEnd_3212899 := by exact prefixLift 3212899
  have htrace : WordTrace (prefixWord ++ tailWord_3212899) baseStart_3212899 baseEnd_3212899 := by
    simpa [prefixWord, tailWord_3212899, baseEnd_3212899] using wordTrace_append hprefix tailTrace_3212899
  have hstable : (prefixWord ++ tailWord_3212899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3212899).length < 2 ^ (prefixWord ++ tailWord_3212899).sum := by decide
  have hdescent : baseEnd_3212899 < baseStart_3212899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3212899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213002 : List Nat := [3, 1, 2, 1, 5, 10]
def baseStart_3213002 : Nat := 118140960795 + 3213002 * 2 ^ 59
def prefixEnd_3213002 : Nat := 4983230072969 + 3 ^ 40 * 3213002 * 2
def baseEnd_3213002 : Nat := 13578719093476076943199

theorem tailTrace_3213002 : CollatzResearch.WordTrace tailWord_3213002 prefixEnd_3213002 13578719093476076943199 := by
  unfold tailWord_3213002
  simp only [CollatzResearch.WordTrace]
  refine ⟨29296952576462491474880315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78125206870566643933014173 29296952576462491474880315)
  ·
    refine ⟨43945428864693737212320473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29296952576462491474880315 43945428864693737212320473)
    ·
      refine ⟨32959071648520302909240355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43945428864693737212320473 32959071648520302909240355)
      ·
        refine ⟨49438607472780454363860533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32959071648520302909240355 49438607472780454363860533)
        ·
          refine ⟨4634869450573167596611925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49438607472780454363860533 4634869450573167596611925)
          ·
            refine ⟨13578719093476076943199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4634869450573167596611925 13578719093476076943199)
            ·
              rfl

theorem cell22_3213002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 10].length) (baseStart_3213002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213002 prefixEnd_3213002 := by exact prefixLift 3213002
  have htrace : WordTrace (prefixWord ++ tailWord_3213002) baseStart_3213002 baseEnd_3213002 := by
    simpa [prefixWord, tailWord_3213002, baseEnd_3213002] using wordTrace_append hprefix tailTrace_3213002
  have hstable : (prefixWord ++ tailWord_3213002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213002).length < 2 ^ (prefixWord ++ tailWord_3213002).sum := by decide
  have hdescent : baseEnd_3213002 < baseStart_3213002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213006 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_3213006 : Nat := 118140960795 + 3213006 * 2 ^ 59
def prefixEnd_3213006 : Nat := 4983230072969 + 3 ^ 40 * 3213006 * 2
def baseEnd_3213006 : Nat := 1099877615853307555299107

theorem tailTrace_3213006 : CollatzResearch.WordTrace tailWord_3213006 prefixEnd_3213006 1099877615853307555299107 := by
  unfold tailWord_3213006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14648494524729434322833359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78125304131890316388444581 14648494524729434322833359)
  ·
    refine ⟨21972741787094151484250039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14648494524729434322833359 21972741787094151484250039)
    ·
      refine ⟨32959112680641227226375059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21972741787094151484250039 32959112680641227226375059)
      ·
        refine ⟨49438669020961840839562589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32959112680641227226375059 49438669020961840839562589)
        ·
          refine ⟨18539500882860690314835971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49438669020961840839562589 18539500882860690314835971)
          ·
            refine ⟨27809251324291035472253957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18539500882860690314835971 27809251324291035472253957)
            ·
              refine ⟨5214234623304569151047617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27809251324291035472253957 5214234623304569151047617)
              ·
                refine ⟨3910675967478426863285713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5214234623304569151047617 3910675967478426863285713)
                ·
                  refine ⟨2933006975608820147464285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3910675967478426863285713 2933006975608820147464285)
                  ·
                    refine ⟨1099877615853307555299107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2933006975608820147464285 1099877615853307555299107)
                    ·
                      rfl

theorem cell22_3213006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_3213006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213006 prefixEnd_3213006 := by exact prefixLift 3213006
  have htrace : WordTrace (prefixWord ++ tailWord_3213006) baseStart_3213006 baseEnd_3213006 := by
    simpa [prefixWord, tailWord_3213006, baseEnd_3213006] using wordTrace_append hprefix tailTrace_3213006
  have hstable : (prefixWord ++ tailWord_3213006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213006).length < 2 ^ (prefixWord ++ tailWord_3213006).sum := by decide
  have hdescent : baseEnd_3213006 < baseStart_3213006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213034 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_3213034 : Nat := 118140960795 + 3213034 * 2 ^ 59
def prefixEnd_3213034 : Nat := 4983230072969 + 3 ^ 40 * 3213034 * 2
def baseEnd_3213034 : Nat := 1099887200825524815599021

theorem tailTrace_3213034 : CollatzResearch.WordTrace tailWord_3213034 prefixEnd_3213034 1099887200825524815599021 := by
  unfold tailWord_3213034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29297244360433508841171539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78125984961156023576457437 29297244360433508841171539)
  ·
    refine ⟨43945866540650263261757309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29297244360433508841171539 43945866540650263261757309)
    ·
      refine ⟨16479699952743848723158991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43945866540650263261757309 16479699952743848723158991)
      ·
        refine ⟨24719549929115773084738487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16479699952743848723158991 24719549929115773084738487)
        ·
          refine ⟨37079324893673659627107731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24719549929115773084738487 37079324893673659627107731)
          ·
            refine ⟨55618987340510489440661597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37079324893673659627107731 55618987340510489440661597)
            ·
              refine ⟨20857120252691433540248099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55618987340510489440661597 20857120252691433540248099)
              ·
                refine ⟨31285680379037150310372149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20857120252691433540248099 31285680379037150310372149)
                ·
                  refine ⟨2933032535534732841597389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31285680379037150310372149 2933032535534732841597389)
                  ·
                    refine ⟨1099887200825524815599021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2933032535534732841597389 1099887200825524815599021)
                    ·
                      rfl

theorem cell22_3213034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_3213034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213034 prefixEnd_3213034 := by exact prefixLift 3213034
  have htrace : WordTrace (prefixWord ++ tailWord_3213034) baseStart_3213034 baseEnd_3213034 := by
    simpa [prefixWord, tailWord_3213034, baseEnd_3213034] using wordTrace_append hprefix tailTrace_3213034
  have hstable : (prefixWord ++ tailWord_3213034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213034).length < 2 ^ (prefixWord ++ tailWord_3213034).sum := by decide
  have hdescent : baseEnd_3213034 < baseStart_3213034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213079 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 2, 5]
def baseStart_3213079 : Nat := 118140960795 + 3213079 * 2 ^ 59
def prefixEnd_3213079 : Nat := 4983230072969 + 3 ^ 40 * 3213079 * 2
def baseEnd_3213079 : Nat := 1099902605245159698223883

theorem tailTrace_3213079 : CollatzResearch.WordTrace tailWord_3213079 prefixEnd_3213079 1099902605245159698223883 := by
  unfold tailWord_3213079
  simp only [CollatzResearch.WordTrace]
  refine ⟨117190618726571008050074291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78127079151047338700049527 117190618726571008050074291)
  ·
    refine ⟨175785928089856512075111437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117190618726571008050074291 175785928089856512075111437)
    ·
      refine ⟨65919723033696192028166789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175785928089856512075111437 65919723033696192028166789)
      ·
        refine ⟨12359948068818036005281273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65919723033696192028166789 12359948068818036005281273)
        ·
          refine ⟨9269961051613527003960955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12359948068818036005281273 9269961051613527003960955)
          ·
            refine ⟨13904941577420290505941433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9269961051613527003960955 13904941577420290505941433)
            ·
              refine ⟨10428706183065217879456075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13904941577420290505941433 10428706183065217879456075)
              ·
                refine ⟨15643059274597826819184113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10428706183065217879456075 15643059274597826819184113)
                ·
                  refine ⟨11732294455948370114388085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15643059274597826819184113 11732294455948370114388085)
                  ·
                    refine ⟨1099902605245159698223883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11732294455948370114388085 1099902605245159698223883)
                    ·
                      rfl

theorem cell22_3213079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_3213079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213079 prefixEnd_3213079 := by exact prefixLift 3213079
  have htrace : WordTrace (prefixWord ++ tailWord_3213079) baseStart_3213079 baseEnd_3213079 := by
    simpa [prefixWord, tailWord_3213079, baseEnd_3213079] using wordTrace_append hprefix tailTrace_3213079
  have hstable : (prefixWord ++ tailWord_3213079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213079).length < 2 ^ (prefixWord ++ tailWord_3213079).sum := by decide
  have hdescent : baseEnd_3213079 < baseStart_3213079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213102 : List Nat := [4, 1, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3213102 : Nat := 118140960795 + 3213102 * 2 ^ 59
def prefixEnd_3213102 : Nat := 4983230072969 + 3 ^ 40 * 3213102 * 2
def baseEnd_3213102 : Nat := 1099910478615195304898813

theorem tailTrace_3213102 : CollatzResearch.WordTrace tailWord_3213102 prefixEnd_3213102 1099910478615195304898813 := by
  unfold tailWord_3213102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14648932200685960372270195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78127638403658455318774373 14648932200685960372270195)
  ·
    refine ⟨21973398301028940558405293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14648932200685960372270195 21973398301028940558405293)
    ·
      refine ⟨8240024362885852709401985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21973398301028940558405293 8240024362885852709401985)
      ·
        refine ⟨6180018272164389532051489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8240024362885852709401985 6180018272164389532051489)
        ·
          refine ⟨4635013704123292149038617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6180018272164389532051489 4635013704123292149038617)
          ·
            refine ⟨3476260278092469111778963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4635013704123292149038617 3476260278092469111778963)
            ·
              refine ⟨5214390417138703667668445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476260278092469111778963 5214390417138703667668445)
              ·
                refine ⟨1955396406427013875375667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5214390417138703667668445 1955396406427013875375667)
                ·
                  refine ⟨2933094609640520813063501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955396406427013875375667 2933094609640520813063501)
                  ·
                    refine ⟨1099910478615195304898813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2933094609640520813063501 1099910478615195304898813)
                    ·
                      rfl

theorem cell22_3213102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3213102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213102 prefixEnd_3213102 := by exact prefixLift 3213102
  have htrace : WordTrace (prefixWord ++ tailWord_3213102) baseStart_3213102 baseEnd_3213102 := by
    simpa [prefixWord, tailWord_3213102, baseEnd_3213102] using wordTrace_append hprefix tailTrace_3213102
  have hstable : (prefixWord ++ tailWord_3213102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213102).length < 2 ^ (prefixWord ++ tailWord_3213102).sum := by decide
  have hdescent : baseEnd_3213102 < baseStart_3213102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213220 : List Nat := [2, 3, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_3213220 : Nat := 118140960795 + 3213220 * 2 ^ 59
def prefixEnd_3213220 : Nat := 4983230072969 + 3 ^ 40 * 3213220 * 2
def baseEnd_3213220 : Nat := 1099950872426682330448451

theorem tailTrace_3213220 : CollatzResearch.WordTrace tailWord_3213220 prefixEnd_3213220 1099950872426682330448451 := by
  unfold tailWord_3213220
  simp only [CollatzResearch.WordTrace]
  refine ⟨58597880709530094565478557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78130507612706792753971409 58597880709530094565478557)
  ·
    refine ⟨21974205266073785462054459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58597880709530094565478557 21974205266073785462054459)
    ·
      refine ⟨32961307899110678193081689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21974205266073785462054459 32961307899110678193081689)
      ·
        refine ⟨24720980924333008644811267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32961307899110678193081689 24720980924333008644811267)
        ·
          refine ⟨37081471386499512967216901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24720980924333008644811267 37081471386499512967216901)
          ·
            refine ⟨6952775884968658681353169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37081471386499512967216901 6952775884968658681353169)
            ·
              refine ⟨5214581913726494011014877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6952775884968658681353169 5214581913726494011014877)
              ·
                refine ⟨1955468217647435254130579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5214581913726494011014877 1955468217647435254130579)
                ·
                  refine ⟨2933202326471152881195869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955468217647435254130579 2933202326471152881195869)
                  ·
                    refine ⟨1099950872426682330448451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2933202326471152881195869 1099950872426682330448451)
                    ·
                      rfl

theorem cell22_3213220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_3213220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213220 prefixEnd_3213220 := by exact prefixLift 3213220
  have htrace : WordTrace (prefixWord ++ tailWord_3213220) baseStart_3213220 baseEnd_3213220 := by
    simpa [prefixWord, tailWord_3213220, baseEnd_3213220] using wordTrace_append hprefix tailTrace_3213220
  have hstable : (prefixWord ++ tailWord_3213220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213220).length < 2 ^ (prefixWord ++ tailWord_3213220).sum := by decide
  have hdescent : baseEnd_3213220 < baseStart_3213220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213233 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 5]
def baseStart_3213233 : Nat := 118140960795 + 3213233 * 2 ^ 59
def prefixEnd_3213233 : Nat := 4983230072969 + 3 ^ 40 * 3213233 * 2
def baseEnd_3213233 : Nat := 366651774197451543291137

theorem tailTrace_3213233 : CollatzResearch.WordTrace tailWord_3213233 prefixEnd_3213233 366651774197451543291137 := by
  unfold tailWord_3213233
  simp only [CollatzResearch.WordTrace]
  refine ⟨117196235568013092351180353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78130823712008728234120235 117196235568013092351180353)
  ·
    refine ⟨87897176676009819263385265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117196235568013092351180353 87897176676009819263385265)
    ·
      refine ⟨65922882507007364447538949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87897176676009819263385265 65922882507007364447538949)
      ·
        refine ⟨12360540470063880833913553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65922882507007364447538949 12360540470063880833913553)
        ·
          refine ⟨9270405352547910625435165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12360540470063880833913553 9270405352547910625435165)
          ·
            refine ⟨3476402007205466484538187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9270405352547910625435165 3476402007205466484538187)
            ·
              refine ⟨5214603010808199726807281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476402007205466484538187 5214603010808199726807281)
              ·
                refine ⟨3910952258106149795105461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5214603010808199726807281 3910952258106149795105461)
                ·
                  refine ⟨366651774197451543291137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3910952258106149795105461 366651774197451543291137)
                  ·
                    rfl

theorem cell22_3213233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_3213233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213233 prefixEnd_3213233 := by exact prefixLift 3213233
  have htrace : WordTrace (prefixWord ++ tailWord_3213233) baseStart_3213233 baseEnd_3213233 := by
    simpa [prefixWord, tailWord_3213233, baseEnd_3213233] using wordTrace_append hprefix tailTrace_3213233
  have hstable : (prefixWord ++ tailWord_3213233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213233).length < 2 ^ (prefixWord ++ tailWord_3213233).sum := by decide
  have hdescent : baseEnd_3213233 < baseStart_3213233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213396 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 10]
def baseStart_3213396 : Nat := 118140960795 + 3213396 * 2 ^ 59
def prefixEnd_3213396 : Nat := 4983230072969 + 3 ^ 40 * 3213396 * 2
def baseEnd_3213396 : Nat := 366670373607825512682637

theorem tailTrace_3213396 : CollatzResearch.WordTrace tailWord_3213396 prefixEnd_3213396 366670373607825512682637 := by
  unfold tailWord_3213396
  simp only [CollatzResearch.WordTrace]
  refine ⟨58601090333211285594682021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78134787110948380792909361 58601090333211285594682021)
  ·
    refine ⟨10987704437477116049002879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58601090333211285594682021 10987704437477116049002879)
    ·
      refine ⟨16481556656215674073504319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10987704437477116049002879 16481556656215674073504319)
      ·
        refine ⟨24722334984323511110256479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16481556656215674073504319 24722334984323511110256479)
        ·
          refine ⟨37083502476485266665384719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24722334984323511110256479 37083502476485266665384719)
          ·
            refine ⟨55625253714727899998077079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37083502476485266665384719 55625253714727899998077079)
            ·
              refine ⟨83437880572091849997115619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55625253714727899998077079 83437880572091849997115619)
              ·
                refine ⟨125156820858137774995673429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83437880572091849997115619 125156820858137774995673429)
                ·
                  refine ⟨366670373607825512682637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 125156820858137774995673429 366670373607825512682637)
                  ·
                    rfl

theorem cell22_3213396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_3213396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213396 prefixEnd_3213396 := by exact prefixLift 3213396
  have htrace : WordTrace (prefixWord ++ tailWord_3213396) baseStart_3213396 baseEnd_3213396 := by
    simpa [prefixWord, tailWord_3213396, baseEnd_3213396] using wordTrace_append hprefix tailTrace_3213396
  have hstable : (prefixWord ++ tailWord_3213396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213396).length < 2 ^ (prefixWord ++ tailWord_3213396).sum := by decide
  have hdescent : baseEnd_3213396 < baseStart_3213396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213411 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 3, 5]
def baseStart_3213411 : Nat := 118140960795 + 3213411 * 2 ^ 59
def prefixEnd_3213411 : Nat := 4983230072969 + 3 ^ 40 * 3213411 * 2
def baseEnd_3213411 : Nat := 1100016255630021498922865

theorem tailTrace_3213411 : CollatzResearch.WordTrace tailWord_3213411 prefixEnd_3213411 1100016255630021498922865 := by
  unfold tailWord_3213411
  simp only [CollatzResearch.WordTrace]
  refine ⟨117202727761368228751160087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78135151840912152500773391 117202727761368228751160087)
  ·
    refine ⟨175804091642052343126740131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117202727761368228751160087 175804091642052343126740131)
    ·
      refine ⟨263706137463078514690110197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175804091642052343126740131 263706137463078514690110197)
      ·
        refine ⟨24722450387163610752197831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263706137463078514690110197 24722450387163610752197831)
        ·
          refine ⟨37083675580745416128296747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24722450387163610752197831 37083675580745416128296747)
          ·
            refine ⟨55625513371118124192445121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37083675580745416128296747 55625513371118124192445121)
            ·
              refine ⟨41719135028338593144333841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55625513371118124192445121 41719135028338593144333841)
              ·
                refine ⟨31289351271253944858250381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41719135028338593144333841 31289351271253944858250381)
                ·
                  refine ⟨11733506726720229321843893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31289351271253944858250381 11733506726720229321843893)
                  ·
                    refine ⟨1100016255630021498922865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11733506726720229321843893 1100016255630021498922865)
                    ·
                      rfl

theorem cell22_3213411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_3213411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213411 prefixEnd_3213411 := by exact prefixLift 3213411
  have htrace : WordTrace (prefixWord ++ tailWord_3213411) baseStart_3213411 baseEnd_3213411 := by
    simpa [prefixWord, tailWord_3213411, baseEnd_3213411] using wordTrace_append hprefix tailTrace_3213411
  have hstable : (prefixWord ++ tailWord_3213411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213411).length < 2 ^ (prefixWord ++ tailWord_3213411).sum := by decide
  have hdescent : baseEnd_3213411 < baseStart_3213411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213413 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 6]
def baseStart_3213413 : Nat := 118140960795 + 3213413 * 2 ^ 59
def prefixEnd_3213413 : Nat := 4983230072969 + 3 ^ 40 * 3213413 * 2
def baseEnd_3213413 : Nat := 366672313423631386790953

theorem tailTrace_3213413 : CollatzResearch.WordTrace tailWord_3213413 prefixEnd_3213413 366672313423631386790953 := by
  unfold tailWord_3213413
  simp only [CollatzResearch.WordTrace]
  refine ⟨117202800707360983092732893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78135200471573988728488595 117202800707360983092732893)
  ·
    refine ⟨43951050265260368659774835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117202800707360983092732893 43951050265260368659774835)
    ·
      refine ⟨65926575397890552989662253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43951050265260368659774835 65926575397890552989662253)
      ·
        refine ⟨24722465774208957371123345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65926575397890552989662253 24722465774208957371123345)
        ·
          refine ⟨18541849330656718028342509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24722465774208957371123345 18541849330656718028342509)
          ·
            refine ⟨6953193498996269260628441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18541849330656718028342509 6953193498996269260628441)
            ·
              refine ⟨5214895124247201945471331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6953193498996269260628441 5214895124247201945471331)
              ·
                refine ⟨7822342686370802918206997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5214895124247201945471331 7822342686370802918206997)
                ·
                  refine ⟨366672313423631386790953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7822342686370802918206997 366672313423631386790953)
                  ·
                    rfl

theorem cell22_3213413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_3213413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213413 prefixEnd_3213413 := by exact prefixLift 3213413
  have htrace : WordTrace (prefixWord ++ tailWord_3213413) baseStart_3213413 baseEnd_3213413 := by
    simpa [prefixWord, tailWord_3213413, baseEnd_3213413] using wordTrace_append hprefix tailTrace_3213413
  have hstable : (prefixWord ++ tailWord_3213413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213413).length < 2 ^ (prefixWord ++ tailWord_3213413).sum := by decide
  have hdescent : baseEnd_3213413 < baseStart_3213413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213548 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 6]
def baseStart_3213548 : Nat := 118140960795 + 3213548 * 2 ^ 59
def prefixEnd_3213548 : Nat := 4983230072969 + 3 ^ 40 * 3213548 * 2
def baseEnd_3213548 : Nat := 366687717843266269415815

theorem tailTrace_3213548 : CollatzResearch.WordTrace tailWord_3213548 prefixEnd_3213548 366687717843266269415815 := by
  unfold tailWord_3213548
  simp only [CollatzResearch.WordTrace]
  refine ⟨58603862280935950574448649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78138483041247934099264865 58603862280935950574448649)
  ·
    refine ⟨43952896710701962930836487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58603862280935950574448649 43952896710701962930836487)
    ·
      refine ⟨65929345066052944396254731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43952896710701962930836487 65929345066052944396254731)
      ·
        refine ⟨98894017599079416594382097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65929345066052944396254731 98894017599079416594382097)
        ·
          refine ⟨74170513199309562445786573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98894017599079416594382097 74170513199309562445786573)
          ·
            refine ⟨27813942449741085917169965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74170513199309562445786573 27813942449741085917169965)
            ·
              refine ⟨10430228418652907218938737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27813942449741085917169965 10430228418652907218938737)
              ·
                refine ⟨7822671313989680414204053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10430228418652907218938737 7822671313989680414204053)
                ·
                  refine ⟨366687717843266269415815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7822671313989680414204053 366687717843266269415815)
                  ·
                    rfl

theorem cell22_3213548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_3213548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213548 prefixEnd_3213548 := by exact prefixLift 3213548
  have htrace : WordTrace (prefixWord ++ tailWord_3213548) baseStart_3213548 baseEnd_3213548 := by
    simpa [prefixWord, tailWord_3213548, baseEnd_3213548] using wordTrace_append hprefix tailTrace_3213548
  have hstable : (prefixWord ++ tailWord_3213548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213548).length < 2 ^ (prefixWord ++ tailWord_3213548).sum := by decide
  have hdescent : baseEnd_3213548 < baseStart_3213548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213550 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3213550 : Nat := 118140960795 + 3213550 * 2 ^ 59
def prefixEnd_3213550 : Nat := 4983230072969 + 3 ^ 40 * 3213550 * 2
def baseEnd_3213550 : Nat := 1100063838170671469697439

theorem tailTrace_3213550 : CollatzResearch.WordTrace tailWord_3213550 prefixEnd_3213550 1100063838170671469697439 := by
  unfold tailWord_3213550
  simp only [CollatzResearch.WordTrace]
  refine ⟨14650974688483081936308763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78138531671909770326980069 14650974688483081936308763)
  ·
    refine ⟨21976462032724622904463145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14650974688483081936308763 21976462032724622904463145)
    ·
      refine ⟨16482346524543467178347359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21976462032724622904463145 16482346524543467178347359)
      ·
        refine ⟨24723519786815200767521039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16482346524543467178347359 24723519786815200767521039)
        ·
          refine ⟨37085279680222801151281559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24723519786815200767521039 37085279680222801151281559)
          ·
            refine ⟨55627919520334201726922339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37085279680222801151281559 55627919520334201726922339)
            ·
              refine ⟨83441879280501302590383509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55627919520334201726922339 83441879280501302590383509)
              ·
                refine ⟨3911338091273498558924227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83441879280501302590383509 3911338091273498558924227)
                ·
                  refine ⟨5867007136910247838386341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911338091273498558924227 5867007136910247838386341)
                  ·
                    refine ⟨1100063838170671469697439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5867007136910247838386341 1100063838170671469697439)
                    ·
                      rfl

theorem cell22_3213550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3213550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213550 prefixEnd_3213550 := by exact prefixLift 3213550
  have htrace : WordTrace (prefixWord ++ tailWord_3213550) baseStart_3213550 baseEnd_3213550 := by
    simpa [prefixWord, tailWord_3213550, baseEnd_3213550] using wordTrace_append hprefix tailTrace_3213550
  have hstable : (prefixWord ++ tailWord_3213550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213550).length < 2 ^ (prefixWord ++ tailWord_3213550).sum := by decide
  have hdescent : baseEnd_3213550 < baseStart_3213550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213580 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_3213580 : Nat := 118140960795 + 3213580 * 2 ^ 59
def prefixEnd_3213580 : Nat := 4983230072969 + 3 ^ 40 * 3213580 * 2
def baseEnd_3213580 : Nat := 1100074107783761391447347

theorem tailTrace_3213580 : CollatzResearch.WordTrace tailWord_3213580 prefixEnd_3213580 1100074107783761391447347 := by
  unfold tailWord_3213580
  simp only [CollatzResearch.WordTrace]
  refine ⟨58604445848877985307031097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78139261131837313742708129 58604445848877985307031097)
  ·
    refine ⟨43953334386658488980273323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58604445848877985307031097 43953334386658488980273323)
    ·
      refine ⟨65930001579987733470409985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43953334386658488980273323 65930001579987733470409985)
      ·
        refine ⟨49447501184990800102807489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65930001579987733470409985 49447501184990800102807489)
        ·
          refine ⟨37085625888743100077105617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49447501184990800102807489 37085625888743100077105617)
          ·
            refine ⟨27814219416557325057829213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37085625888743100077105617 27814219416557325057829213)
            ·
              refine ⟨10430332281208996896685955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27814219416557325057829213 10430332281208996896685955)
              ·
                refine ⟨15645498421813495345028933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10430332281208996896685955 15645498421813495345028933)
                ·
                  refine ⟨2933530954090030377192925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15645498421813495345028933 2933530954090030377192925)
                  ·
                    refine ⟨1100074107783761391447347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2933530954090030377192925 1100074107783761391447347)
                    ·
                      rfl

theorem cell22_3213580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_3213580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213580 prefixEnd_3213580 := by exact prefixLift 3213580
  have htrace : WordTrace (prefixWord ++ tailWord_3213580) baseStart_3213580 baseEnd_3213580 := by
    simpa [prefixWord, tailWord_3213580, baseEnd_3213580] using wordTrace_append hprefix tailTrace_3213580
  have hstable : (prefixWord ++ tailWord_3213580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213580).length < 2 ^ (prefixWord ++ tailWord_3213580).sum := by decide
  have hdescent : baseEnd_3213580 < baseStart_3213580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213655 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 5]
def baseStart_3213655 : Nat := 118140960795 + 3213655 * 2 ^ 59
def prefixEnd_3213655 : Nat := 4983230072969 + 3 ^ 40 * 3213655 * 2
def baseEnd_3213655 : Nat := 366699927272162065274039

theorem tailTrace_3213655 : CollatzResearch.WordTrace tailWord_3213655 prefixEnd_3213655 366699927272162065274039 := by
  unfold tailWord_3213655
  simp only [CollatzResearch.WordTrace]
  refine ⟨117211627172484258423042419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78141084781656172282028279 117211627172484258423042419)
  ·
    refine ⟨175817440758726387634563629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117211627172484258423042419 175817440758726387634563629)
    ·
      refine ⟨65931540284522395362961361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175817440758726387634563629 65931540284522395362961361)
      ·
        refine ⟨49448655213391796522221021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65931540284522395362961361 49448655213391796522221021)
        ·
          refine ⟨18543245705021923695832883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49448655213391796522221021 18543245705021923695832883)
          ·
            refine ⟨27814868557532885543749325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18543245705021923695832883 27814868557532885543749325)
            ·
              refine ⟨10430575709074832078905997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27814868557532885543749325 10430575709074832078905997)
              ·
                refine ⟨3911465890903062029589749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10430575709074832078905997 3911465890903062029589749)
                ·
                  refine ⟨366699927272162065274039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3911465890903062029589749 366699927272162065274039)
                  ·
                    rfl

theorem cell22_3213655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 5].length) (baseStart_3213655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213655 prefixEnd_3213655 := by exact prefixLift 3213655
  have htrace : WordTrace (prefixWord ++ tailWord_3213655) baseStart_3213655 baseEnd_3213655 := by
    simpa [prefixWord, tailWord_3213655, baseEnd_3213655] using wordTrace_append hprefix tailTrace_3213655
  have hstable : (prefixWord ++ tailWord_3213655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213655).length < 2 ^ (prefixWord ++ tailWord_3213655).sum := by decide
  have hdescent : baseEnd_3213655 < baseStart_3213655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213683 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 8]
def baseStart_3213683 : Nat := 118140960795 + 3213683 * 2 ^ 59
def prefixEnd_3213683 : Nat := 4983230072969 + 3 ^ 40 * 3213683 * 2
def baseEnd_3213683 : Nat := 366703122262901152040677

theorem tailTrace_3213683 : CollatzResearch.WordTrace tailWord_3213683 prefixEnd_3213683 366703122262901152040677 := by
  unfold tailWord_3213683
  simp only [CollatzResearch.WordTrace]
  refine ⟨117212648416382819205061703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78141765610921879470041135 117212648416382819205061703)
  ·
    refine ⟨175818972624574228807592555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117212648416382819205061703 175818972624574228807592555)
    ·
      refine ⟨263728458936861343211388833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175818972624574228807592555 263728458936861343211388833)
      ·
        refine ⟨197796344202646007408541625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263728458936861343211388833 197796344202646007408541625)
        ·
          refine ⟨148347258151984505556406219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197796344202646007408541625 148347258151984505556406219)
          ·
            refine ⟨222520887227976758334609329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148347258151984505556406219 222520887227976758334609329)
            ·
              refine ⟨166890665420982568750956997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222520887227976758334609329 166890665420982568750956997)
              ·
                refine ⟨31291999766434231640804437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166890665420982568750956997 31291999766434231640804437)
                ·
                  refine ⟨366703122262901152040677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31291999766434231640804437 366703122262901152040677)
                  ·
                    rfl

theorem cell22_3213683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 8].length) (baseStart_3213683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213683 prefixEnd_3213683 := by exact prefixLift 3213683
  have htrace : WordTrace (prefixWord ++ tailWord_3213683) baseStart_3213683 baseEnd_3213683 := by
    simpa [prefixWord, tailWord_3213683, baseEnd_3213683] using wordTrace_append hprefix tailTrace_3213683
  have hstable : (prefixWord ++ tailWord_3213683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213683).length < 2 ^ (prefixWord ++ tailWord_3213683).sum := by decide
  have hdescent : baseEnd_3213683 < baseStart_3213683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213700 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 6]
def baseStart_3213700 : Nat := 118140960795 + 3213700 * 2 ^ 59
def prefixEnd_3213700 : Nat := 4983230072969 + 3 ^ 40 * 3213700 * 2
def baseEnd_3213700 : Nat := 366705062078707026148993

theorem tailTrace_3213700 : CollatzResearch.WordTrace tailWord_3213700 prefixEnd_3213700 366705062078707026148993 := by
  unfold tailWord_3213700
  simp only [CollatzResearch.WordTrace]
  refine ⟨58606634228660615554215277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78142178971547487405620369 58606634228660615554215277)
  ·
    refine ⟨21977487835747730832830729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58606634228660615554215277 21977487835747730832830729)
    ·
      refine ⟨16483115876810798124623047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21977487835747730832830729 16483115876810798124623047)
      ·
        refine ⟨24724673815216197186934571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16483115876810798124623047 24724673815216197186934571)
        ·
          refine ⟨37087010722824295780401857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24724673815216197186934571 37087010722824295780401857)
          ·
            refine ⟨27815258042118221835301393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37087010722824295780401857 27815258042118221835301393)
            ·
              refine ⟨20861443531588666376476045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27815258042118221835301393 20861443531588666376476045)
              ·
                refine ⟨7823041324345749891178517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20861443531588666376476045 7823041324345749891178517)
                ·
                  refine ⟨366705062078707026148993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7823041324345749891178517 366705062078707026148993)
                  ·
                    rfl

theorem cell22_3213700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_3213700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213700 prefixEnd_3213700 := by exact prefixLift 3213700
  have htrace : WordTrace (prefixWord ++ tailWord_3213700) baseStart_3213700 baseEnd_3213700 := by
    simpa [prefixWord, tailWord_3213700, baseEnd_3213700] using wordTrace_append hprefix tailTrace_3213700
  have hstable : (prefixWord ++ tailWord_3213700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213700).length < 2 ^ (prefixWord ++ tailWord_3213700).sum := by decide
  have hdescent : baseEnd_3213700 < baseStart_3213700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213736 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3213736 : Nat := 118140960795 + 3213736 * 2 ^ 59
def prefixEnd_3213736 : Nat := 4983230072969 + 3 ^ 40 * 3213736 * 2
def baseEnd_3213736 : Nat := 1100127509771828984546869

theorem tailTrace_3213736 : CollatzResearch.WordTrace tailWord_3213736 prefixEnd_3213736 1100127509771828984546869 := by
  unfold tailWord_3213736
  simp only [CollatzResearch.WordTrace]
  refine ⟨58607290742595404628370531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78143054323460539504494041 58607290742595404628370531)
  ·
    refine ⟨87910936113893106942555797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58607290742595404628370531 87910936113893106942555797)
    ·
      refine ⟨4120825130338739387932303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87910936113893106942555797 4120825130338739387932303)
      ·
        refine ⟨6181237695508109081898455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4120825130338739387932303 6181237695508109081898455)
        ·
          refine ⟨9271856543262163622847683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6181237695508109081898455 9271856543262163622847683)
          ·
            refine ⟨13907784814893245434271525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9271856543262163622847683 13907784814893245434271525)
            ·
              refine ⟨2607709652792483518925911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13907784814893245434271525 2607709652792483518925911)
              ·
                refine ⟨3911564479188725278388867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607709652792483518925911 3911564479188725278388867)
                ·
                  refine ⟨5867346718783087917583301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911564479188725278388867 5867346718783087917583301)
                  ·
                    refine ⟨1100127509771828984546869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5867346718783087917583301 1100127509771828984546869)
                    ·
                      rfl

theorem cell22_3213736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3213736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213736 prefixEnd_3213736 := by exact prefixLift 3213736
  have htrace : WordTrace (prefixWord ++ tailWord_3213736) baseStart_3213736 baseEnd_3213736 := by
    simpa [prefixWord, tailWord_3213736, baseEnd_3213736] using wordTrace_append hprefix tailTrace_3213736
  have hstable : (prefixWord ++ tailWord_3213736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213736).length < 2 ^ (prefixWord ++ tailWord_3213736).sum := by decide
  have hdescent : baseEnd_3213736 < baseStart_3213736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213745 : List Nat := [1, 2, 2, 4, 1, 3, 9]
def baseStart_3213745 : Nat := 118140960795 + 3213745 * 2 ^ 59
def prefixEnd_3213745 : Nat := 4983230072969 + 3 ^ 40 * 3213745 * 2
def baseEnd_3213745 : Nat := 40745577431694665224883

theorem tailTrace_3213745 : CollatzResearch.WordTrace tailWord_3213745 prefixEnd_3213745 40745577431694665224883 := by
  unfold tailWord_3213745
  simp only [CollatzResearch.WordTrace]
  refine ⟨117214909742158203793818689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78143273161438802529212459 117214909742158203793818689)
  ·
    refine ⟨87911182306618652845364017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117214909742158203793818689 87911182306618652845364017)
    ·
      refine ⟨65933386729963989634023013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87911182306618652845364017 65933386729963989634023013)
      ·
        refine ⟨12362510011868248056379315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65933386729963989634023013 12362510011868248056379315)
        ·
          refine ⟨18543765017802372084568973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12362510011868248056379315 18543765017802372084568973)
          ·
            refine ⟨6953911881675889531713365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18543765017802372084568973 6953911881675889531713365)
            ·
              refine ⟨40745577431694665224883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6953911881675889531713365 40745577431694665224883)
              ·
                rfl

theorem cell22_3213745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 9].length) (baseStart_3213745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213745 prefixEnd_3213745 := by exact prefixLift 3213745
  have htrace : WordTrace (prefixWord ++ tailWord_3213745) baseStart_3213745 baseEnd_3213745 := by
    simpa [prefixWord, tailWord_3213745, baseEnd_3213745] using wordTrace_append hprefix tailTrace_3213745
  have hstable : (prefixWord ++ tailWord_3213745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213745).length < 2 ^ (prefixWord ++ tailWord_3213745).sum := by decide
  have hdescent : baseEnd_3213745 < baseStart_3213745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213749 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_3213749 : Nat := 118140960795 + 3213749 * 2 ^ 59
def prefixEnd_3213749 : Nat := 4983230072969 + 3 ^ 40 * 3213749 * 2
def baseEnd_3213749 : Nat := 1100131959937501283971829

theorem tailTrace_3213749 : CollatzResearch.WordTrace tailWord_3213749 prefixEnd_3213749 1100131959937501283971829 := by
  unfold tailWord_3213749
  simp only [CollatzResearch.WordTrace]
  refine ⟨117215055634143712476964301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78143370422762474984642867 117215055634143712476964301)
  ·
    refine ⟨43955645862803892178861613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117215055634143712476964301 43955645862803892178861613)
    ·
      refine ⟨16483367198551459567073105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43955645862803892178861613 16483367198551459567073105)
      ·
        refine ⟨12362525398913594675304829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16483367198551459567073105 12362525398913594675304829)
        ·
          refine ⟨4635947024592598003239311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12362525398913594675304829 4635947024592598003239311)
          ·
            refine ⟨6953920536888897004858967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635947024592598003239311 6953920536888897004858967)
            ·
              refine ⟨10430880805333345507288451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953920536888897004858967 10430880805333345507288451)
              ·
                refine ⟨15646321208000018260932677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10430880805333345507288451 15646321208000018260932677)
                ·
                  refine ⟨2933685226500003423924877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15646321208000018260932677 2933685226500003423924877)
                  ·
                    refine ⟨1100131959937501283971829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2933685226500003423924877 1100131959937501283971829)
                    ·
                      rfl

theorem cell22_3213749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_3213749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213749 prefixEnd_3213749 := by exact prefixLift 3213749
  have htrace : WordTrace (prefixWord ++ tailWord_3213749) baseStart_3213749 baseEnd_3213749 := by
    simpa [prefixWord, tailWord_3213749, baseEnd_3213749] using wordTrace_append hprefix tailTrace_3213749
  have hstable : (prefixWord ++ tailWord_3213749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213749).length < 2 ^ (prefixWord ++ tailWord_3213749).sum := by decide
  have hdescent : baseEnd_3213749 < baseStart_3213749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213811 : List Nat := [1, 1, 1, 2, 2, 2, 7, 2, 1, 3]
def baseStart_3213811 : Nat := 118140960795 + 3213811 * 2 ^ 59
def prefixEnd_3213811 : Nat := 4983230072969 + 3 ^ 40 * 3213811 * 2
def baseEnd_3213811 : Nat := 1100153183804553788921639

theorem tailTrace_3213811 : CollatzResearch.WordTrace tailWord_3213811 prefixEnd_3213811 1100153183804553788921639 := by
  unfold tailWord_3213811
  simp only [CollatzResearch.WordTrace]
  refine ⟨117217316959919097065721287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78144877973279398043814191 117217316959919097065721287)
  ·
    refine ⟨175825975439878645598581931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117217316959919097065721287 175825975439878645598581931)
    ·
      refine ⟨263738963159817968397872897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175825975439878645598581931 263738963159817968397872897)
      ·
        refine ⟨197804222369863476298404673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263738963159817968397872897 197804222369863476298404673)
        ·
          refine ⟨148353166777397607223803505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197804222369863476298404673 148353166777397607223803505)
          ·
            refine ⟨111264875083048205417852629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148353166777397607223803505 111264875083048205417852629)
            ·
              refine ⟨2607770509758942314480921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 111264875083048205417852629 2607770509758942314480921)
              ·
                refine ⟨1955827882319206735860691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607770509758942314480921 1955827882319206735860691)
                ·
                  refine ⟨2933741823478810103791037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955827882319206735860691 2933741823478810103791037)
                  ·
                    refine ⟨1100153183804553788921639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2933741823478810103791037 1100153183804553788921639)
                    ·
                      rfl

theorem cell22_3213811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 1, 3].length) (baseStart_3213811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213811 prefixEnd_3213811 := by exact prefixLift 3213811
  have htrace : WordTrace (prefixWord ++ tailWord_3213811) baseStart_3213811 baseEnd_3213811 := by
    simpa [prefixWord, tailWord_3213811, baseEnd_3213811] using wordTrace_append hprefix tailTrace_3213811
  have hstable : (prefixWord ++ tailWord_3213811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213811).length < 2 ^ (prefixWord ++ tailWord_3213811).sum := by decide
  have hdescent : baseEnd_3213811 < baseStart_3213811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213820 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_3213820 : Nat := 118140960795 + 3213820 * 2 ^ 59
def prefixEnd_3213820 : Nat := 4983230072969 + 3 ^ 40 * 3213820 * 2
def baseEnd_3213820 : Nat := 1100156264688480765446611

theorem tailTrace_3213820 : CollatzResearch.WordTrace tailWord_3213820 prefixEnd_3213820 1100156264688480765446611 := by
  unfold tailWord_3213820
  simp only [CollatzResearch.WordTrace]
  refine ⟨58608822608443245801399457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78145096811257661068532609 58608822608443245801399457)
  ·
    refine ⟨43956616956332434351049593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58608822608443245801399457 43956616956332434351049593)
    ·
      refine ⟨32967462717249325763287195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43956616956332434351049593 32967462717249325763287195)
      ·
        refine ⟨49451194075873988644930793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32967462717249325763287195 49451194075873988644930793)
        ·
          refine ⟨37088395556905491483698095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49451194075873988644930793 37088395556905491483698095)
          ·
            refine ⟨55632593335358237225547143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37088395556905491483698095 55632593335358237225547143)
            ·
              refine ⟨83448890003037355838320715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55632593335358237225547143 83448890003037355838320715)
              ·
                refine ⟨125173335004556033757481073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83448890003037355838320715 125173335004556033757481073)
                ·
                  refine ⟨93880001253417025318110805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125173335004556033757481073 93880001253417025318110805)
                  ·
                    refine ⟨1100156264688480765446611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93880001253417025318110805 1100156264688480765446611)
                    ·
                      rfl

theorem cell22_3213820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_3213820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213820 prefixEnd_3213820 := by exact prefixLift 3213820
  have htrace : WordTrace (prefixWord ++ tailWord_3213820) baseStart_3213820 baseEnd_3213820 := by
    simpa [prefixWord, tailWord_3213820, baseEnd_3213820] using wordTrace_append hprefix tailTrace_3213820
  have hstable : (prefixWord ++ tailWord_3213820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213820).length < 2 ^ (prefixWord ++ tailWord_3213820).sum := by decide
  have hdescent : baseEnd_3213820 < baseStart_3213820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213867 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 4, 3]
def baseStart_3213867 : Nat := 118140960795 + 3213867 * 2 ^ 59
def prefixEnd_3213867 : Nat := 4983230072969 + 3 ^ 40 * 3213867 * 2
def baseEnd_3213867 : Nat := 1100172353748988309521467

theorem tailTrace_3213867 : CollatzResearch.WordTrace tailWord_3213867 prefixEnd_3213867 1100172353748988309521467 := by
  unfold tailWord_3213867
  simp only [CollatzResearch.WordTrace]
  refine ⟨117219359447716218629759855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78146239631810812419839903 117219359447716218629759855)
  ·
    refine ⟨175829039171574327944639783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117219359447716218629759855 175829039171574327944639783)
    ·
      refine ⟨263743558757361491916959675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175829039171574327944639783 263743558757361491916959675)
      ·
        refine ⟨395615338136042237875439513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263743558757361491916959675 395615338136042237875439513)
        ·
          refine ⟨296711503602031678406579635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395615338136042237875439513 296711503602031678406579635)
          ·
            refine ⟨445067255403047517609869453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296711503602031678406579635 445067255403047517609869453)
            ·
              refine ⟨166900220776142819103701045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445067255403047517609869453 166900220776142819103701045)
              ·
                refine ⟨15646895697763389290971973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166900220776142819103701045 15646895697763389290971973)
                ·
                  refine ⟨2933792943330635492057245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15646895697763389290971973 2933792943330635492057245)
                  ·
                    refine ⟨1100172353748988309521467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2933792943330635492057245 1100172353748988309521467)
                    ·
                      rfl

theorem cell22_3213867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 3].length) (baseStart_3213867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213867 prefixEnd_3213867 := by exact prefixLift 3213867
  have htrace : WordTrace (prefixWord ++ tailWord_3213867) baseStart_3213867 baseEnd_3213867 := by
    simpa [prefixWord, tailWord_3213867, baseEnd_3213867] using wordTrace_append hprefix tailTrace_3213867
  have hstable : (prefixWord ++ tailWord_3213867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213867).length < 2 ^ (prefixWord ++ tailWord_3213867).sum := by decide
  have hdescent : baseEnd_3213867 < baseStart_3213867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213884 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_3213884 : Nat := 118140960795 + 3213884 * 2 ^ 59
def prefixEnd_3213884 : Nat := 4983230072969 + 3 ^ 40 * 3213884 * 2
def baseEnd_3213884 : Nat := 1100178173196405931846415

theorem tailTrace_3213884 : CollatzResearch.WordTrace tailWord_3213884 prefixEnd_3213884 1100178173196405931846415 := by
  unfold tailWord_3213884
  simp only [CollatzResearch.WordTrace]
  refine ⟨58609989744327315266564353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78146652992436420355419137 58609989744327315266564353)
  ·
    refine ⟨43957492308245486449923265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58609989744327315266564353 43957492308245486449923265)
    ·
      refine ⟨32968119231184114837442449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43957492308245486449923265 32968119231184114837442449)
      ·
        refine ⟨24726089423388086128081837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32968119231184114837442449 24726089423388086128081837)
        ·
          refine ⟨9272283533770532298030689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24726089423388086128081837 9272283533770532298030689)
          ·
            refine ⟨6954212650327899223523017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9272283533770532298030689 6954212650327899223523017)
            ·
              refine ⟨5215659487745924417642263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6954212650327899223523017 5215659487745924417642263)
              ·
                refine ⟨7823489231618886626463395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5215659487745924417642263 7823489231618886626463395)
                ·
                  refine ⟨11735233847428329939695093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7823489231618886626463395 11735233847428329939695093)
                  ·
                    refine ⟨1100178173196405931846415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11735233847428329939695093 1100178173196405931846415)
                    ·
                      rfl

theorem cell22_3213884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_3213884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213884 prefixEnd_3213884 := by exact prefixLift 3213884
  have htrace : WordTrace (prefixWord ++ tailWord_3213884) baseStart_3213884 baseEnd_3213884 := by
    simpa [prefixWord, tailWord_3213884, baseEnd_3213884] using wordTrace_append hprefix tailTrace_3213884
  have hstable : (prefixWord ++ tailWord_3213884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213884).length < 2 ^ (prefixWord ++ tailWord_3213884).sum := by decide
  have hdescent : baseEnd_3213884 < baseStart_3213884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213886 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3213886 : Nat := 118140960795 + 3213886 * 2 ^ 59
def prefixEnd_3213886 : Nat := 4983230072969 + 3 ^ 40 * 3213886 * 2
def baseEnd_3213886 : Nat := 366726285945759531098803

theorem tailTrace_3213886 : CollatzResearch.WordTrace tailWord_3213886 prefixEnd_3213886 366726285945759531098803 := by
  unfold tailWord_3213886
  simp only [CollatzResearch.WordTrace]
  refine ⟨14652506554330923109337689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78146701623098256583134341 14652506554330923109337689)
  ·
    refine ⟨10989379915748192332003267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14652506554330923109337689 10989379915748192332003267)
    ·
      refine ⟨16484069873622288498004901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10989379915748192332003267 16484069873622288498004901)
      ·
        refine ⟨3090763101304179093375919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16484069873622288498004901 3090763101304179093375919)
        ·
          refine ⟨4636144651956268640063879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090763101304179093375919 4636144651956268640063879)
          ·
            refine ⟨6954216977934402960095819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636144651956268640063879 6954216977934402960095819)
            ·
              refine ⟨10431325466901604440143729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6954216977934402960095819 10431325466901604440143729)
              ·
                refine ⟨7823494100176203330107797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10431325466901604440143729 7823494100176203330107797)
                ·
                  refine ⟨366726285945759531098803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7823494100176203330107797 366726285945759531098803)
                  ·
                    rfl

theorem cell22_3213886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3213886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213886 prefixEnd_3213886 := by exact prefixLift 3213886
  have htrace : WordTrace (prefixWord ++ tailWord_3213886) baseStart_3213886 baseEnd_3213886 := by
    simpa [prefixWord, tailWord_3213886, baseEnd_3213886] using wordTrace_append hprefix tailTrace_3213886
  have hstable : (prefixWord ++ tailWord_3213886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213886).length < 2 ^ (prefixWord ++ tailWord_3213886).sum := by decide
  have hdescent : baseEnd_3213886 < baseStart_3213886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213954 : List Nat := [3, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_3213954 : Nat := 118140960795 + 3213954 * 2 ^ 59
def prefixEnd_3213954 : Nat := 4983230072969 + 3 ^ 40 * 3213954 * 2
def baseEnd_3213954 : Nat := 366734045208983027532067

theorem tailTrace_3213954 : CollatzResearch.WordTrace tailWord_3213954 prefixEnd_3213954 366734045208983027532067 := by
  unfold tailWord_3213954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29305633149600258122044229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78148355065600688325451277 29305633149600258122044229)
  ·
    refine ⟨5494806215550048397883293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29305633149600258122044229 5494806215550048397883293)
    ·
      refine ⟨2060552330831268149206235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5494806215550048397883293 2060552330831268149206235)
      ·
        refine ⟨3090828496246902223809353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060552330831268149206235 3090828496246902223809353)
        ·
          refine ⟨2318121372185176667857015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3090828496246902223809353 2318121372185176667857015)
          ·
            refine ⟨3477182058277765001785523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318121372185176667857015 3477182058277765001785523)
            ·
              refine ⟨5215773087416647502678285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477182058277765001785523 5215773087416647502678285)
              ·
                refine ⟨1955914907781242813504357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5215773087416647502678285 1955914907781242813504357)
                ·
                  refine ⟨366734045208983027532067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1955914907781242813504357 366734045208983027532067)
                  ·
                    rfl

theorem cell22_3213954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_3213954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213954 prefixEnd_3213954 := by exact prefixLift 3213954
  have htrace : WordTrace (prefixWord ++ tailWord_3213954) baseStart_3213954 baseEnd_3213954 := by
    simpa [prefixWord, tailWord_3213954, baseEnd_3213954] using wordTrace_append hprefix tailTrace_3213954
  have hstable : (prefixWord ++ tailWord_3213954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213954).length < 2 ^ (prefixWord ++ tailWord_3213954).sum := by decide
  have hdescent : baseEnd_3213954 < baseStart_3213954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213980 : List Nat := [2, 2, 3, 2, 2, 2, 3, 2, 1, 3]
def baseStart_3213980 : Nat := 118140960795 + 3213980 * 2 ^ 59
def prefixEnd_3213980 : Nat := 4983230072969 + 3 ^ 40 * 3213980 * 2
def baseEnd_3213980 : Nat := 1100211035958293681446121

theorem tailTrace_3213980 : CollatzResearch.WordTrace tailWord_3213980 prefixEnd_3213980 1100211035958293681446121 := by
  unfold tailWord_3213980
  simp only [CollatzResearch.WordTrace]
  refine ⟨58611740448153419464311697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78148987264204559285748929 58611740448153419464311697)
  ·
    refine ⟨43958805336115064598233773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58611740448153419464311697 43958805336115064598233773)
    ·
      refine ⟨16484552001043149224337665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43958805336115064598233773 16484552001043149224337665)
      ·
        refine ⟨12363414000782361918253249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16484552001043149224337665 12363414000782361918253249)
        ·
          refine ⟨9272560500586771438689937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12363414000782361918253249 9272560500586771438689937)
          ·
            refine ⟨6954420375440078579017453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9272560500586771438689937 6954420375440078579017453)
            ·
              refine ⟨2607907640790029467131545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6954420375440078579017453 2607907640790029467131545)
              ·
                refine ⟨1955930730592522100348659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607907640790029467131545 1955930730592522100348659)
                ·
                  refine ⟨2933896095888783150522989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955930730592522100348659 2933896095888783150522989)
                  ·
                    refine ⟨1100211035958293681446121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2933896095888783150522989 1100211035958293681446121)
                    ·
                      rfl

theorem cell22_3213980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_3213980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213980 prefixEnd_3213980 := by exact prefixLift 3213980
  have htrace : WordTrace (prefixWord ++ tailWord_3213980) baseStart_3213980 baseEnd_3213980 := by
    simpa [prefixWord, tailWord_3213980, baseEnd_3213980] using wordTrace_append hprefix tailTrace_3213980
  have hstable : (prefixWord ++ tailWord_3213980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213980).length < 2 ^ (prefixWord ++ tailWord_3213980).sum := by decide
  have hdescent : baseEnd_3213980 < baseStart_3213980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3213987 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 6]
def baseStart_3213987 : Nat := 118140960795 + 3213987 * 2 ^ 59
def prefixEnd_3213987 : Nat := 4983230072969 + 3 ^ 40 * 3213987 * 2
def baseEnd_3213987 : Nat := 366737810733782665507033

theorem tailTrace_3213987 : CollatzResearch.WordTrace tailWord_3213987 prefixEnd_3213987 366737810733782665507033 := by
  unfold tailWord_3213987
  simp only [CollatzResearch.WordTrace]
  refine ⟨117223736207281479124128215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78149157471520986082752143 117223736207281479124128215)
  ·
    refine ⟨175835604310922218686192323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117223736207281479124128215 175835604310922218686192323)
    ·
      refine ⟨263753406466383328029288485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175835604310922218686192323 263753406466383328029288485)
      ·
        refine ⟨49453763712446874005491591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263753406466383328029288485 49453763712446874005491591)
        ·
          refine ⟨74180645568670311008237387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49453763712446874005491591 74180645568670311008237387)
          ·
            refine ⟨111270968353005466512356081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74180645568670311008237387 111270968353005466512356081)
            ·
              refine ⟨83453226264754099884267061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111270968353005466512356081 83453226264754099884267061)
              ·
                refine ⟨7823739962320696864150037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83453226264754099884267061 7823739962320696864150037)
                ·
                  refine ⟨366737810733782665507033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7823739962320696864150037 366737810733782665507033)
                  ·
                    rfl

theorem cell22_3213987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 6].length) (baseStart_3213987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3213987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3213987 prefixEnd_3213987 := by exact prefixLift 3213987
  have htrace : WordTrace (prefixWord ++ tailWord_3213987) baseStart_3213987 baseEnd_3213987 := by
    simpa [prefixWord, tailWord_3213987, baseEnd_3213987] using wordTrace_append hprefix tailTrace_3213987
  have hstable : (prefixWord ++ tailWord_3213987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3213987).length < 2 ^ (prefixWord ++ tailWord_3213987).sum := by decide
  have hdescent : baseEnd_3213987 < baseStart_3213987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3213987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214049 : List Nat := [1, 2, 3, 1, 4, 1, 3, 7]
def baseStart_3214049 : Nat := 118140960795 + 3214049 * 2 ^ 59
def prefixEnd_3214049 : Nat := 4983230072969 + 3 ^ 40 * 3214049 * 2
def baseEnd_3214049 : Nat := 122248295118711166830101

theorem tailTrace_3214049 : CollatzResearch.WordTrace tailWord_3214049 prefixEnd_3214049 122248295118711166830101 := by
  unfold tailWord_3214049
  simp only [CollatzResearch.WordTrace]
  refine ⟨117225997533056863712885201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78150665022037909141923467 117225997533056863712885201)
  ·
    refine ⟨87919498149792647784663901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117225997533056863712885201 87919498149792647784663901)
    ·
      refine ⟨32969811806172242919248963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87919498149792647784663901 32969811806172242919248963)
      ·
        refine ⟨49454717709258364378873445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32969811806172242919248963 49454717709258364378873445)
        ·
          refine ⟨9272759570485943321038771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49454717709258364378873445 9272759570485943321038771)
          ·
            refine ⟨13909139355728914981558157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9272759570485943321038771 13909139355728914981558157)
            ·
              refine ⟨5215927258398343118084309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13909139355728914981558157 5215927258398343118084309)
              ·
                refine ⟨122248295118711166830101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5215927258398343118084309 122248295118711166830101)
                ·
                  rfl

theorem cell22_3214049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 7].length) (baseStart_3214049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214049 prefixEnd_3214049 := by exact prefixLift 3214049
  have htrace : WordTrace (prefixWord ++ tailWord_3214049) baseStart_3214049 baseEnd_3214049 := by
    simpa [prefixWord, tailWord_3214049, baseEnd_3214049] using wordTrace_append hprefix tailTrace_3214049
  have hstable : (prefixWord ++ tailWord_3214049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214049).length < 2 ^ (prefixWord ++ tailWord_3214049).sum := by decide
  have hdescent : baseEnd_3214049 < baseStart_3214049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214066 : List Nat := [3, 2, 1, 3, 1, 3, 3, 6]
def baseStart_3214066 : Nat := 118140960795 + 3214066 * 2 ^ 59
def prefixEnd_3214066 : Nat := 4983230072969 + 3 ^ 40 * 3214066 * 2
def baseEnd_3214066 : Nat := 122248941723979791532873

theorem tailTrace_3214066 : CollatzResearch.WordTrace tailWord_3214066 prefixEnd_3214066 122248941723979791532873 := by
  unfold tailWord_3214066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29306654393498818904063513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78151078382663517077502701 29306654393498818904063513)
  ·
    refine ⟨21979990795124114178047635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29306654393498818904063513 21979990795124114178047635)
    ·
      refine ⟨32969986192686171267071453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21979990795124114178047635 32969986192686171267071453)
      ·
        refine ⟨12363744822257314225151795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32969986192686171267071453 12363744822257314225151795)
        ·
          refine ⟨18545617233385971337727693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12363744822257314225151795 18545617233385971337727693)
          ·
            refine ⟨6954606462519739251647885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18545617233385971337727693 6954606462519739251647885)
            ·
              refine ⟨2607977423444902219367957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6954606462519739251647885 2607977423444902219367957)
              ·
                refine ⟨122248941723979791532873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2607977423444902219367957 122248941723979791532873)
                ·
                  rfl

theorem cell22_3214066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_3214066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214066 prefixEnd_3214066 := by exact prefixLift 3214066
  have htrace : WordTrace (prefixWord ++ tailWord_3214066) baseStart_3214066 baseEnd_3214066 := by
    simpa [prefixWord, tailWord_3214066, baseEnd_3214066] using wordTrace_append hprefix tailTrace_3214066
  have hstable : (prefixWord ++ tailWord_3214066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214066).length < 2 ^ (prefixWord ++ tailWord_3214066).sum := by decide
  have hdescent : baseEnd_3214066 < baseStart_3214066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214154 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_3214154 : Nat := 118140960795 + 3214154 * 2 ^ 59
def prefixEnd_3214154 : Nat := 4983230072969 + 3 ^ 40 * 3214154 * 2
def baseEnd_3214154 : Nat := 1100270599714215227595587

theorem tailTrace_3214154 : CollatzResearch.WordTrace tailWord_3214154 prefixEnd_3214154 1100270599714215227595587 := by
  unfold tailWord_3214154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29307456799419116661364379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78153218131784311096971677 29307456799419116661364379)
  ·
    refine ⟨43961185199128674992046569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29307456799419116661364379 43961185199128674992046569)
    ·
      refine ⟨32970888899346506244034927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43961185199128674992046569 32970888899346506244034927)
      ·
        refine ⟨49456333349019759366052391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32970888899346506244034927 49456333349019759366052391)
        ·
          refine ⟨74184500023529639049078587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49456333349019759366052391 74184500023529639049078587)
          ·
            refine ⟨111276750035294458573617881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74184500023529639049078587 111276750035294458573617881)
            ·
              refine ⟨83457562526470843930213411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111276750035294458573617881 83457562526470843930213411)
              ·
                refine ⟨125186343789706265895320117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83457562526470843930213411 125186343789706265895320117)
                ·
                  refine ⟨11736219730284962427686261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125186343789706265895320117 11736219730284962427686261)
                  ·
                    refine ⟨1100270599714215227595587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11736219730284962427686261 1100270599714215227595587)
                    ·
                      rfl

theorem cell22_3214154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_3214154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214154 prefixEnd_3214154 := by exact prefixLift 3214154
  have htrace : WordTrace (prefixWord ++ tailWord_3214154) baseStart_3214154 baseEnd_3214154 := by
    simpa [prefixWord, tailWord_3214154, baseEnd_3214154] using wordTrace_append hprefix tailTrace_3214154
  have hstable : (prefixWord ++ tailWord_3214154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214154).length < 2 ^ (prefixWord ++ tailWord_3214154).sum := by decide
  have hdescent : baseEnd_3214154 < baseStart_3214154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214156 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 6]
def baseStart_3214156 : Nat := 118140960795 + 3214156 * 2 ^ 59
def prefixEnd_3214156 : Nat := 4983230072969 + 3 ^ 40 * 3214156 * 2
def baseEnd_3214156 : Nat := 366757094785029296348527

theorem tailTrace_3214156 : CollatzResearch.WordTrace tailWord_3214156 prefixEnd_3214156 366757094785029296348527 := by
  unfold tailWord_3214156
  simp only [CollatzResearch.WordTrace]
  refine ⟨58614950071834610493515161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78153266762446147324686881 58614950071834610493515161)
  ·
    refine ⟨43961212553875957870136371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58614950071834610493515161 43961212553875957870136371)
    ·
      refine ⟨65941818830813936805204557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43961212553875957870136371 65941818830813936805204557)
      ·
        refine ⟨24728182061555226301951709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65941818830813936805204557 24728182061555226301951709)
        ·
          refine ⟨9273068273083209863231891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24728182061555226301951709 9273068273083209863231891)
          ·
            refine ⟨13909602409624814794847837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9273068273083209863231891 13909602409624814794847837)
            ·
              refine ⟨5216100903609305548067939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13909602409624814794847837 5216100903609305548067939)
              ·
                refine ⟨7824151355413958322101909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216100903609305548067939 7824151355413958322101909)
                ·
                  refine ⟨366757094785029296348527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7824151355413958322101909 366757094785029296348527)
                  ·
                    rfl

theorem cell22_3214156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_3214156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214156 prefixEnd_3214156 := by exact prefixLift 3214156
  have htrace : WordTrace (prefixWord ++ tailWord_3214156) baseStart_3214156 baseEnd_3214156 := by
    simpa [prefixWord, tailWord_3214156, baseEnd_3214156] using wordTrace_append hprefix tailTrace_3214156
  have hstable : (prefixWord ++ tailWord_3214156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214156).length < 2 ^ (prefixWord ++ tailWord_3214156).sum := by decide
  have hdescent : baseEnd_3214156 < baseStart_3214156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214218 : List Nat := [3, 1, 2, 4, 1, 3, 1, 7]
def baseStart_3214218 : Nat := 118140960795 + 3214218 * 2 ^ 59
def prefixEnd_3214218 : Nat := 4983230072969 + 3 ^ 40 * 3214218 * 2
def baseEnd_3214218 : Nat := 122254723135793377110599

theorem tailTrace_3214218 : CollatzResearch.WordTrace tailWord_3214218 prefixEnd_3214218 122254723135793377110599 := by
  unfold tailWord_3214218
  simp only [CollatzResearch.WordTrace]
  refine ⟨29308040367361151393946827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78154774312963070383858205 29308040367361151393946827)
  ·
    refine ⟨43962060551041727090920241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29308040367361151393946827 43962060551041727090920241)
    ·
      refine ⟨32971545413281295318190181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43962060551041727090920241 32971545413281295318190181)
      ·
        refine ⟨6182164764990242872160659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32971545413281295318190181 6182164764990242872160659)
        ·
          refine ⟨9273247147485364308240989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182164764990242872160659 9273247147485364308240989)
          ·
            refine ⟨3477467680307011615590371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9273247147485364308240989 3477467680307011615590371)
            ·
              refine ⟨5216201520460517423385557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477467680307011615590371 5216201520460517423385557)
              ·
                refine ⟨122254723135793377110599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5216201520460517423385557 122254723135793377110599)
                ·
                  rfl

theorem cell22_3214218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_3214218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214218 prefixEnd_3214218 := by exact prefixLift 3214218
  have htrace : WordTrace (prefixWord ++ tailWord_3214218) baseStart_3214218 baseEnd_3214218 := by
    simpa [prefixWord, tailWord_3214218, baseEnd_3214218] using wordTrace_append hprefix tailTrace_3214218
  have hstable : (prefixWord ++ tailWord_3214218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214218).length < 2 ^ (prefixWord ++ tailWord_3214218).sum := by decide
  have hdescent : baseEnd_3214218 < baseStart_3214218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214261 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3214261 : Nat := 118140960795 + 3214261 * 2 ^ 59
def prefixEnd_3214261 : Nat := 4983230072969 + 3 ^ 40 * 3214261 * 2
def baseEnd_3214261 : Nat := 1100307228000902615170259

theorem tailTrace_3214261 : CollatzResearch.WordTrace tailWord_3214261 prefixEnd_3214261 1100307228000902615170259 := by
  unfold tailWord_3214261
  simp only [CollatzResearch.WordTrace]
  refine ⟨117233729808288823919602637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78155819872192549279735091 117233729808288823919602637)
  ·
    refine ⟨43962648678108308969850989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117233729808288823919602637 43962648678108308969850989)
    ·
      refine ⟨16485993254290615863694121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43962648678108308969850989 16485993254290615863694121)
      ·
        refine ⟨12364494940717961897770591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16485993254290615863694121 12364494940717961897770591)
        ·
          refine ⟨18546742411076942846655887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12364494940717961897770591 18546742411076942846655887)
          ·
            refine ⟨27820113616615414269983831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18546742411076942846655887 27820113616615414269983831)
            ·
              refine ⟨41730170424923121404975747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27820113616615414269983831 41730170424923121404975747)
              ·
                refine ⟨62595255637384682107463621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41730170424923121404975747 62595255637384682107463621)
                ·
                  refine ⟨11736610432009627895149429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62595255637384682107463621 11736610432009627895149429)
                  ·
                    refine ⟨1100307228000902615170259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11736610432009627895149429 1100307228000902615170259)
                    ·
                      rfl

theorem cell22_3214261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3214261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214261 prefixEnd_3214261 := by exact prefixLift 3214261
  have htrace : WordTrace (prefixWord ++ tailWord_3214261) baseStart_3214261 baseEnd_3214261 := by
    simpa [prefixWord, tailWord_3214261, baseEnd_3214261] using wordTrace_append hprefix tailTrace_3214261
  have hstable : (prefixWord ++ tailWord_3214261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214261).length < 2 ^ (prefixWord ++ tailWord_3214261).sum := by decide
  have hdescent : baseEnd_3214261 < baseStart_3214261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214280 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 5]
def baseStart_3214280 : Nat := 118140960795 + 3214280 * 2 ^ 59
def prefixEnd_3214280 : Nat := 4983230072969 + 3 ^ 40 * 3214280 * 2
def baseEnd_3214280 : Nat := 366771244029730966315067

theorem tailTrace_3214280 : CollatzResearch.WordTrace tailWord_3214280 prefixEnd_3214280 366771244029730966315067 := by
  unfold tailWord_3214280
  simp only [CollatzResearch.WordTrace]
  refine ⟨58617211397609995082272147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78156281863479993443029529 58617211397609995082272147)
  ·
    refine ⟨87925817096414992623408221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58617211397609995082272147 87925817096414992623408221)
    ·
      refine ⟨32972181411155622233778083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87925817096414992623408221 32972181411155622233778083)
      ·
        refine ⟨49458272116733433350667125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32972181411155622233778083 49458272116733433350667125)
        ·
          refine ⟨4636713010943759376625043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49458272116733433350667125 4636713010943759376625043)
          ·
            refine ⟨6955069516415639064937565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636713010943759376625043 6955069516415639064937565)
            ·
              refine ⟨2608151068655864649351587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6955069516415639064937565 2608151068655864649351587)
              ·
                refine ⟨3912226602983796974027381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608151068655864649351587 3912226602983796974027381)
                ·
                  refine ⟨366771244029730966315067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3912226602983796974027381 366771244029730966315067)
                  ·
                    rfl

theorem cell22_3214280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 5].length) (baseStart_3214280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214280 prefixEnd_3214280 := by exact prefixLift 3214280
  have htrace : WordTrace (prefixWord ++ tailWord_3214280) baseStart_3214280 baseEnd_3214280 := by
    simpa [prefixWord, tailWord_3214280, baseEnd_3214280] using wordTrace_append hprefix tailTrace_3214280
  have hstable : (prefixWord ++ tailWord_3214280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214280).length < 2 ^ (prefixWord ++ tailWord_3214280).sum := by decide
  have hdescent : baseEnd_3214280 < baseStart_3214280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214308 : List Nat := [2, 3, 1, 1, 1, 1, 2, 7, 4]
def baseStart_3214308 : Nat := 118140960795 + 3214308 * 2 ^ 59
def prefixEnd_3214308 : Nat := 4983230072969 + 3 ^ 40 * 3214308 * 2
def baseEnd_3214308 : Nat := 366774439020470053081705

theorem tailTrace_3214308 : CollatzResearch.WordTrace tailWord_3214308 prefixEnd_3214308 366774439020470053081705 := by
  unfold tailWord_3214308
  simp only [CollatzResearch.WordTrace]
  refine ⟨58617722019559275473281789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78156962692745700631042385 58617722019559275473281789)
  ·
    refine ⟨21981645757334728302480671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58617722019559275473281789 21981645757334728302480671)
    ·
      refine ⟨32972468636002092453721007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21981645757334728302480671 32972468636002092453721007)
      ·
        refine ⟨49458702954003138680581511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32972468636002092453721007 49458702954003138680581511)
        ·
          refine ⟨74188054431004708020872267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49458702954003138680581511 74188054431004708020872267)
          ·
            refine ⟨111282081646507062031308401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74188054431004708020872267 111282081646507062031308401)
            ·
              refine ⟨83461561234880296523481301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111282081646507062031308401 83461561234880296523481301)
              ·
                refine ⟨1956130341442506949769093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83461561234880296523481301 1956130341442506949769093)
                ·
                  refine ⟨366774439020470053081705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1956130341442506949769093 366774439020470053081705)
                  ·
                    rfl

theorem cell22_3214308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_3214308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214308 prefixEnd_3214308 := by exact prefixLift 3214308
  have htrace : WordTrace (prefixWord ++ tailWord_3214308) baseStart_3214308 baseEnd_3214308 := by
    simpa [prefixWord, tailWord_3214308, baseEnd_3214308] using wordTrace_append hprefix tailTrace_3214308
  have hstable : (prefixWord ++ tailWord_3214308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214308).length < 2 ^ (prefixWord ++ tailWord_3214308).sum := by decide
  have hdescent : baseEnd_3214308 < baseStart_3214308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214473 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_3214473 : Nat := 118140960795 + 3214473 * 2 ^ 59
def prefixEnd_3214473 : Nat := 4983230072969 + 3 ^ 40 * 3214473 * 2
def baseEnd_3214473 : Nat := 1100379799933404728869609

theorem tailTrace_3214473 : CollatzResearch.WordTrace tailWord_3214473 prefixEnd_3214473 1100379799933404728869609 := by
  unfold tailWord_3214473
  simp only [CollatzResearch.WordTrace]
  refine ⟨117241462083520784126320073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78160974722347189417546715 117241462083520784126320073)
  ·
    refine ⟨87931096562640588094740055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117241462083520784126320073 87931096562640588094740055)
    ·
      refine ⟨131896644843960882142110083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87931096562640588094740055 131896644843960882142110083)
      ·
        refine ⟨197844967265941323213165125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131896644843960882142110083 197844967265941323213165125)
        ·
          refine ⟨37095931362363998102468461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197844967265941323213165125 37095931362363998102468461)
          ·
            refine ⟨13910974260886499288425673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37095931362363998102468461 13910974260886499288425673)
            ·
              refine ⟨10433230695664874466319255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13910974260886499288425673 10433230695664874466319255)
              ·
                refine ⟨15649846043497311699478883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10433230695664874466319255 15649846043497311699478883)
                ·
                  refine ⟨23474769065245967549218325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15649846043497311699478883 23474769065245967549218325)
                  ·
                    refine ⟨1100379799933404728869609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23474769065245967549218325 1100379799933404728869609)
                    ·
                      rfl

theorem cell22_3214473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_3214473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214473 prefixEnd_3214473 := by exact prefixLift 3214473
  have htrace : WordTrace (prefixWord ++ tailWord_3214473) baseStart_3214473 baseEnd_3214473 := by
    simpa [prefixWord, tailWord_3214473, baseEnd_3214473] using wordTrace_append hprefix tailTrace_3214473
  have hstable : (prefixWord ++ tailWord_3214473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214473).length < 2 ^ (prefixWord ++ tailWord_3214473).sum := by decide
  have hdescent : baseEnd_3214473 < baseStart_3214473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214488 : List Nat := [2, 1, 2, 4, 2, 1, 10]
def baseStart_3214488 : Nat := 118140960795 + 3214488 * 2 ^ 59
def prefixEnd_3214488 : Nat := 4983230072969 + 3 ^ 40 * 3214488 * 2
def baseEnd_3214488 : Nat := 40754997582961099620169

theorem tailTrace_3214488 : CollatzResearch.WordTrace tailWord_3214488 prefixEnd_3214488 40754997582961099620169 := by
  unfold tailWord_3214488
  simp only [CollatzResearch.WordTrace]
  refine ⟨58621004589233220844058059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78161339452310961125410745 58621004589233220844058059)
  ·
    refine ⟨87931506883849831266087089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58621004589233220844058059 87931506883849831266087089)
    ·
      refine ⟨65948630162887373449565317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87931506883849831266087089 65948630162887373449565317)
      ·
        refine ⟨12365368155541382521793497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65948630162887373449565317 12365368155541382521793497)
        ·
          refine ⟨9274026116656036891345123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12365368155541382521793497 9274026116656036891345123)
          ·
            refine ⟨13911039174984055337017685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9274026116656036891345123 13911039174984055337017685)
            ·
              refine ⟨40754997582961099620169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13911039174984055337017685 40754997582961099620169)
              ·
                rfl

theorem cell22_3214488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 10].length) (baseStart_3214488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214488 prefixEnd_3214488 := by exact prefixLift 3214488
  have htrace : WordTrace (prefixWord ++ tailWord_3214488) baseStart_3214488 baseEnd_3214488 := by
    simpa [prefixWord, tailWord_3214488, baseEnd_3214488] using wordTrace_append hprefix tailTrace_3214488
  have hstable : (prefixWord ++ tailWord_3214488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214488).length < 2 ^ (prefixWord ++ tailWord_3214488).sum := by decide
  have hdescent : baseEnd_3214488 < baseStart_3214488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214490 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_3214490 : Nat := 118140960795 + 3214490 * 2 ^ 59
def prefixEnd_3214490 : Nat := 4983230072969 + 3 ^ 40 * 3214490 * 2
def baseEnd_3214490 : Nat := 1100385619380822351194557

theorem tailTrace_3214490 : CollatzResearch.WordTrace tailWord_3214490 prefixEnd_3214490 1100385619380822351194557 := by
  unfold tailWord_3214490
  simp only [CollatzResearch.WordTrace]
  refine ⟨29310520531114799007422231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78161388082972797353125949 29310520531114799007422231)
  ·
    refine ⟨43965780796672198511133347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29310520531114799007422231 43965780796672198511133347)
    ·
      refine ⟨65948671195008297766700021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43965780796672198511133347 65948671195008297766700021)
      ·
        refine ⟨6182687924532027915628127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65948671195008297766700021 6182687924532027915628127)
        ·
          refine ⟨9274031886798041873442191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6182687924532027915628127 9274031886798041873442191)
          ·
            refine ⟨13911047830197062810163287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9274031886798041873442191 13911047830197062810163287)
            ·
              refine ⟨20866571745295594215244931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13911047830197062810163287 20866571745295594215244931)
              ·
                refine ⟨31299857617943391322867397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20866571745295594215244931 31299857617943391322867397)
                ·
                  refine ⟨5868723303364385873037637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31299857617943391322867397 5868723303364385873037637)
                  ·
                    refine ⟨1100385619380822351194557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5868723303364385873037637 1100385619380822351194557)
                    ·
                      rfl

theorem cell22_3214490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_3214490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214490 prefixEnd_3214490 := by exact prefixLift 3214490
  have htrace : WordTrace (prefixWord ++ tailWord_3214490) baseStart_3214490 baseEnd_3214490 := by
    simpa [prefixWord, tailWord_3214490, baseEnd_3214490] using wordTrace_append hprefix tailTrace_3214490
  have hstable : (prefixWord ++ tailWord_3214490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214490).length < 2 ^ (prefixWord ++ tailWord_3214490).sum := by decide
  have hdescent : baseEnd_3214490 < baseStart_3214490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214509 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3214509 : Nat := 118140960795 + 3214509 * 2 ^ 59
def prefixEnd_3214509 : Nat := 4983230072969 + 3 ^ 40 * 3214509 * 2
def baseEnd_3214509 : Nat := 1100392123469112634969499

theorem tailTrace_3214509 : CollatzResearch.WordTrace tailWord_3214509 prefixEnd_3214509 1100392123469112634969499 := by
  unfold tailWord_3214509
  simp only [CollatzResearch.WordTrace]
  refine ⟨117242775111390362274630581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78161850074260241516420387 117242775111390362274630581)
  ·
    refine ⟨10991510166692846463246617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117242775111390362274630581 10991510166692846463246617)
    ·
      refine ⟨8243632625019634847434963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10991510166692846463246617 8243632625019634847434963)
      ·
        refine ⟨12365448937529452271152445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8243632625019634847434963 12365448937529452271152445)
        ·
          refine ⟨4637043351573544601682167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12365448937529452271152445 4637043351573544601682167)
          ·
            refine ⟨6955565027360316902523251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637043351573544601682167 6955565027360316902523251)
            ·
              refine ⟨10433347541040475353784877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955565027360316902523251 10433347541040475353784877)
              ·
                refine ⟨3912505327890178257669329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10433347541040475353784877 3912505327890178257669329)
                ·
                  refine ⟨2934378995917633693251997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3912505327890178257669329 2934378995917633693251997)
                  ·
                    refine ⟨1100392123469112634969499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2934378995917633693251997 1100392123469112634969499)
                    ·
                      rfl

theorem cell22_3214509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3214509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214509 prefixEnd_3214509 := by exact prefixLift 3214509
  have htrace : WordTrace (prefixWord ++ tailWord_3214509) baseStart_3214509 baseEnd_3214509 := by
    simpa [prefixWord, tailWord_3214509, baseEnd_3214509] using wordTrace_append hprefix tailTrace_3214509
  have hstable : (prefixWord ++ tailWord_3214509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214509).length < 2 ^ (prefixWord ++ tailWord_3214509).sum := by decide
  have hdescent : baseEnd_3214509 < baseStart_3214509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214627 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 1, 5]
def baseStart_3214627 : Nat := 118140960795 + 3214627 * 2 ^ 59
def prefixEnd_3214627 : Nat := 4983230072969 + 3 ^ 40 * 3214627 * 2
def baseEnd_3214627 : Nat := 1100432517280599660519137

theorem tailTrace_3214627 : CollatzResearch.WordTrace tailWord_3214627 prefixEnd_3214627 1100432517280599660519137 := by
  unfold tailWord_3214627
  simp only [CollatzResearch.WordTrace]
  refine ⟨117247078924962868427426135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78164719283308578951617423 117247078924962868427426135)
  ·
    refine ⟨175870618387444302641139203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117247078924962868427426135 175870618387444302641139203)
    ·
      refine ⟨263805927581166453961708805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175870618387444302641139203 263805927581166453961708805)
      ·
        refine ⟨49463611421468710117820401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263805927581166453961708805 49463611421468710117820401)
        ·
          refine ⟨37097708566101532588365301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49463611421468710117820401 37097708566101532588365301)
          ·
            refine ⟨3477910178072018680159247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37097708566101532588365301 3477910178072018680159247)
            ·
              refine ⟨5216865267108028020238871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477910178072018680159247 5216865267108028020238871)
              ·
                refine ⟨7825297900662042030358307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216865267108028020238871 7825297900662042030358307)
                ·
                  refine ⟨11737946850993063045537461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7825297900662042030358307 11737946850993063045537461)
                  ·
                    refine ⟨1100432517280599660519137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11737946850993063045537461 1100432517280599660519137)
                    ·
                      rfl

theorem cell22_3214627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 5].length) (baseStart_3214627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214627 prefixEnd_3214627 := by exact prefixLift 3214627
  have htrace : WordTrace (prefixWord ++ tailWord_3214627) baseStart_3214627 baseEnd_3214627 := by
    simpa [prefixWord, tailWord_3214627, baseEnd_3214627] using wordTrace_append hprefix tailTrace_3214627
  have hstable : (prefixWord ++ tailWord_3214627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214627).length < 2 ^ (prefixWord ++ tailWord_3214627).sum := by decide
  have hdescent : baseEnd_3214627 < baseStart_3214627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214657 : List Nat := [1, 2, 5, 2, 1, 3, 8]
def baseStart_3214657 : Nat := 118140960795 + 3214657 * 2 ^ 59
def prefixEnd_3214657 : Nat := 4983230072969 + 3 ^ 40 * 3214657 * 2
def baseEnd_3214657 : Nat := 40757140255321836380335

theorem tailTrace_3214657 : CollatzResearch.WordTrace tailWord_3214657 prefixEnd_3214657 40757140255321836380335 := by
  unfold tailWord_3214657
  simp only [CollatzResearch.WordTrace]
  refine ⟨117248173114854183551018225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78165448743236122367345483 117248173114854183551018225)
  ·
    refine ⟨87936129836140637663263669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117248173114854183551018225 87936129836140637663263669)
    ·
      refine ⟨8244012172138184780930969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87936129836140637663263669 8244012172138184780930969)
      ·
        refine ⟨6183009129103638585698227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8244012172138184780930969 6183009129103638585698227)
        ·
          refine ⟨9274513693655457878547341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6183009129103638585698227 9274513693655457878547341)
          ·
            refine ⟨3477942635120796704455253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9274513693655457878547341 3477942635120796704455253)
            ·
              refine ⟨40757140255321836380335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3477942635120796704455253 40757140255321836380335)
              ·
                rfl

theorem cell22_3214657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 8].length) (baseStart_3214657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214657 prefixEnd_3214657 := by exact prefixLift 3214657
  have htrace : WordTrace (prefixWord ++ tailWord_3214657) baseStart_3214657 baseEnd_3214657 := by
    simpa [prefixWord, tailWord_3214657, baseEnd_3214657] using wordTrace_append hprefix tailTrace_3214657
  have hstable : (prefixWord ++ tailWord_3214657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214657).length < 2 ^ (prefixWord ++ tailWord_3214657).sum := by decide
  have hdescent : baseEnd_3214657 < baseStart_3214657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214670 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3214670 : Nat := 118140960795 + 3214670 * 2 ^ 59
def prefixEnd_3214670 : Nat := 4983230072969 + 3 ^ 40 * 3214670 * 2
def baseEnd_3214670 : Nat := 1100447237059361881694005

theorem tailTrace_3214670 : CollatzResearch.WordTrace tailWord_3214670 prefixEnd_3214670 1100447237059361881694005 := by
  unfold tailWord_3214670
  simp only [CollatzResearch.WordTrace]
  refine ⟨14656080907975885846405183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78165764842538057847494309 14656080907975885846405183)
  ·
    refine ⟨21984121361963828769607775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14656080907975885846405183 21984121361963828769607775)
    ·
      refine ⟨32976182042945743154411663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21984121361963828769607775 32976182042945743154411663)
      ·
        refine ⟨49464273064418614731617495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32976182042945743154411663 49464273064418614731617495)
        ·
          refine ⟨74196409596627922097426243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49464273064418614731617495 74196409596627922097426243)
          ·
            refine ⟨111294614394941883146139365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74196409596627922097426243 111294614394941883146139365)
            ·
              refine ⟨20867740199051603089901131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111294614394941883146139365 20867740199051603089901131)
              ·
                refine ⟨31301610298577404634851697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20867740199051603089901131 31301610298577404634851697)
                ·
                  refine ⟨23476207723933053476138773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31301610298577404634851697 23476207723933053476138773)
                  ·
                    refine ⟨1100447237059361881694005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23476207723933053476138773 1100447237059361881694005)
                    ·
                      rfl

theorem cell22_3214670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3214670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214670 prefixEnd_3214670 := by exact prefixLift 3214670
  have htrace : WordTrace (prefixWord ++ tailWord_3214670) baseStart_3214670 baseEnd_3214670 := by
    simpa [prefixWord, tailWord_3214670, baseEnd_3214670] using wordTrace_append hprefix tailTrace_3214670
  have hstable : (prefixWord ++ tailWord_3214670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214670).length < 2 ^ (prefixWord ++ tailWord_3214670).sum := by decide
  have hdescent : baseEnd_3214670 < baseStart_3214670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214723 : List Nat := [1, 1, 1, 3, 5, 3, 2, 2, 1, 3]
def baseStart_3214723 : Nat := 118140960795 + 3214723 * 2 ^ 59
def prefixEnd_3214723 : Nat := 4983230072969 + 3 ^ 40 * 3214723 * 2
def baseEnd_3214723 : Nat := 1100465380042487410118843

theorem tailTrace_3214723 : CollatzResearch.WordTrace tailWord_3214723 prefixEnd_3214723 1100465380042487410118843 := by
  unfold tailWord_3214723
  simp only [CollatzResearch.WordTrace]
  refine ⟨117250580332615076822920823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78167053555076717881947215 117250580332615076822920823)
  ·
    refine ⟨175875870498922615234381235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117250580332615076822920823 175875870498922615234381235)
    ·
      refine ⟨263813805748383922851571853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175875870498922615234381235 263813805748383922851571853)
      ·
        refine ⟨98930177155643971069339445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263813805748383922851571853 98930177155643971069339445)
        ·
          refine ⟨9274704108341622287750573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98930177155643971069339445 9274704108341622287750573)
          ·
            refine ⟨3478014040628108357906465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9274704108341622287750573 3478014040628108357906465)
            ·
              refine ⟨2608510530471081268429849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3478014040628108357906465 2608510530471081268429849)
              ·
                refine ⟨1956382897853310951322387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2608510530471081268429849 1956382897853310951322387)
                ·
                  refine ⟨2934574346779966426983581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956382897853310951322387 2934574346779966426983581)
                  ·
                    refine ⟨1100465380042487410118843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2934574346779966426983581 1100465380042487410118843)
                    ·
                      rfl

theorem cell22_3214723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 1, 3].length) (baseStart_3214723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214723 prefixEnd_3214723 := by exact prefixLift 3214723
  have htrace : WordTrace (prefixWord ++ tailWord_3214723) baseStart_3214723 baseEnd_3214723 := by
    simpa [prefixWord, tailWord_3214723, baseEnd_3214723] using wordTrace_append hprefix tailTrace_3214723
  have hstable : (prefixWord ++ tailWord_3214723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214723).length < 2 ^ (prefixWord ++ tailWord_3214723).sum := by decide
  have hdescent : baseEnd_3214723 < baseStart_3214723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214734 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_3214734 : Nat := 118140960795 + 3214734 * 2 ^ 59
def prefixEnd_3214734 : Nat := 4983230072969 + 3 ^ 40 * 3214734 * 2
def baseEnd_3214734 : Nat := 1100469145567287048093809

theorem tailTrace_3214734 : CollatzResearch.WordTrace tailWord_3214734 prefixEnd_3214734 1100469145567287048093809 := by
  unfold tailWord_3214734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14656372691946903212696407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78167321023716817134380837 14656372691946903212696407)
  ·
    refine ⟨21984559037920354819044611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14656372691946903212696407 21984559037920354819044611)
    ·
      refine ⟨32976838556880532228566917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21984559037920354819044611 32976838556880532228566917)
      ·
        refine ⟨6183157229415099792856297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32976838556880532228566917 6183157229415099792856297)
        ·
          refine ⟨4637367922061324844642223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6183157229415099792856297 4637367922061324844642223)
          ·
            refine ⟨6956051883091987266963335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637367922061324844642223 6956051883091987266963335)
            ·
              refine ⟨10434077824637980900445003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956051883091987266963335 10434077824637980900445003)
              ·
                refine ⟨15651116736956971350667505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10434077824637980900445003 15651116736956971350667505)
                ·
                  refine ⟨11738337552717728513000629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15651116736956971350667505 11738337552717728513000629)
                  ·
                    refine ⟨1100469145567287048093809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11738337552717728513000629 1100469145567287048093809)
                    ·
                      rfl

theorem cell22_3214734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_3214734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214734 prefixEnd_3214734 := by exact prefixLift 3214734
  have htrace : WordTrace (prefixWord ++ tailWord_3214734) baseStart_3214734 baseEnd_3214734 := by
    simpa [prefixWord, tailWord_3214734, baseEnd_3214734] using wordTrace_append hprefix tailTrace_3214734
  have hstable : (prefixWord ++ tailWord_3214734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214734).length < 2 ^ (prefixWord ++ tailWord_3214734).sum := by decide
  have hdescent : baseEnd_3214734 < baseStart_3214734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214775 : List Nat := [1, 1, 3, 1, 3, 2, 11]
def baseStart_3214775 : Nat := 118140960795 + 3214775 * 2 ^ 59
def prefixEnd_3214775 : Nat := 4983230072969 + 3 ^ 40 * 3214775 * 2
def baseEnd_3214775 : Nat := 40758636322413948437729

theorem tailTrace_3214775 : CollatzResearch.WordTrace tailWord_3214775 prefixEnd_3214775 40758636322413948437729 := by
  unfold tailWord_3214775
  simp only [CollatzResearch.WordTrace]
  refine ⟨117252476928426689703813779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78168317952284459802542519 117252476928426689703813779)
  ·
    refine ⟨175878715392640034555720669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117252476928426689703813779 175878715392640034555720669)
    ·
      refine ⟨65954518272240012958395251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175878715392640034555720669 65954518272240012958395251)
      ·
        refine ⟨98931777408360019437592877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65954518272240012958395251 98931777408360019437592877)
        ·
          refine ⟨37099416528135007289097329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98931777408360019437592877 37099416528135007289097329)
          ·
            refine ⟨27824562396101255466822997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37099416528135007289097329 27824562396101255466822997)
            ·
              refine ⟨40758636322413948437729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27824562396101255466822997 40758636322413948437729)
              ·
                rfl

theorem cell22_3214775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 11].length) (baseStart_3214775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214775 prefixEnd_3214775 := by exact prefixLift 3214775
  have htrace : WordTrace (prefixWord ++ tailWord_3214775) baseStart_3214775 baseEnd_3214775 := by
    simpa [prefixWord, tailWord_3214775, baseEnd_3214775] using wordTrace_append hprefix tailTrace_3214775
  have hstable : (prefixWord ++ tailWord_3214775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214775).length < 2 ^ (prefixWord ++ tailWord_3214775).sum := by decide
  have hdescent : baseEnd_3214775 < baseStart_3214775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214809 : List Nat := [1, 2, 1, 2, 4, 4, 2, 6]
def baseStart_3214809 : Nat := 118140960795 + 3214809 * 2 ^ 59
def prefixEnd_3214809 : Nat := 4983230072969 + 3 ^ 40 * 3214809 * 2
def baseEnd_3214809 : Nat := 122277202177779094718731

theorem tailTrace_3214809 : CollatzResearch.WordTrace tailWord_3214809 prefixEnd_3214809 122277202177779094718731 := by
  unfold tailWord_3214809
  simp only [CollatzResearch.WordTrace]
  refine ⟨117253717010303513510551481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78169144673535675673700987 117253717010303513510551481)
  ·
    refine ⟨87940287757727635132913611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117253717010303513510551481 87940287757727635132913611)
    ·
      refine ⟨131910431636591452699370417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87940287757727635132913611 131910431636591452699370417)
      ·
        refine ⟨98932823727443589524527813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131910431636591452699370417 98932823727443589524527813)
        ·
          refine ⟨18549904448895673035848965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98932823727443589524527813 18549904448895673035848965)
          ·
            refine ⟨3478107084167938694221681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18549904448895673035848965 3478107084167938694221681)
            ·
              refine ⟨2608580313125954020666261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3478107084167938694221681 2608580313125954020666261)
              ·
                refine ⟨122277202177779094718731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2608580313125954020666261 122277202177779094718731)
                ·
                  rfl

theorem cell22_3214809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 6].length) (baseStart_3214809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214809 prefixEnd_3214809 := by exact prefixLift 3214809
  have htrace : WordTrace (prefixWord ++ tailWord_3214809) baseStart_3214809 baseEnd_3214809 := by
    simpa [prefixWord, tailWord_3214809, baseEnd_3214809] using wordTrace_append hprefix tailTrace_3214809
  have hstable : (prefixWord ++ tailWord_3214809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214809).length < 2 ^ (prefixWord ++ tailWord_3214809).sum := by decide
  have hdescent : baseEnd_3214809 < baseStart_3214809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214897 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_3214897 : Nat := 118140960795 + 3214897 * 2 ^ 59
def prefixEnd_3214897 : Nat := 4983230072969 + 3 ^ 40 * 3214897 * 2
def baseEnd_3214897 : Nat := 1100524943798408956268309

theorem tailTrace_3214897 : CollatzResearch.WordTrace tailWord_3214897 prefixEnd_3214897 1100524943798408956268309 := by
  unfold tailWord_3214897
  simp only [CollatzResearch.WordTrace]
  refine ⟨117256926633984704539754945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78171284422656469693169963 117256926633984704539754945)
  ·
    refine ⟨87942694975488528404816209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117256926633984704539754945 87942694975488528404816209)
    ·
      refine ⟨65957021231616396303612157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87942694975488528404816209 65957021231616396303612157)
      ·
        refine ⟨24733882961856148613854559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65957021231616396303612157 24733882961856148613854559)
        ·
          refine ⟨37100824442784222920781839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24733882961856148613854559 37100824442784222920781839)
          ·
            refine ⟨55651236664176334381172759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37100824442784222920781839 55651236664176334381172759)
            ·
              refine ⟨83476854996264501571759139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55651236664176334381172759 83476854996264501571759139)
              ·
                refine ⟨125215282494396752357638709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83476854996264501571759139 125215282494396752357638709)
                ·
                  refine ⟨11738932733849695533528629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125215282494396752357638709 11738932733849695533528629)
                  ·
                    refine ⟨1100524943798408956268309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11738932733849695533528629 1100524943798408956268309)
                    ·
                      rfl

theorem cell22_3214897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_3214897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214897 prefixEnd_3214897 := by exact prefixLift 3214897
  have htrace : WordTrace (prefixWord ++ tailWord_3214897) baseStart_3214897 baseEnd_3214897 := by
    simpa [prefixWord, tailWord_3214897, baseEnd_3214897] using wordTrace_append hprefix tailTrace_3214897
  have hstable : (prefixWord ++ tailWord_3214897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214897).length < 2 ^ (prefixWord ++ tailWord_3214897).sum := by decide
  have hdescent : baseEnd_3214897 < baseStart_3214897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214912 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_3214912 : Nat := 118140960795 + 3214912 * 2 ^ 59
def prefixEnd_3214912 : Nat := 4983230072969 + 3 ^ 40 * 3214912 * 2
def baseEnd_3214912 : Nat := 1100530078604953917143263

theorem tailTrace_3214912 : CollatzResearch.WordTrace tailWord_3214912 prefixEnd_3214912 1100530078604953917143263 := by
  unfold tailWord_3214912
  simp only [CollatzResearch.WordTrace]
  refine ⟨58628736864465181050775495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78171649152620241401033993 58628736864465181050775495)
  ·
    refine ⟨87943105296697771576163243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58628736864465181050775495 87943105296697771576163243)
    ·
      refine ⟨131914657945046657364244865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87943105296697771576163243 131914657945046657364244865)
      ·
        refine ⟨98935993458784993023183649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131914657945046657364244865 98935993458784993023183649)
        ·
          refine ⟨74201995094088744767387737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98935993458784993023183649 74201995094088744767387737)
          ·
            refine ⟨55651496320566558575540803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74201995094088744767387737 55651496320566558575540803)
            ·
              refine ⟨83477244480849837863311205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55651496320566558575540803 83477244480849837863311205)
              ·
                refine ⟨15651983340159344599370851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83477244480849837863311205 15651983340159344599370851)
                ·
                  refine ⟨23477975010239016899056277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15651983340159344599370851 23477975010239016899056277)
                  ·
                    refine ⟨1100530078604953917143263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23477975010239016899056277 1100530078604953917143263)
                    ·
                      rfl

theorem cell22_3214912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_3214912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214912 prefixEnd_3214912 := by exact prefixLift 3214912
  have htrace : WordTrace (prefixWord ++ tailWord_3214912) baseStart_3214912 baseEnd_3214912 := by
    simpa [prefixWord, tailWord_3214912, baseEnd_3214912] using wordTrace_append hprefix tailTrace_3214912
  have hstable : (prefixWord ++ tailWord_3214912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214912).length < 2 ^ (prefixWord ++ tailWord_3214912).sum := by decide
  have hdescent : baseEnd_3214912 < baseStart_3214912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214948 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_3214948 : Nat := 118140960795 + 3214948 * 2 ^ 59
def prefixEnd_3214948 : Nat := 4983230072969 + 3 ^ 40 * 3214948 * 2
def baseEnd_3214948 : Nat := 1100542402140661823243153

theorem tailTrace_3214948 : CollatzResearch.WordTrace tailWord_3214948 prefixEnd_3214948 1100542402140661823243153 := by
  unfold tailWord_3214948
  simp only [CollatzResearch.WordTrace]
  refine ⟨58629393378399970124930749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78172524504533293499907665 58629393378399970124930749)
  ·
    refine ⟨21986022516899988796849031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58629393378399970124930749 21986022516899988796849031)
    ·
      refine ⟨32979033775349983195273547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21986022516899988796849031 32979033775349983195273547)
      ·
        refine ⟨49468550663024974792910321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32979033775349983195273547 49468550663024974792910321)
        ·
          refine ⟨37101412997268731094682741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49468550663024974792910321 37101412997268731094682741)
          ·
            refine ⟨3478257468493943540126507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37101412997268731094682741 3478257468493943540126507)
            ·
              refine ⟨5217386202740915310189761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3478257468493943540126507 5217386202740915310189761)
              ·
                refine ⟨3913039652055686482642321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5217386202740915310189761 3913039652055686482642321)
                ·
                  refine ⟨2934779739041764861981741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3913039652055686482642321 2934779739041764861981741)
                  ·
                    refine ⟨1100542402140661823243153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2934779739041764861981741 1100542402140661823243153)
                    ·
                      rfl

theorem cell22_3214948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_3214948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214948 prefixEnd_3214948 := by exact prefixLift 3214948
  have htrace : WordTrace (prefixWord ++ tailWord_3214948) baseStart_3214948 baseEnd_3214948 := by
    simpa [prefixWord, tailWord_3214948, baseEnd_3214948] using wordTrace_append hprefix tailTrace_3214948
  have hstable : (prefixWord ++ tailWord_3214948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214948).length < 2 ^ (prefixWord ++ tailWord_3214948).sum := by decide
  have hdescent : baseEnd_3214948 < baseStart_3214948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3214965 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 2, 3]
def baseStart_3214965 : Nat := 118140960795 + 3214965 * 2 ^ 59
def prefixEnd_3214965 : Nat := 4983230072969 + 3 ^ 40 * 3214965 * 2
def baseEnd_3214965 : Nat := 1100548221588079445568101

theorem tailTrace_3214965 : CollatzResearch.WordTrace tailWord_3214965 prefixEnd_3214965 1100548221588079445568101 := by
  unfold tailWord_3214965
  simp only [CollatzResearch.WordTrace]
  refine ⟨117259406797738352153230349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78172937865158901435486899 117259406797738352153230349)
  ·
    refine ⟨43972277549151882057461381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117259406797738352153230349 43972277549151882057461381)
    ·
      refine ⟨8244802040465977885774009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43972277549151882057461381 8244802040465977885774009)
      ·
        refine ⟨6183601530349483414330507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8244802040465977885774009 6183601530349483414330507)
        ·
          refine ⟨9275402295524225121495761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6183601530349483414330507 9275402295524225121495761)
          ·
            refine ⟨6956551721643168841121821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9275402295524225121495761 6956551721643168841121821)
            ·
              refine ⟨2608706895616188315420683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6956551721643168841121821 2608706895616188315420683)
              ·
                refine ⟨3913060343424282473131025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608706895616188315420683 3913060343424282473131025)
                ·
                  refine ⟨2934795257568211854848269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3913060343424282473131025 2934795257568211854848269)
                  ·
                    refine ⟨1100548221588079445568101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2934795257568211854848269 1100548221588079445568101)
                    ·
                      rfl

theorem cell22_3214965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_3214965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3214965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3214965 prefixEnd_3214965 := by exact prefixLift 3214965
  have htrace : WordTrace (prefixWord ++ tailWord_3214965) baseStart_3214965 baseEnd_3214965 := by
    simpa [prefixWord, tailWord_3214965, baseEnd_3214965] using wordTrace_append hprefix tailTrace_3214965
  have hstable : (prefixWord ++ tailWord_3214965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3214965).length < 2 ^ (prefixWord ++ tailWord_3214965).sum := by decide
  have hdescent : baseEnd_3214965 < baseStart_3214965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3214965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215006 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_3215006 : Nat := 118140960795 + 3215006 * 2 ^ 59
def prefixEnd_3215006 : Nat := 4983230072969 + 3 ^ 40 * 3215006 * 2
def baseEnd_3215006 : Nat := 366854085575323001764325

theorem tailTrace_3215006 : CollatzResearch.WordTrace tailWord_3215006 prefixEnd_3215006 366854085575323001764325 := by
  unfold tailWord_3215006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14657612773823727019434109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78173934793726544103648581 14657612773823727019434109)
  ·
    refine ⟨5496604790183897632287791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14657612773823727019434109 5496604790183897632287791)
    ·
      refine ⟨8244907185275846448431687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5496604790183897632287791 8244907185275846448431687)
      ·
        refine ⟨12367360777913769672647531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8244907185275846448431687 12367360777913769672647531)
        ·
          refine ⟨18551041166870654508971297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12367360777913769672647531 18551041166870654508971297)
          ·
            refine ⟨13913280875152990881728473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18551041166870654508971297 13913280875152990881728473)
            ·
              refine ⟨10434960656364743161296355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13913280875152990881728473 10434960656364743161296355)
              ·
                refine ⟨15652440984547114741944533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10434960656364743161296355 15652440984547114741944533)
                ·
                  refine ⟨366854085575323001764325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15652440984547114741944533 366854085575323001764325)
                  ·
                    rfl

theorem cell22_3215006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_3215006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215006 prefixEnd_3215006 := by exact prefixLift 3215006
  have htrace : WordTrace (prefixWord ++ tailWord_3215006) baseStart_3215006 baseEnd_3215006 := by
    simpa [prefixWord, tailWord_3215006, baseEnd_3215006] using wordTrace_append hprefix tailTrace_3215006
  have hstable : (prefixWord ++ tailWord_3215006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215006).length < 2 ^ (prefixWord ++ tailWord_3215006).sum := by decide
  have hdescent : baseEnd_3215006 < baseStart_3215006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215016 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3215016 : Nat := 118140960795 + 3215016 * 2 ^ 59
def prefixEnd_3215016 : Nat := 4983230072969 + 3 ^ 40 * 3215016 * 2
def baseEnd_3215016 : Nat := 1100565679930332312542945

theorem tailTrace_3215016 : CollatzResearch.WordTrace tailWord_3215016 prefixEnd_3215016 1100565679930332312542945 := by
  unfold tailWord_3215016
  simp only [CollatzResearch.WordTrace]
  refine ⟨58630633460276793931668451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78174177947035725242224601 58630633460276793931668451)
  ·
    refine ⟨87945950190415190897502677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58630633460276793931668451 87945950190415190897502677)
    ·
      refine ⟨2061233207587856036660219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 87945950190415190897502677 2061233207587856036660219)
      ·
        refine ⟨3091849811381784054990329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061233207587856036660219 3091849811381784054990329)
        ·
          refine ⟨2318887358536338041242747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091849811381784054990329 2318887358536338041242747)
          ·
            refine ⟨3478331037804507061864121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318887358536338041242747 3478331037804507061864121)
            ·
              refine ⟨2608748278353380296398091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3478331037804507061864121 2608748278353380296398091)
              ·
                refine ⟨3913122417530070444597137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608748278353380296398091 3913122417530070444597137)
                ·
                  refine ⟨2934841813147552833447853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3913122417530070444597137 2934841813147552833447853)
                  ·
                    refine ⟨1100565679930332312542945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2934841813147552833447853 1100565679930332312542945)
                    ·
                      rfl

theorem cell22_3215016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3215016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215016 prefixEnd_3215016 := by exact prefixLift 3215016
  have htrace : WordTrace (prefixWord ++ tailWord_3215016) baseStart_3215016 baseEnd_3215016 := by
    simpa [prefixWord, tailWord_3215016, baseEnd_3215016] using wordTrace_append hprefix tailTrace_3215016
  have hstable : (prefixWord ++ tailWord_3215016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215016).length < 2 ^ (prefixWord ++ tailWord_3215016).sum := by decide
  have hdescent : baseEnd_3215016 < baseStart_3215016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215036 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_3215036 : Nat := 118140960795 + 3215036 * 2 ^ 59
def prefixEnd_3215036 : Nat := 4983230072969 + 3 ^ 40 * 3215036 * 2
def baseEnd_3215036 : Nat := 1100572526339058927042883

theorem tailTrace_3215036 : CollatzResearch.WordTrace tailWord_3215036 prefixEnd_3215036 1100572526339058927042883 := by
  unfold tailWord_3215036
  simp only [CollatzResearch.WordTrace]
  refine ⟨58630998190240565639532481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78174664253654087519376641 58630998190240565639532481)
  ·
    refine ⟨43973248642680424229649361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58630998190240565639532481 43973248642680424229649361)
    ·
      refine ⟨32979936482010318172237021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43973248642680424229649361 32979936482010318172237021)
      ·
        refine ⟨12367476180753869314588883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32979936482010318172237021 12367476180753869314588883)
        ·
          refine ⟨18551214271130803971883325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12367476180753869314588883 18551214271130803971883325)
          ·
            refine ⟨6956705351674051489456247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18551214271130803971883325 6956705351674051489456247)
            ·
              refine ⟨10435058027511077234184371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956705351674051489456247 10435058027511077234184371)
              ·
                refine ⟨15652587041266615851276557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10435058027511077234184371 15652587041266615851276557)
                ·
                  refine ⟨5869720140474980944228709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15652587041266615851276557 5869720140474980944228709)
                  ·
                    refine ⟨1100572526339058927042883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5869720140474980944228709 1100572526339058927042883)
                    ·
                      rfl

theorem cell22_3215036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_3215036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215036 prefixEnd_3215036 := by exact prefixLift 3215036
  have htrace : WordTrace (prefixWord ++ tailWord_3215036) baseStart_3215036 baseEnd_3215036 := by
    simpa [prefixWord, tailWord_3215036, baseEnd_3215036] using wordTrace_append hprefix tailTrace_3215036
  have hstable : (prefixWord ++ tailWord_3215036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215036).length < 2 ^ (prefixWord ++ tailWord_3215036).sum := by decide
  have hdescent : baseEnd_3215036 < baseStart_3215036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215134 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3215134 : Nat := 118140960795 + 3215134 * 2 ^ 59
def prefixEnd_3215134 : Nat := 4983230072969 + 3 ^ 40 * 3215134 * 2
def baseEnd_3215134 : Nat := 1100606073741819338092583

theorem tailTrace_3215134 : CollatzResearch.WordTrace tailWord_3215134 prefixEnd_3215134 1100606073741819338092583 := by
  unfold tailWord_3215134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14658196341765761752016557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78177047156084062677421637 14658196341765761752016557)
  ·
    refine ⟨5496823628162160657006209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14658196341765761752016557 5496823628162160657006209)
    ·
      refine ⟨4122617721121620492754657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5496823628162160657006209 4122617721121620492754657)
      ·
        refine ⟨3091963290841215369565993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4122617721121620492754657 3091963290841215369565993)
        ·
          refine ⟨2318972468130911527174495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091963290841215369565993 2318972468130911527174495)
          ·
            refine ⟨3478458702196367290761743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318972468130911527174495 3478458702196367290761743)
            ·
              refine ⟨5217688053294550936142615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3478458702196367290761743 5217688053294550936142615)
              ·
                refine ⟨7826532079941826404213923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5217688053294550936142615 7826532079941826404213923)
                ·
                  refine ⟨11739798119912739606320885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7826532079941826404213923 11739798119912739606320885)
                  ·
                    refine ⟨1100606073741819338092583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11739798119912739606320885 1100606073741819338092583)
                    ·
                      rfl

theorem cell22_3215134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3215134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215134 prefixEnd_3215134 := by exact prefixLift 3215134
  have htrace : WordTrace (prefixWord ++ tailWord_3215134) baseStart_3215134 baseEnd_3215134 := by
    simpa [prefixWord, tailWord_3215134, baseEnd_3215134] using wordTrace_append hprefix tailTrace_3215134
  have hstable : (prefixWord ++ tailWord_3215134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215134).length < 2 ^ (prefixWord ++ tailWord_3215134).sum := by decide
  have hdescent : baseEnd_3215134 < baseStart_3215134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215158 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3215158 : Nat := 118140960795 + 3215158 * 2 ^ 59
def prefixEnd_3215158 : Nat := 4983230072969 + 3 ^ 40 * 3215158 * 2
def baseEnd_3215158 : Nat := 366871429810763758497503

theorem tailTrace_3215158 : CollatzResearch.WordTrace tailWord_3215158 prefixEnd_3215158 366871429810763758497503 := by
  unfold tailWord_3215158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329152880377446632187883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78177630724026097410004085 7329152880377446632187883)
  ·
    refine ⟨10993729320566169948281825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7329152880377446632187883 10993729320566169948281825)
    ·
      refine ⟨8245296990424627461211369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10993729320566169948281825 8245296990424627461211369)
      ·
        refine ⟨6183972742818470595908527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8245296990424627461211369 6183972742818470595908527)
        ·
          refine ⟨9275959114227705893862791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6183972742818470595908527 9275959114227705893862791)
          ·
            refine ⟨13913938671341558840794187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9275959114227705893862791 13913938671341558840794187)
            ·
              refine ⟨20870908007012338261191281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13913938671341558840794187 20870908007012338261191281)
              ·
                refine ⟨15653181005259253695893461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20870908007012338261191281 15653181005259253695893461)
                ·
                  refine ⟨366871429810763758497503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15653181005259253695893461 366871429810763758497503)
                  ·
                    rfl

theorem cell22_3215158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3215158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215158 prefixEnd_3215158 := by exact prefixLift 3215158
  have htrace : WordTrace (prefixWord ++ tailWord_3215158) baseStart_3215158 baseEnd_3215158 := by
    simpa [prefixWord, tailWord_3215158, baseEnd_3215158] using wordTrace_append hprefix tailTrace_3215158
  have hstable : (prefixWord ++ tailWord_3215158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215158).length < 2 ^ (prefixWord ++ tailWord_3215158).sum := by decide
  have hdescent : baseEnd_3215158 < baseStart_3215158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215162 : List Nat := [3, 1, 1, 1, 5, 3, 1, 3, 1, 3]
def baseStart_3215162 : Nat := 118140960795 + 3215162 * 2 ^ 59
def prefixEnd_3215162 : Nat := 4983230072969 + 3 ^ 40 * 3215162 * 2
def baseEnd_3215162 : Nat := 1100615658714036598392497

theorem tailTrace_3215162 : CollatzResearch.WordTrace tailWord_3215162 prefixEnd_3215162 1100615658714036598392497 := by
  unfold tailWord_3215162
  simp only [CollatzResearch.WordTrace]
  refine ⟨29316647994506163699537935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78177727985349769865434493 29316647994506163699537935)
  ·
    refine ⟨43974971991759245549306903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29316647994506163699537935 43974971991759245549306903)
    ·
      refine ⟨65962457987638868323960355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43974971991759245549306903 65962457987638868323960355)
      ·
        refine ⟨98943686981458302485940533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65962457987638868323960355 98943686981458302485940533)
        ·
          refine ⟨9275970654511715858056925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98943686981458302485940533 9275970654511715858056925)
          ·
            refine ⟨3478488995441893446771347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9275970654511715858056925 3478488995441893446771347)
            ·
              refine ⟨5217733493162840170157021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3478488995441893446771347 5217733493162840170157021)
              ·
                refine ⟨1956650059936065063808883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5217733493162840170157021 1956650059936065063808883)
                ·
                  refine ⟨2934975089904097595713325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956650059936065063808883 2934975089904097595713325)
                  ·
                    refine ⟨1100615658714036598392497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2934975089904097595713325 1100615658714036598392497)
                    ·
                      rfl

theorem cell22_3215162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_3215162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215162 prefixEnd_3215162 := by exact prefixLift 3215162
  have htrace : WordTrace (prefixWord ++ tailWord_3215162) baseStart_3215162 baseEnd_3215162 := by
    simpa [prefixWord, tailWord_3215162, baseEnd_3215162] using wordTrace_append hprefix tailTrace_3215162
  have hstable : (prefixWord ++ tailWord_3215162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215162).length < 2 ^ (prefixWord ++ tailWord_3215162).sum := by decide
  have hdescent : baseEnd_3215162 < baseStart_3215162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215201 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3215201 : Nat := 118140960795 + 3215201 * 2 ^ 59
def prefixEnd_3215201 : Nat := 4983230072969 + 3 ^ 40 * 3215201 * 2
def baseEnd_3215201 : Nat := 1100629009211053496667377

theorem tailTrace_3215201 : CollatzResearch.WordTrace tailWord_3215201 prefixEnd_3215201 1100629009211053496667377 := by
  unfold tailWord_3215201
  simp only [CollatzResearch.WordTrace]
  refine ⟨117268014424883364458821457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78178676283255576305880971 117268014424883364458821457)
  ·
    refine ⟨87951010818662523344116093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117268014424883364458821457 87951010818662523344116093)
    ·
      refine ⟨32981629056998446254043535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87951010818662523344116093 32981629056998446254043535)
      ·
        refine ⟨49472443585497669381065303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32981629056998446254043535 49472443585497669381065303)
        ·
          refine ⟨74208665378246504071597955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49472443585497669381065303 74208665378246504071597955)
          ·
            refine ⟨111312998067369756107396933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74208665378246504071597955 111312998067369756107396933)
            ·
              refine ⟨20871187137631829270136925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111312998067369756107396933 20871187137631829270136925)
              ·
                refine ⟨7826695176611935976301347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20871187137631829270136925 7826695176611935976301347)
                ·
                  refine ⟨11740042764917903964452021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7826695176611935976301347 11740042764917903964452021)
                  ·
                    refine ⟨1100629009211053496667377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11740042764917903964452021 1100629009211053496667377)
                    ·
                      rfl

theorem cell22_3215201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3215201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215201 prefixEnd_3215201 := by exact prefixLift 3215201
  have htrace : WordTrace (prefixWord ++ tailWord_3215201) baseStart_3215201 baseEnd_3215201 := by
    simpa [prefixWord, tailWord_3215201, baseEnd_3215201] using wordTrace_append hprefix tailTrace_3215201
  have hstable : (prefixWord ++ tailWord_3215201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215201).length < 2 ^ (prefixWord ++ tailWord_3215201).sum := by decide
  have hdescent : baseEnd_3215201 < baseStart_3215201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215235 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 2, 3]
def baseStart_3215235 : Nat := 118140960795 + 3215235 * 2 ^ 59
def prefixEnd_3215235 : Nat := 4983230072969 + 3 ^ 40 * 3215235 * 2
def baseEnd_3215235 : Nat := 1100640648105888741317273

theorem tailTrace_3215235 : CollatzResearch.WordTrace tailWord_3215235 prefixEnd_3215235 1100640648105888741317273 := by
  unfold tailWord_3215235
  simp only [CollatzResearch.WordTrace]
  refine ⟨117269254506760188265559159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78179503004506792177039439 117269254506760188265559159)
  ·
    refine ⟨175903881760140282398338739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117269254506760188265559159 175903881760140282398338739)
    ·
      refine ⟨263855822640210423597508109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175903881760140282398338739 263855822640210423597508109)
      ·
        refine ⟨98945933490078908849065541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263855822640210423597508109 98945933490078908849065541)
        ·
          refine ⟨18552362529389795409199789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98945933490078908849065541 18552362529389795409199789)
          ·
            refine ⟨6957135948521173278449921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18552362529389795409199789 6957135948521173278449921)
            ·
              refine ⟨5217851961390879958837441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6957135948521173278449921 5217851961390879958837441)
              ·
                refine ⟨3913388971043159969128081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5217851961390879958837441 3913388971043159969128081)
                ·
                  refine ⟨2935041728282369976846061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3913388971043159969128081 2935041728282369976846061)
                  ·
                    refine ⟨1100640648105888741317273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2935041728282369976846061 1100640648105888741317273)
                    ·
                      rfl

theorem cell22_3215235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 3].length) (baseStart_3215235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215235 prefixEnd_3215235 := by exact prefixLift 3215235
  have htrace : WordTrace (prefixWord ++ tailWord_3215235) baseStart_3215235 baseEnd_3215235 := by
    simpa [prefixWord, tailWord_3215235, baseEnd_3215235] using wordTrace_append hprefix tailTrace_3215235
  have hstable : (prefixWord ++ tailWord_3215235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215235).length < 2 ^ (prefixWord ++ tailWord_3215235).sum := by decide
  have hdescent : baseEnd_3215235 < baseStart_3215235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215265 : List Nat := [1, 2, 3, 4, 2, 1, 3, 6]
def baseStart_3215265 : Nat := 118140960795 + 3215265 * 2 ^ 59
def prefixEnd_3215265 : Nat := 4983230072969 + 3 ^ 40 * 3215265 * 2
def baseEnd_3215265 : Nat := 122294546413219851451909

theorem tailTrace_3215265 : CollatzResearch.WordTrace tailWord_3215265 prefixEnd_3215265 122294546413219851451909 := by
  unfold tailWord_3215265
  simp only [CollatzResearch.WordTrace]
  refine ⟨117270348696651503389151249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78180232464434335592767499 117270348696651503389151249)
  ·
    refine ⟨87952761522488627541863437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117270348696651503389151249 87952761522488627541863437)
    ·
      refine ⟨32982285570933235328198789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87952761522488627541863437 32982285570933235328198789)
      ·
        refine ⟨6184178544549981624037273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32982285570933235328198789 6184178544549981624037273)
        ·
          refine ⟨4638133908412486218027955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6184178544549981624037273 4638133908412486218027955)
          ·
            refine ⟨6957200862618729327041933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638133908412486218027955 6957200862618729327041933)
            ·
              refine ⟨2608950323482023497640725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6957200862618729327041933 2608950323482023497640725)
              ·
                refine ⟨122294546413219851451909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2608950323482023497640725 122294546413219851451909)
                ·
                  rfl

theorem cell22_3215265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 6].length) (baseStart_3215265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215265 prefixEnd_3215265 := by exact prefixLift 3215265
  have htrace : WordTrace (prefixWord ++ tailWord_3215265) baseStart_3215265 baseEnd_3215265 := by
    simpa [prefixWord, tailWord_3215265, baseEnd_3215265] using wordTrace_append hprefix tailTrace_3215265
  have hstable : (prefixWord ++ tailWord_3215265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215265).length < 2 ^ (prefixWord ++ tailWord_3215265).sum := by decide
  have hdescent : baseEnd_3215265 < baseStart_3215265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215291 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 2, 5]
def baseStart_3215291 : Nat := 118140960795 + 3215291 * 2 ^ 59
def prefixEnd_3215291 : Nat := 4983230072969 + 3 ^ 40 * 3215291 * 2
def baseEnd_3215291 : Nat := 1100659818050323261917101

theorem tailTrace_3215291 : CollatzResearch.WordTrace tailWord_3215291 prefixEnd_3215291 1100659818050323261917101 := by
  unfold tailWord_3215291
  simp only [CollatzResearch.WordTrace]
  refine ⟨117271296994557309829597727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78180864663038206553065151 117271296994557309829597727)
  ·
    refine ⟨175906945491835964744396591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117271296994557309829597727 175906945491835964744396591)
    ·
      refine ⟨263860418237753947116594887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175906945491835964744396591 263860418237753947116594887)
      ·
        refine ⟨395790627356630920674892331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263860418237753947116594887 395790627356630920674892331)
        ·
          refine ⟨593685941034946381012338497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395790627356630920674892331 593685941034946381012338497)
          ·
            refine ⟨445264455776209785759253873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593685941034946381012338497 445264455776209785759253873)
            ·
              refine ⟨333948341832157339319440405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445264455776209785759253873 333948341832157339319440405)
              ·
                refine ⟨15653828523382375280598769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 333948341832157339319440405 15653828523382375280598769)
                ·
                  refine ⟨11740371392536781460449077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15653828523382375280598769 11740371392536781460449077)
                  ·
                    refine ⟨1100659818050323261917101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11740371392536781460449077 1100659818050323261917101)
                    ·
                      rfl

theorem cell22_3215291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_3215291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215291 prefixEnd_3215291 := by exact prefixLift 3215291
  have htrace : WordTrace (prefixWord ++ tailWord_3215291) baseStart_3215291 baseEnd_3215291 := by
    simpa [prefixWord, tailWord_3215291, baseEnd_3215291] using wordTrace_append hprefix tailTrace_3215291
  have hstable : (prefixWord ++ tailWord_3215291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215291).length < 2 ^ (prefixWord ++ tailWord_3215291).sum := by decide
  have hdescent : baseEnd_3215291 < baseStart_3215291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215293 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 7]
def baseStart_3215293 : Nat := 118140960795 + 3215293 * 2 ^ 59
def prefixEnd_3215293 : Nat := 4983230072969 + 3 ^ 40 * 3215293 * 2
def baseEnd_3215293 : Nat := 366886834230398641122365

theorem tailTrace_3215293 : CollatzResearch.WordTrace tailWord_3215293 prefixEnd_3215293 366886834230398641122365 := by
  unfold tailWord_3215293
  simp only [CollatzResearch.WordTrace]
  refine ⟨117271369940550064171170533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78180913293700042780780355 117271369940550064171170533)
  ·
    refine ⟨21988381863853137032094475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117271369940550064171170533 21988381863853137032094475)
    ·
      refine ⟨32982572795779705548141713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21988381863853137032094475 32982572795779705548141713)
      ·
        refine ⟨24736929596834779161106285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32982572795779705548141713 24736929596834779161106285)
        ·
          refine ⟨9276348598813042185414857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24736929596834779161106285 9276348598813042185414857)
          ·
            refine ⟨6957261449109781639061143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9276348598813042185414857 6957261449109781639061143)
            ·
              refine ⟨10435892173664672458591715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957261449109781639061143 10435892173664672458591715)
              ·
                refine ⟨15653838260497008687887573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10435892173664672458591715 15653838260497008687887573)
                ·
                  refine ⟨366886834230398641122365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15653838260497008687887573 366886834230398641122365)
                  ·
                    rfl

theorem cell22_3215293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_3215293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215293 prefixEnd_3215293 := by exact prefixLift 3215293
  have htrace : WordTrace (prefixWord ++ tailWord_3215293) baseStart_3215293 baseEnd_3215293 := by
    simpa [prefixWord, tailWord_3215293, baseEnd_3215293] using wordTrace_append hprefix tailTrace_3215293
  have hstable : (prefixWord ++ tailWord_3215293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215293).length < 2 ^ (prefixWord ++ tailWord_3215293).sum := by decide
  have hdescent : baseEnd_3215293 < baseStart_3215293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215308 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_3215308 : Nat := 118140960795 + 3215308 * 2 ^ 59
def prefixEnd_3215308 : Nat := 4983230072969 + 3 ^ 40 * 3215308 * 2
def baseEnd_3215308 : Nat := 1100665637497740884242049

theorem tailTrace_3215308 : CollatzResearch.WordTrace tailWord_3215308 prefixEnd_3215308 1100665637497740884242049 := by
  unfold tailWord_3215308
  simp only [CollatzResearch.WordTrace]
  refine ⟨58635958517747860866483289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78181278023663814488644385 58635958517747860866483289)
  ·
    refine ⟨43976968888310895649862467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58635958517747860866483289 43976968888310895649862467)
    ·
      refine ⟨65965453332466343474793701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43976968888310895649862467 65965453332466343474793701)
      ·
        refine ⟨12368522499837439401523819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65965453332466343474793701 12368522499837439401523819)
        ·
          refine ⟨18552783749756159102285729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12368522499837439401523819 18552783749756159102285729)
          ·
            refine ⟨13914587812317119326714297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18552783749756159102285729 13914587812317119326714297)
            ·
              refine ⟨10435940859237839495035723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13914587812317119326714297 10435940859237839495035723)
              ·
                refine ⟨15653911288856759242553585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10435940859237839495035723 15653911288856759242553585)
                ·
                  refine ⟨11740433466642569431915189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15653911288856759242553585 11740433466642569431915189)
                  ·
                    refine ⟨1100665637497740884242049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11740433466642569431915189 1100665637497740884242049)
                    ·
                      rfl

theorem cell22_3215308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_3215308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215308 prefixEnd_3215308 := by exact prefixLift 3215308
  have htrace : WordTrace (prefixWord ++ tailWord_3215308) baseStart_3215308 baseEnd_3215308 := by
    simpa [prefixWord, tailWord_3215308, baseEnd_3215308] using wordTrace_append hprefix tailTrace_3215308
  have hstable : (prefixWord ++ tailWord_3215308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215308).length < 2 ^ (prefixWord ++ tailWord_3215308).sum := by decide
  have hdescent : baseEnd_3215308 < baseStart_3215308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215310 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_3215310 : Nat := 118140960795 + 3215310 * 2 ^ 59
def prefixEnd_3215310 : Nat := 4983230072969 + 3 ^ 40 * 3215310 * 2
def baseEnd_3215310 : Nat := 366888774046204515230681

theorem tailTrace_3215310 : CollatzResearch.WordTrace tailWord_3215310 prefixEnd_3215310 366888774046204515230681 := by
  unfold tailWord_3215310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14658998747686059509317423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78181326654325650716359589 14658998747686059509317423)
  ·
    refine ⟨21988498121529089263976135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14658998747686059509317423 21988498121529089263976135)
    ·
      refine ⟨32982747182293633895964203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21988498121529089263976135 32982747182293633895964203)
      ·
        refine ⟨49474120773440450843946305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32982747182293633895964203 49474120773440450843946305)
        ·
          refine ⟨37105590580080338132959729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49474120773440450843946305 37105590580080338132959729)
          ·
            refine ⟨27829192935060253599719797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37105590580080338132959729 27829192935060253599719797)
            ·
              refine ⟨2608986837661898774973731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27829192935060253599719797 2608986837661898774973731)
              ·
                refine ⟨3913480256492848162460597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608986837661898774973731 3913480256492848162460597)
                ·
                  refine ⟨366888774046204515230681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3913480256492848162460597 366888774046204515230681)
                  ·
                    rfl

theorem cell22_3215310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_3215310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215310 prefixEnd_3215310 := by exact prefixLift 3215310
  have htrace : WordTrace (prefixWord ++ tailWord_3215310) baseStart_3215310 baseEnd_3215310 := by
    simpa [prefixWord, tailWord_3215310, baseEnd_3215310] using wordTrace_append hprefix tailTrace_3215310
  have hstable : (prefixWord ++ tailWord_3215310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215310).length < 2 ^ (prefixWord ++ tailWord_3215310).sum := by decide
  have hdescent : baseEnd_3215310 < baseStart_3215310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215351 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 10]
def baseStart_3215351 : Nat := 118140960795 + 3215351 * 2 ^ 59
def prefixEnd_3215351 : Nat := 4983230072969 + 3 ^ 40 * 3215351 * 2
def baseEnd_3215351 : Nat := 1100680357276503105416917

theorem tailTrace_3215351 : CollatzResearch.WordTrace tailWord_3215351 prefixEnd_3215351 1100680357276503105416917 := by
  unfold tailWord_3215351
  simp only [CollatzResearch.WordTrace]
  refine ⟨117273485374339940076781907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78182323582893293384521271 117273485374339940076781907)
  ·
    refine ⟨175910228061509910115172861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117273485374339940076781907 175910228061509910115172861)
    ·
      refine ⟨65966335523066216293189823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175910228061509910115172861 65966335523066216293189823)
      ·
        refine ⟨98949503284599324439784735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65966335523066216293189823 98949503284599324439784735)
        ·
          refine ⟨148424254926898986659677103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98949503284599324439784735 148424254926898986659677103)
          ·
            refine ⟨222636382390348479989515655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148424254926898986659677103 222636382390348479989515655)
            ·
              refine ⟨333954573585522719984273483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222636382390348479989515655 333954573585522719984273483)
              ·
                refine ⟨500931860378284079976410225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333954573585522719984273483 500931860378284079976410225)
                ·
                  refine ⟨375698895283713059982307669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500931860378284079976410225 375698895283713059982307669)
                  ·
                    refine ⟨1100680357276503105416917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 375698895283713059982307669 1100680357276503105416917)
                    ·
                      rfl

theorem cell22_3215351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_3215351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215351 prefixEnd_3215351 := by exact prefixLift 3215351
  have htrace : WordTrace (prefixWord ++ tailWord_3215351) baseStart_3215351 baseEnd_3215351 := by
    simpa [prefixWord, tailWord_3215351, baseEnd_3215351] using wordTrace_append hprefix tailTrace_3215351
  have hstable : (prefixWord ++ tailWord_3215351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215351).length < 2 ^ (prefixWord ++ tailWord_3215351).sum := by decide
  have hdescent : baseEnd_3215351 < baseStart_3215351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215368 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_3215368 : Nat := 118140960795 + 3215368 * 2 ^ 59
def prefixEnd_3215368 : Nat := 4983230072969 + 3 ^ 40 * 3215368 * 2
def baseEnd_3215368 : Nat := 1100686176723920727741865

theorem tailTrace_3215368 : CollatzResearch.WordTrace tailWord_3215368 prefixEnd_3215368 1100686176723920727741865 := by
  unfold tailWord_3215368
  simp only [CollatzResearch.WordTrace]
  refine ⟨58637052707639175990075379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78182736943518901320100505 58637052707639175990075379)
  ·
    refine ⟨87955579061458763985113069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58637052707639175990075379 87955579061458763985113069)
    ·
      refine ⟨32983342148047036494417401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87955579061458763985113069 32983342148047036494417401)
      ·
        refine ⟨24737506611035277370813051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32983342148047036494417401 24737506611035277370813051)
        ·
          refine ⟨37106259916552916056219577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24737506611035277370813051 37106259916552916056219577)
          ·
            refine ⟨27829694937414687042164683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37106259916552916056219577 27829694937414687042164683)
            ·
              refine ⟨41744542406122030563247025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27829694937414687042164683 41744542406122030563247025)
              ·
                refine ⟨31308406804591522922435269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41744542406122030563247025 31308406804591522922435269)
                ·
                  refine ⟨5870326275860910547956613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31308406804591522922435269 5870326275860910547956613)
                  ·
                    refine ⟨1100686176723920727741865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5870326275860910547956613 1100686176723920727741865)
                    ·
                      rfl

theorem cell22_3215368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_3215368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215368 prefixEnd_3215368 := by exact prefixLift 3215368
  have htrace : WordTrace (prefixWord ++ tailWord_3215368) baseStart_3215368 baseEnd_3215368 := by
    simpa [prefixWord, tailWord_3215368, baseEnd_3215368] using wordTrace_append hprefix tailTrace_3215368
  have hstable : (prefixWord ++ tailWord_3215368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215368).length < 2 ^ (prefixWord ++ tailWord_3215368).sum := by decide
  have hdescent : baseEnd_3215368 < baseStart_3215368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215400 : List Nat := [2, 1, 5, 3, 1, 10]
def baseStart_3215400 : Nat := 118140960795 + 3215400 * 2 ^ 59
def prefixEnd_3215400 : Nat := 4983230072969 + 3 ^ 40 * 3215400 * 2
def baseEnd_3215400 : Nat := 13588853468862756925207

theorem tailTrace_3215400 : CollatzResearch.WordTrace tailWord_3215400 prefixEnd_3215400 13588853468862756925207 := by
  unfold tailWord_3215400
  simp only [CollatzResearch.WordTrace]
  refine ⟨58637636275581210722657827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78183515034108280963543769 58637636275581210722657827)
  ·
    refine ⟨87956454413371816083986741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58637636275581210722657827 87956454413371816083986741)
    ·
      refine ⟨8245917601253607757873757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87956454413371816083986741 8245917601253607757873757)
      ·
        refine ⟨3092219100470102909202659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8245917601253607757873757 3092219100470102909202659)
        ·
          refine ⟨4638328650705154363803989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092219100470102909202659 4638328650705154363803989)
          ·
            refine ⟨13588853468862756925207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4638328650705154363803989 13588853468862756925207)
            ·
              rfl

theorem cell22_3215400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 10].length) (baseStart_3215400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215400 prefixEnd_3215400 := by exact prefixLift 3215400
  have htrace : WordTrace (prefixWord ++ tailWord_3215400) baseStart_3215400 baseEnd_3215400 := by
    simpa [prefixWord, tailWord_3215400, baseEnd_3215400] using wordTrace_append hprefix tailTrace_3215400
  have hstable : (prefixWord ++ tailWord_3215400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215400).length < 2 ^ (prefixWord ++ tailWord_3215400).sum := by decide
  have hdescent : baseEnd_3215400 < baseStart_3215400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215413 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3215413 : Nat := 118140960795 + 3215413 * 2 ^ 59
def prefixEnd_3215413 : Nat := 4983230072969 + 3 ^ 40 * 3215413 * 2
def baseEnd_3215413 : Nat := 1100701581143555610366727

theorem tailTrace_3215413 : CollatzResearch.WordTrace tailWord_3215413 prefixEnd_3215413 1100701581143555610366727 := by
  unfold tailWord_3215413
  simp only [CollatzResearch.WordTrace]
  refine ⟨117275746700115324665538893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78183831133410216443692595 117275746700115324665538893)
  ·
    refine ⟨43978405012543246749577085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117275746700115324665538893 43978405012543246749577085)
    ·
      refine ⟨16491901879703717531091407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43978405012543246749577085 16491901879703717531091407)
      ·
        refine ⟨24737852819555576296637111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16491901879703717531091407 24737852819555576296637111)
        ·
          refine ⟨37106779229333364444955667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24737852819555576296637111 37106779229333364444955667)
          ·
            refine ⟨55660168844000046667433501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37106779229333364444955667 55660168844000046667433501)
            ·
              refine ⟨20872563316500017500287563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55660168844000046667433501 20872563316500017500287563)
              ·
                refine ⟨31308844974750026250431345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20872563316500017500287563 31308844974750026250431345)
                ·
                  refine ⟨23481633731062519687823509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31308844974750026250431345 23481633731062519687823509)
                  ·
                    refine ⟨1100701581143555610366727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23481633731062519687823509 1100701581143555610366727)
                    ·
                      rfl

theorem cell22_3215413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3215413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215413 prefixEnd_3215413 := by exact prefixLift 3215413
  have htrace : WordTrace (prefixWord ++ tailWord_3215413) baseStart_3215413 baseEnd_3215413 := by
    simpa [prefixWord, tailWord_3215413, baseEnd_3215413] using wordTrace_append hprefix tailTrace_3215413
  have hstable : (prefixWord ++ tailWord_3215413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215413).length < 2 ^ (prefixWord ++ tailWord_3215413).sum := by decide
  have hdescent : baseEnd_3215413 < baseStart_3215413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215417 : List Nat := [1, 2, 1, 5, 4, 1, 1, 7]
def baseStart_3215417 : Nat := 118140960795 + 3215417 * 2 ^ 59
def prefixEnd_3215417 : Nat := 4983230072969 + 3 ^ 40 * 3215417 * 2
def baseEnd_3215417 : Nat := 122300327825033437029635

theorem tailTrace_3215417 : CollatzResearch.WordTrace tailWord_3215417 prefixEnd_3215417 122300327825033437029635 := by
  unfold tailWord_3215417
  simp only [CollatzResearch.WordTrace]
  refine ⟨117275892592100833348684505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78183928394733888899123003 117275892592100833348684505)
  ·
    refine ⟨87956919444075625011513379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117275892592100833348684505 87956919444075625011513379)
    ·
      refine ⟨131935379166113437517270069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87956919444075625011513379 131935379166113437517270069)
      ·
        refine ⟨12368941796823134767244069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131935379166113437517270069 12368941796823134767244069)
        ·
          refine ⟨2319176586904337768858263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12368941796823134767244069 2319176586904337768858263)
          ·
            refine ⟨3478764880356506653287395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319176586904337768858263 3478764880356506653287395)
            ·
              refine ⟨5218147320534759979931093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3478764880356506653287395 5218147320534759979931093)
              ·
                refine ⟨122300327825033437029635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5218147320534759979931093 122300327825033437029635)
                ·
                  rfl

theorem cell22_3215417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 7].length) (baseStart_3215417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215417 prefixEnd_3215417 := by exact prefixLift 3215417
  have htrace : WordTrace (prefixWord ++ tailWord_3215417) baseStart_3215417 baseEnd_3215417 := by
    simpa [prefixWord, tailWord_3215417, baseEnd_3215417] using wordTrace_append hprefix tailTrace_3215417
  have hstable : (prefixWord ++ tailWord_3215417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215417).length < 2 ^ (prefixWord ++ tailWord_3215417).sum := by decide
  have hdescent : baseEnd_3215417 < baseStart_3215417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215492 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_3215492 : Nat := 118140960795 + 3215492 * 2 ^ 59
def prefixEnd_3215492 : Nat := 4983230072969 + 3 ^ 40 * 3215492 * 2
def baseEnd_3215492 : Nat := 1100728624458025737641485

theorem tailTrace_3215492 : CollatzResearch.WordTrace tailWord_3215492 prefixEnd_3215492 1100728624458025737641485 := by
  unfold tailWord_3215492
  simp only [CollatzResearch.WordTrace]
  refine ⟨58639314033414560578832365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78185752044552747438443153 58639314033414560578832365)
  ·
    refine ⟨21989742762530460217062137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58639314033414560578832365 21989742762530460217062137)
    ·
      refine ⟨16492307071897845162796603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21989742762530460217062137 16492307071897845162796603)
      ·
        refine ⟨24738460607846767744194905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16492307071897845162796603 24738460607846767744194905)
        ·
          refine ⟨18553845455885075808146179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24738460607846767744194905 18553845455885075808146179)
          ·
            refine ⟨27830768183827613712219269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18553845455885075808146179 27830768183827613712219269)
            ·
              refine ⟨5218269034467677571041113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27830768183827613712219269 5218269034467677571041113)
              ·
                refine ⟨3913701775850758178280835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5218269034467677571041113 3913701775850758178280835)
                ·
                  refine ⟨5870552663776137267421253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913701775850758178280835 5870552663776137267421253)
                  ·
                    refine ⟨1100728624458025737641485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5870552663776137267421253 1100728624458025737641485)
                    ·
                      rfl

theorem cell22_3215492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_3215492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215492 prefixEnd_3215492 := by exact prefixLift 3215492
  have htrace : WordTrace (prefixWord ++ tailWord_3215492) baseStart_3215492 baseEnd_3215492 := by
    simpa [prefixWord, tailWord_3215492, baseEnd_3215492] using wordTrace_append hprefix tailTrace_3215492
  have hstable : (prefixWord ++ tailWord_3215492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215492).length < 2 ^ (prefixWord ++ tailWord_3215492).sum := by decide
  have hdescent : baseEnd_3215492 < baseStart_3215492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215520 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_3215520 : Nat := 118140960795 + 3215520 * 2 ^ 59
def prefixEnd_3215520 : Nat := 4983230072969 + 3 ^ 40 * 3215520 * 2
def baseEnd_3215520 : Nat := 1100738209430242997941399

theorem tailTrace_3215520 : CollatzResearch.WordTrace tailWord_3215520 prefixEnd_3215520 1100738209430242997941399 := by
  unfold tailWord_3215520
  simp only [CollatzResearch.WordTrace]
  refine ⟨58639824655363840969842007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78186432873818454626456009 58639824655363840969842007)
  ·
    refine ⟨87959736983045761454763011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58639824655363840969842007 87959736983045761454763011)
    ·
      refine ⟨131939605474568642182144517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87959736983045761454763011 131939605474568642182144517)
      ·
        refine ⟨24738676026481620409152097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131939605474568642182144517 24738676026481620409152097)
        ·
          refine ⟨18554007019861215306864073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24738676026481620409152097 18554007019861215306864073)
          ·
            refine ⟨13915505264895911480148055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18554007019861215306864073 13915505264895911480148055)
            ·
              refine ⟨20873257897343867220222083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13915505264895911480148055 20873257897343867220222083)
              ·
                refine ⟨31309886846015800830333125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20873257897343867220222083 31309886846015800830333125)
                ·
                  refine ⟨5870603783627962655687461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31309886846015800830333125 5870603783627962655687461)
                  ·
                    refine ⟨1100738209430242997941399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5870603783627962655687461 1100738209430242997941399)
                    ·
                      rfl

theorem cell22_3215520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_3215520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215520 prefixEnd_3215520 := by exact prefixLift 3215520
  have htrace : WordTrace (prefixWord ++ tailWord_3215520) baseStart_3215520 baseEnd_3215520 := by
    simpa [prefixWord, tailWord_3215520, baseEnd_3215520] using wordTrace_append hprefix tailTrace_3215520
  have hstable : (prefixWord ++ tailWord_3215520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215520).length < 2 ^ (prefixWord ++ tailWord_3215520).sum := by decide
  have hdescent : baseEnd_3215520 < baseStart_3215520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215524 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 6]
def baseStart_3215524 : Nat := 118140960795 + 3215524 * 2 ^ 59
def prefixEnd_3215524 : Nat := 4983230072969 + 3 ^ 40 * 3215524 * 2
def baseEnd_3215524 : Nat := 366913192903996106947129

theorem tailTrace_3215524 : CollatzResearch.WordTrace tailWord_3215524 prefixEnd_3215524 366913192903996106947129 := by
  unfold tailWord_3215524
  simp only [CollatzResearch.WordTrace]
  refine ⟨58639897601356595311414813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78186530135142127081886417 58639897601356595311414813)
  ·
    refine ⟨21989961600508723241780555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58639897601356595311414813 21989961600508723241780555)
    ·
      refine ⟨32984942400763084862670833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21989961600508723241780555 32984942400763084862670833)
      ·
        refine ⟨24738706800572313647003125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32984942400763084862670833 24738706800572313647003125)
        ·
          refine ⟨2319253762553654404406543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24738706800572313647003125 2319253762553654404406543)
          ·
            refine ⟨3478880643830481606609815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319253762553654404406543 3478880643830481606609815)
            ·
              refine ⟨5218320965745722409914723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3478880643830481606609815 5218320965745722409914723)
              ·
                refine ⟨7827481448618583614872085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218320965745722409914723 7827481448618583614872085)
                ·
                  refine ⟨366913192903996106947129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7827481448618583614872085 366913192903996106947129)
                  ·
                    rfl

theorem cell22_3215524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_3215524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215524 prefixEnd_3215524 := by exact prefixLift 3215524
  have htrace : WordTrace (prefixWord ++ tailWord_3215524) baseStart_3215524 baseEnd_3215524 := by
    simpa [prefixWord, tailWord_3215524, baseEnd_3215524] using wordTrace_append hprefix tailTrace_3215524
  have hstable : (prefixWord ++ tailWord_3215524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215524).length < 2 ^ (prefixWord ++ tailWord_3215524).sum := by decide
  have hdescent : baseEnd_3215524 < baseStart_3215524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215584 : List Nat := [2, 1, 1, 3, 1, 3, 3, 4, 1, 3]
def baseStart_3215584 : Nat := 118140960795 + 3215584 * 2 ^ 59
def prefixEnd_3215584 : Nat := 4983230072969 + 3 ^ 40 * 3215584 * 2
def baseEnd_3215584 : Nat := 1100760117938168164341203

theorem tailTrace_3215584 : CollatzResearch.WordTrace tailWord_3215584 prefixEnd_3215584 1100760117938168164341203 := by
  unfold tailWord_3215584
  simp only [CollatzResearch.WordTrace]
  refine ⟨58640991791247910435006903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78187989054997213913342537 58640991791247910435006903)
  ·
    refine ⟨87961487686871865652510355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58640991791247910435006903 87961487686871865652510355)
    ·
      refine ⟨131942231530307798478765533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87961487686871865652510355 131942231530307798478765533)
      ·
        refine ⟨49478336823865424429537075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131942231530307798478765533 49478336823865424429537075)
        ·
          refine ⟨74217505235798136644305613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49478336823865424429537075 74217505235798136644305613)
          ·
            refine ⟨27831564463424301241614605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74217505235798136644305613 27831564463424301241614605)
            ·
              refine ⟨10436836673784112965605477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27831564463424301241614605 10436836673784112965605477)
              ·
                refine ⟨1956906876334521181051027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10436836673784112965605477 1956906876334521181051027)
                ·
                  refine ⟨2935360314501781771576541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956906876334521181051027 2935360314501781771576541)
                  ·
                    refine ⟨1100760117938168164341203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2935360314501781771576541 1100760117938168164341203)
                    ·
                      rfl

theorem cell22_3215584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 1, 3].length) (baseStart_3215584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215584 prefixEnd_3215584 := by exact prefixLift 3215584
  have htrace : WordTrace (prefixWord ++ tailWord_3215584) baseStart_3215584 baseEnd_3215584 := by
    simpa [prefixWord, tailWord_3215584, baseEnd_3215584] using wordTrace_append hprefix tailTrace_3215584
  have hstable : (prefixWord ++ tailWord_3215584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215584).length < 2 ^ (prefixWord ++ tailWord_3215584).sum := by decide
  have hdescent : baseEnd_3215584 < baseStart_3215584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215595 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 2, 5]
def baseStart_3215595 : Nat := 118140960795 + 3215595 * 2 ^ 59
def prefixEnd_3215595 : Nat := 4983230072969 + 3 ^ 40 * 3215595 * 2
def baseEnd_3215595 : Nat := 1100763883462967802316169

theorem tailTrace_3215595 : CollatzResearch.WordTrace tailWord_3215595 prefixEnd_3215595 1100763883462967802316169 := by
  unfold tailWord_3215595
  simp only [CollatzResearch.WordTrace]
  refine ⟨117282384785455969748664239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78188256523637313165776159 117282384785455969748664239)
  ·
    refine ⟨175923577178183954622996359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117282384785455969748664239 175923577178183954622996359)
    ·
      refine ⟨263885365767275931934494539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175923577178183954622996359 263885365767275931934494539)
      ·
        refine ⟨395828048650913897901741809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263885365767275931934494539 395828048650913897901741809)
        ·
          refine ⟨296871036488185423426306357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395828048650913897901741809 296871036488185423426306357)
          ·
            refine ⟨27831659670767383446216221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296871036488185423426306357 27831659670767383446216221)
            ·
              refine ⟨10436872376537768792331083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27831659670767383446216221 10436872376537768792331083)
              ·
                refine ⟨15655308564806653188496625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10436872376537768792331083 15655308564806653188496625)
                ·
                  refine ⟨11741481423604989891372469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15655308564806653188496625 11741481423604989891372469)
                  ·
                    refine ⟨1100763883462967802316169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11741481423604989891372469 1100763883462967802316169)
                    ·
                      rfl

theorem cell22_3215595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_3215595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215595 prefixEnd_3215595 := by exact prefixLift 3215595
  have htrace : WordTrace (prefixWord ++ tailWord_3215595) baseStart_3215595 baseEnd_3215595 := by
    simpa [prefixWord, tailWord_3215595, baseEnd_3215595] using wordTrace_append hprefix tailTrace_3215595
  have hstable : (prefixWord ++ tailWord_3215595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215595).length < 2 ^ (prefixWord ++ tailWord_3215595).sum := by decide
  have hdescent : baseEnd_3215595 < baseStart_3215595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215618 : List Nat := [3, 4, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3215618 : Nat := 118140960795 + 3215618 * 2 ^ 59
def prefixEnd_3215618 : Nat := 4983230072969 + 3 ^ 40 * 3215618 * 2
def baseEnd_3215618 : Nat := 1100771756833003408991099

theorem tailTrace_3215618 : CollatzResearch.WordTrace tailWord_3215618 prefixEnd_3215618 1100771756833003408991099 := by
  unfold tailWord_3215618
  simp only [CollatzResearch.WordTrace]
  refine ⟨29320805916093161169187877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78188815776248429784501005 29320805916093161169187877)
  ·
    refine ⟨5497651109267467719222727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29320805916093161169187877 5497651109267467719222727)
    ·
      refine ⟨8246476663901201578834091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5497651109267467719222727 8246476663901201578834091)
      ·
        refine ⟨12369714995851802368251137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8246476663901201578834091 12369714995851802368251137)
        ·
          refine ⟨9277286246888851776188353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12369714995851802368251137 9277286246888851776188353)
          ·
            refine ⟨6957964685166638832141265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9277286246888851776188353 6957964685166638832141265)
            ·
              refine ⟨5218473513874979124105949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6957964685166638832141265 5218473513874979124105949)
              ·
                refine ⟨1956927567703117171539731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5218473513874979124105949 1956927567703117171539731)
                ·
                  refine ⟨2935391351554675757309597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956927567703117171539731 2935391351554675757309597)
                  ·
                    refine ⟨1100771756833003408991099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2935391351554675757309597 1100771756833003408991099)
                    ·
                      rfl

theorem cell22_3215618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3215618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215618 prefixEnd_3215618 := by exact prefixLift 3215618
  have htrace : WordTrace (prefixWord ++ tailWord_3215618) baseStart_3215618 baseEnd_3215618 := by
    simpa [prefixWord, tailWord_3215618, baseEnd_3215618] using wordTrace_append hprefix tailTrace_3215618
  have hstable : (prefixWord ++ tailWord_3215618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215618).length < 2 ^ (prefixWord ++ tailWord_3215618).sum := by decide
  have hdescent : baseEnd_3215618 < baseStart_3215618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215627 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 1, 4]
def baseStart_3215627 : Nat := 118140960795 + 3215627 * 2 ^ 59
def prefixEnd_3215627 : Nat := 4983230072969 + 3 ^ 40 * 3215627 * 2
def baseEnd_3215627 : Nat := 1100774837716930385516071

theorem tailTrace_3215627 : CollatzResearch.WordTrace tailWord_3215627 prefixEnd_3215627 1100774837716930385516071 := by
  unfold tailWord_3215627
  simp only [CollatzResearch.WordTrace]
  refine ⟨117283551921340039213829135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78189034614226692809219423 117283551921340039213829135)
  ·
    refine ⟨175925327882010058820743703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117283551921340039213829135 175925327882010058820743703)
    ·
      refine ⟨263887991823015088231115555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175925327882010058820743703 263887991823015088231115555)
      ·
        refine ⟨395831987734522632346673333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263887991823015088231115555 395831987734522632346673333)
        ·
          refine ⟨37109248850111496782500625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 395831987734522632346673333 37109248850111496782500625)
          ·
            refine ⟨27831936637583622586875469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37109248850111496782500625 27831936637583622586875469)
            ·
              refine ⟨10436976239093858470078301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27831936637583622586875469 10436976239093858470078301)
              ·
                refine ⟨3913866089660196926279363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10436976239093858470078301 3913866089660196926279363)
                ·
                  refine ⟨5870799134490295389419045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913866089660196926279363 5870799134490295389419045)
                  ·
                    refine ⟨1100774837716930385516071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5870799134490295389419045 1100774837716930385516071)
                    ·
                      rfl

theorem cell22_3215627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 4].length) (baseStart_3215627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215627 prefixEnd_3215627 := by exact prefixLift 3215627
  have htrace : WordTrace (prefixWord ++ tailWord_3215627) baseStart_3215627 baseEnd_3215627 := by
    simpa [prefixWord, tailWord_3215627, baseEnd_3215627] using wordTrace_append hprefix tailTrace_3215627
  have hstable : (prefixWord ++ tailWord_3215627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215627).length < 2 ^ (prefixWord ++ tailWord_3215627).sum := by decide
  have hdescent : baseEnd_3215627 < baseStart_3215627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215708 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_3215708 : Nat := 118140960795 + 3215708 * 2 ^ 59
def prefixEnd_3215708 : Nat := 4983230072969 + 3 ^ 40 * 3215708 * 2
def baseEnd_3215708 : Nat := 1100802565672273174240823

theorem tailTrace_3215708 : CollatzResearch.WordTrace tailWord_3215708 prefixEnd_3215708 1100802565672273174240823 := by
  unfold tailWord_3215708
  simp only [CollatzResearch.WordTrace]
  refine ⟨58643253117023295023763889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78191004156031060031685185 58643253117023295023763889)
  ·
    refine ⟨43982439837767471267822917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58643253117023295023763889 43982439837767471267822917)
    ·
      refine ⟨8246707469581400862716797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43982439837767471267822917 8246707469581400862716797)
      ·
        refine ⟨3092515301093025323518799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8246707469581400862716797 3092515301093025323518799)
        ·
          refine ⟨4638772951639537985278199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092515301093025323518799 4638772951639537985278199)
          ·
            refine ⟨6958159427459306977917299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638772951639537985278199 6958159427459306977917299)
            ·
              refine ⟨10437239141188960466875949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6958159427459306977917299 10437239141188960466875949)
              ·
                refine ⟨3913964677945860175078481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10437239141188960466875949 3913964677945860175078481)
                ·
                  refine ⟨2935473508459395131308861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3913964677945860175078481 2935473508459395131308861)
                  ·
                    refine ⟨1100802565672273174240823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2935473508459395131308861 1100802565672273174240823)
                    ·
                      rfl

theorem cell22_3215708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_3215708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215708 prefixEnd_3215708 := by exact prefixLift 3215708
  have htrace : WordTrace (prefixWord ++ tailWord_3215708) baseStart_3215708 baseEnd_3215708 := by
    simpa [prefixWord, tailWord_3215708, baseEnd_3215708] using wordTrace_append hprefix tailTrace_3215708
  have hstable : (prefixWord ++ tailWord_3215708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215708).length < 2 ^ (prefixWord ++ tailWord_3215708).sum := by decide
  have hdescent : baseEnd_3215708 < baseStart_3215708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215753 : List Nat := [1, 2, 1, 1, 6, 1, 4, 2, 1, 3]
def baseStart_3215753 : Nat := 118140960795 + 3215753 * 2 ^ 59
def prefixEnd_3215753 : Nat := 4983230072969 + 3 ^ 40 * 3215753 * 2
def baseEnd_3215753 : Nat := 1100817970091908056865685

theorem tailTrace_3215753 : CollatzResearch.WordTrace tailWord_3215753 prefixEnd_3215753 1100817970091908056865685 := by
  unfold tailWord_3215753
  simp only [CollatzResearch.WordTrace]
  refine ⟨117288147518883562732915913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78192098345922375155277275 117288147518883562732915913)
  ·
    refine ⟨87966110639162672049686935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117288147518883562732915913 87966110639162672049686935)
    ·
      refine ⟨131949165958744008074530403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87966110639162672049686935 131949165958744008074530403)
      ·
        refine ⟨197923748938116012111795605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131949165958744008074530403 197923748938116012111795605)
        ·
          refine ⟨9277675731474188067740419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197923748938116012111795605 9277675731474188067740419)
          ·
            refine ⟨13916513597211282101610629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277675731474188067740419 13916513597211282101610629)
            ·
              refine ⟨2609346299477115394051993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13916513597211282101610629 2609346299477115394051993)
              ·
                refine ⟨1957009724607836545538995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609346299477115394051993 1957009724607836545538995)
                ·
                  refine ⟨2935514586911754818308493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957009724607836545538995 2935514586911754818308493)
                  ·
                    refine ⟨1100817970091908056865685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2935514586911754818308493 1100817970091908056865685)
                    ·
                      rfl

theorem cell22_3215753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 3].length) (baseStart_3215753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215753 prefixEnd_3215753 := by exact prefixLift 3215753
  have htrace : WordTrace (prefixWord ++ tailWord_3215753) baseStart_3215753 baseEnd_3215753 := by
    simpa [prefixWord, tailWord_3215753, baseEnd_3215753] using wordTrace_append hprefix tailTrace_3215753
  have hstable : (prefixWord ++ tailWord_3215753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215753).length < 2 ^ (prefixWord ++ tailWord_3215753).sum := by decide
  have hdescent : baseEnd_3215753 < baseStart_3215753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215822 : List Nat := [4, 1, 1, 1, 2, 1, 1, 11]
def baseStart_3215822 : Nat := 118140960795 + 3215822 * 2 ^ 59
def prefixEnd_3215822 : Nat := 4983230072969 + 3 ^ 40 * 3215822 * 2
def baseEnd_3215822 : Nat := 122315732244668319654497

theorem tailTrace_3215822 : CollatzResearch.WordTrace tailWord_3215822 prefixEnd_3215822 122315732244668319654497 := by
  unfold tailWord_3215822
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661333019454198439647215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78193776103755725011451813 14661333019454198439647215)
  ·
    refine ⟨21991999529181297659470823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14661333019454198439647215 21991999529181297659470823)
    ·
      refine ⟨32987999293771946489206235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21991999529181297659470823 32987999293771946489206235)
      ·
        refine ⟨49481998940657919733809353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32987999293771946489206235 49481998940657919733809353)
        ·
          refine ⟨37111499205493439800357015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49481998940657919733809353 37111499205493439800357015)
          ·
            refine ⟨55667248808240159700535523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37111499205493439800357015 55667248808240159700535523)
            ·
              refine ⟨83500873212360239550803285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55667248808240159700535523 83500873212360239550803285)
              ·
                refine ⟨122315732244668319654497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 83500873212360239550803285 122315732244668319654497)
                ·
                  rfl

theorem cell22_3215822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_3215822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215822 prefixEnd_3215822 := by exact prefixLift 3215822
  have htrace : WordTrace (prefixWord ++ tailWord_3215822) baseStart_3215822 baseEnd_3215822 := by
    simpa [prefixWord, tailWord_3215822, baseEnd_3215822] using wordTrace_append hprefix tailTrace_3215822
  have hstable : (prefixWord ++ tailWord_3215822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215822).length < 2 ^ (prefixWord ++ tailWord_3215822).sum := by decide
  have hdescent : baseEnd_3215822 < baseStart_3215822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215839 : List Nat := [1, 1, 2, 3, 3, 2, 4, 6]
def baseStart_3215839 : Nat := 118140960795 + 3215839 * 2 ^ 59
def prefixEnd_3215839 : Nat := 4983230072969 + 3 ^ 40 * 3215839 * 2
def baseEnd_3215839 : Nat := 122316378849936944357269

theorem tailTrace_3215839 : CollatzResearch.WordTrace tailWord_3215839 prefixEnd_3215839 122316378849936944357269 := by
  unfold tailWord_3215839
  simp only [CollatzResearch.WordTrace]
  refine ⟨117291284196571999420546571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78194189464381332947031047 117291284196571999420546571)
  ·
    refine ⟨175936926294857999130819857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117291284196571999420546571 175936926294857999130819857)
    ·
      refine ⟨131952694721143499348114893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175936926294857999130819857 131952694721143499348114893)
      ·
        refine ⟨49482260520428812255543085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131952694721143499348114893 49482260520428812255543085)
        ·
          refine ⟨18555847695160804595828657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49482260520428812255543085 18555847695160804595828657)
          ·
            refine ⟨13916885771370603446871493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18555847695160804595828657 13916885771370603446871493)
            ·
              refine ⟨2609416082131988146288405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13916885771370603446871493 2609416082131988146288405)
              ·
                refine ⟨122316378849936944357269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2609416082131988146288405 122316378849936944357269)
                ·
                  rfl

theorem cell22_3215839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 6].length) (baseStart_3215839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215839 prefixEnd_3215839 := by exact prefixLift 3215839
  have htrace : WordTrace (prefixWord ++ tailWord_3215839) baseStart_3215839 baseEnd_3215839 := by
    simpa [prefixWord, tailWord_3215839, baseEnd_3215839] using wordTrace_append hprefix tailTrace_3215839
  have hstable : (prefixWord ++ tailWord_3215839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215839).length < 2 ^ (prefixWord ++ tailWord_3215839).sum := by decide
  have hdescent : baseEnd_3215839 < baseStart_3215839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215845 : List Nat := [1, 3, 1, 5, 3, 1, 1, 3, 4]
def baseStart_3215845 : Nat := 118140960795 + 3215845 * 2 ^ 59
def prefixEnd_3215845 : Nat := 4983230072969 + 3 ^ 40 * 3215845 * 2
def baseEnd_3215845 : Nat := 366949821190683494521801

theorem tailTrace_3215845 : CollatzResearch.WordTrace tailWord_3215845 prefixEnd_3215845 366949821190683494521801 := by
  unfold tailWord_3215845
  simp only [CollatzResearch.WordTrace]
  refine ⟨117291503034550262445264989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78194335356366841630176659 117291503034550262445264989)
  ·
    refine ⟨43984313637956348416974371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117291503034550262445264989 43984313637956348416974371)
    ·
      refine ⟨65976470456934522625461557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43984313637956348416974371 65976470456934522625461557)
      ·
        refine ⟨6185294105337611496137021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65976470456934522625461557 6185294105337611496137021)
        ·
          refine ⟨2319485289501604311051383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6185294105337611496137021 2319485289501604311051383)
          ·
            refine ⟨3479227934252406466577075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319485289501604311051383 3479227934252406466577075)
            ·
              refine ⟨5218841901378609699865613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479227934252406466577075 5218841901378609699865613)
              ·
                refine ⟨1957065713016978637449605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5218841901378609699865613 1957065713016978637449605)
                ·
                  refine ⟨366949821190683494521801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957065713016978637449605 366949821190683494521801)
                  ·
                    rfl

theorem cell22_3215845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_3215845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215845 prefixEnd_3215845 := by exact prefixLift 3215845
  have htrace : WordTrace (prefixWord ++ tailWord_3215845) baseStart_3215845 baseEnd_3215845 := by
    simpa [prefixWord, tailWord_3215845, baseEnd_3215845] using wordTrace_append hprefix tailTrace_3215845
  have hstable : (prefixWord ++ tailWord_3215845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215845).length < 2 ^ (prefixWord ++ tailWord_3215845).sum := by decide
  have hdescent : baseEnd_3215845 < baseStart_3215845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215897 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_3215897 : Nat := 118140960795 + 3215897 * 2 ^ 59
def prefixEnd_3215897 : Nat := 4983230072969 + 3 ^ 40 * 3215897 * 2
def baseEnd_3215897 : Nat := 1100867264234739681265243

theorem tailTrace_3215897 : CollatzResearch.WordTrace tailWord_3215897 prefixEnd_3215897 1100867264234739681265243 := by
  unfold tailWord_3215897
  simp only [CollatzResearch.WordTrace]
  refine ⟨117293399630361875326157945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78195599753574583550771963 117293399630361875326157945)
  ·
    refine ⟨87970049722771406494618459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117293399630361875326157945 87970049722771406494618459)
    ·
      refine ⟨131955074584157109741927689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87970049722771406494618459 131955074584157109741927689)
      ·
        refine ⟨98966305938117832306445767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131955074584157109741927689 98966305938117832306445767)
        ·
          refine ⟨148449458907176748459668651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98966305938117832306445767 148449458907176748459668651)
          ·
            refine ⟨222674188360765122689502977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148449458907176748459668651 222674188360765122689502977)
            ·
              refine ⟨167005641270573842017127233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222674188360765122689502977 167005641270573842017127233)
              ·
                refine ⟨125254230952930381512845425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167005641270573842017127233 125254230952930381512845425)
                ·
                  refine ⟨93940673214697786134634069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125254230952930381512845425 93940673214697786134634069)
                  ·
                    refine ⟨1100867264234739681265243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93940673214697786134634069 1100867264234739681265243)
                    ·
                      rfl

theorem cell22_3215897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_3215897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215897 prefixEnd_3215897 := by exact prefixLift 3215897
  have htrace : WordTrace (prefixWord ++ tailWord_3215897) baseStart_3215897 baseEnd_3215897 := by
    simpa [prefixWord, tailWord_3215897, baseEnd_3215897] using wordTrace_append hprefix tailTrace_3215897
  have hstable : (prefixWord ++ tailWord_3215897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215897).length < 2 ^ (prefixWord ++ tailWord_3215897).sum := by decide
  have hdescent : baseEnd_3215897 < baseStart_3215897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215918 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_3215918 : Nat := 118140960795 + 3215918 * 2 ^ 59
def prefixEnd_3215918 : Nat := 4983230072969 + 3 ^ 40 * 3215918 * 2
def baseEnd_3215918 : Nat := 366958150987967542163393

theorem tailTrace_3215918 : CollatzResearch.WordTrace tailWord_3215918 prefixEnd_3215918 366958150987967542163393 := by
  unfold tailWord_3215918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661770695410724489084051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78196110375523863941781605 14661770695410724489084051)
  ·
    refine ⟨21992656043116086733626077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14661770695410724489084051 21992656043116086733626077)
    ·
      refine ⟨8247246016168532525109779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21992656043116086733626077 8247246016168532525109779)
      ·
        refine ⟨12370869024252798787664669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8247246016168532525109779 12370869024252798787664669)
        ·
          refine ⟨4639075884094799545374251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12370869024252798787664669 4639075884094799545374251)
          ·
            refine ⟨6958613826142199318061377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639075884094799545374251 6958613826142199318061377)
            ·
              refine ⟨5218960369606649488546033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6958613826142199318061377 5218960369606649488546033)
              ·
                refine ⟨3914220277204987116409525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5218960369606649488546033 3914220277204987116409525)
                ·
                  refine ⟨366958150987967542163393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3914220277204987116409525 366958150987967542163393)
                  ·
                    rfl

theorem cell22_3215918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_3215918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215918 prefixEnd_3215918 := by exact prefixLift 3215918
  have htrace : WordTrace (prefixWord ++ tailWord_3215918) baseStart_3215918 baseEnd_3215918 := by
    simpa [prefixWord, tailWord_3215918, baseEnd_3215918] using wordTrace_append hprefix tailTrace_3215918
  have hstable : (prefixWord ++ tailWord_3215918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215918).length < 2 ^ (prefixWord ++ tailWord_3215918).sum := by decide
  have hdescent : baseEnd_3215918 < baseStart_3215918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215929 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 6]
def baseStart_3215929 : Nat := 118140960795 + 3215929 * 2 ^ 59
def prefixEnd_3215929 : Nat := 4983230072969 + 3 ^ 40 * 3215929 * 2
def baseEnd_3215929 : Nat := 366959406162900754821715

theorem tailTrace_3215929 : CollatzResearch.WordTrace tailWord_3215929 prefixEnd_3215929 366959406162900754821715 := by
  unfold tailWord_3215929
  simp only [CollatzResearch.WordTrace]
  refine ⟨117294566766245944791322841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78196377844163963194215227 117294566766245944791322841)
  ·
    refine ⟨87970925074684458593492131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117294566766245944791322841 87970925074684458593492131)
    ·
      refine ⟨131956387612026687890238197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87970925074684458593492131 131956387612026687890238197)
      ·
        refine ⟨12370911338627501989709831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131956387612026687890238197 12370911338627501989709831)
        ·
          refine ⟨18556367007941252984564747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370911338627501989709831 18556367007941252984564747)
          ·
            refine ⟨27834550511911879476847121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18556367007941252984564747 27834550511911879476847121)
            ·
              refine ⟨20875912883933909607635341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27834550511911879476847121 20875912883933909607635341)
              ·
                refine ⟨7828467331475216102863253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20875912883933909607635341 7828467331475216102863253)
                ·
                  refine ⟨366959406162900754821715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7828467331475216102863253 366959406162900754821715)
                  ·
                    rfl

theorem cell22_3215929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_3215929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215929 prefixEnd_3215929 := by exact prefixLift 3215929
  have htrace : WordTrace (prefixWord ++ tailWord_3215929) baseStart_3215929 baseEnd_3215929 := by
    simpa [prefixWord, tailWord_3215929, baseEnd_3215929] using wordTrace_append hprefix tailTrace_3215929
  have hstable : (prefixWord ++ tailWord_3215929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215929).length < 2 ^ (prefixWord ++ tailWord_3215929).sum := by decide
  have hdescent : baseEnd_3215929 < baseStart_3215929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3215959 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 1, 6]
def baseStart_3215959 : Nat := 118140960795 + 3215959 * 2 ^ 59
def prefixEnd_3215959 : Nat := 4983230072969 + 3 ^ 40 * 3215959 * 2
def baseEnd_3215959 : Nat := 1100888488101792186215053

theorem tailTrace_3215959 : CollatzResearch.WordTrace tailWord_3215959 prefixEnd_3215959 1100888488101792186215053 := by
  unfold tailWord_3215959
  simp only [CollatzResearch.WordTrace]
  refine ⟨117295660956137259914914931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78197107304091506609943287 117295660956137259914914931)
  ·
    refine ⟨175943491434205889872372397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117295660956137259914914931 175943491434205889872372397)
    ·
      refine ⟨65978809287827208702139649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175943491434205889872372397 65978809287827208702139649)
      ·
        refine ⟨49484106965870406526604737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65978809287827208702139649 49484106965870406526604737)
        ·
          refine ⟨37113080224402804894953553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49484106965870406526604737 37113080224402804894953553)
          ·
            refine ⟨27834810168302103671215165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37113080224402804894953553 27834810168302103671215165)
            ·
              refine ⟨10438053813113288876705687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27834810168302103671215165 10438053813113288876705687)
              ·
                refine ⟨15657080719669933315058531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10438053813113288876705687 15657080719669933315058531)
                ·
                  refine ⟨23485621079504899972587797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15657080719669933315058531 23485621079504899972587797)
                  ·
                    refine ⟨1100888488101792186215053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23485621079504899972587797 1100888488101792186215053)
                    ·
                      rfl

theorem cell22_3215959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_3215959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3215959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3215959 prefixEnd_3215959 := by exact prefixLift 3215959
  have htrace : WordTrace (prefixWord ++ tailWord_3215959) baseStart_3215959 baseEnd_3215959 := by
    simpa [prefixWord, tailWord_3215959, baseEnd_3215959] using wordTrace_append hprefix tailTrace_3215959
  have hstable : (prefixWord ++ tailWord_3215959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3215959).length < 2 ^ (prefixWord ++ tailWord_3215959).sum := by decide
  have hdescent : baseEnd_3215959 < baseStart_3215959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3215959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216036 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 5]
def baseStart_3216036 : Nat := 118140960795 + 3216036 * 2 ^ 59
def prefixEnd_3216036 : Nat := 4983230072969 + 3 ^ 40 * 3216036 * 2
def baseEnd_3216036 : Nat := 366971615591796550679939

theorem tailTrace_3216036 : CollatzResearch.WordTrace tailWord_3216036 prefixEnd_3216036 366971615591796550679939 := by
  unfold tailWord_3216036
  simp only [CollatzResearch.WordTrace]
  refine ⟨58649234688429151032733981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78198979584572201376978641 58649234688429151032733981)
  ·
    refine ⟨21993463008160931637275243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58649234688429151032733981 21993463008160931637275243)
    ·
      refine ⟨32990194512241397455912865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21993463008160931637275243 32990194512241397455912865)
      ·
        refine ⟨24742645884181048091934649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32990194512241397455912865 24742645884181048091934649)
        ·
          refine ⟨18556984413135786068950987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24742645884181048091934649 18556984413135786068950987)
          ·
            refine ⟨27835476619703679103426481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18556984413135786068950987 27835476619703679103426481)
            ·
              refine ⟨20876607464777759327569861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27835476619703679103426481 20876607464777759327569861)
              ·
                refine ⟨3914363899645829873919349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20876607464777759327569861 3914363899645829873919349)
                ·
                  refine ⟨366971615591796550679939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3914363899645829873919349 366971615591796550679939)
                  ·
                    rfl

theorem cell22_3216036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_3216036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216036 prefixEnd_3216036 := by exact prefixLift 3216036
  have htrace : WordTrace (prefixWord ++ tailWord_3216036) baseStart_3216036 baseEnd_3216036 := by
    simpa [prefixWord, tailWord_3216036, baseEnd_3216036] using wordTrace_append hprefix tailTrace_3216036
  have hstable : (prefixWord ++ tailWord_3216036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216036).length < 2 ^ (prefixWord ++ tailWord_3216036).sum := by decide
  have hdescent : baseEnd_3216036 < baseStart_3216036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216053 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 5]
def baseStart_3216053 : Nat := 118140960795 + 3216053 * 2 ^ 59
def prefixEnd_3216053 : Nat := 4983230072969 + 3 ^ 40 * 3216053 * 2
def baseEnd_3216053 : Nat := 366973555407602424788255

theorem tailTrace_3216053 : CollatzResearch.WordTrace tailWord_3216053 prefixEnd_3216053 366973555407602424788255 := by
  unfold tailWord_3216053
  simp only [CollatzResearch.WordTrace]
  refine ⟨117299089417796713968836813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78199392945197809312557875 117299089417796713968836813)
  ·
    refine ⟨43987158531673767738313805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117299089417796713968836813 43987158531673767738313805)
    ·
      refine ⟨16495184449377662901867677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43987158531673767738313805 16495184449377662901867677)
      ·
        refine ⟨6185694168516623588200379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16495184449377662901867677 6185694168516623588200379)
        ·
          refine ⟨9278541252774935382300569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6185694168516623588200379 9278541252774935382300569)
          ·
            refine ⟨6958905939581201536725427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9278541252774935382300569 6958905939581201536725427)
            ·
              refine ⟨10438358909371802305088141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6958905939581201536725427 10438358909371802305088141)
              ·
                refine ⟨3914384591014425864408053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10438358909371802305088141 3914384591014425864408053)
                ·
                  refine ⟨366973555407602424788255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3914384591014425864408053 366973555407602424788255)
                  ·
                    rfl

theorem cell22_3216053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_3216053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216053 prefixEnd_3216053 := by exact prefixLift 3216053
  have htrace : WordTrace (prefixWord ++ tailWord_3216053) baseStart_3216053 baseEnd_3216053 := by
    simpa [prefixWord, tailWord_3216053, baseEnd_3216053] using wordTrace_append hprefix tailTrace_3216053
  have hstable : (prefixWord ++ tailWord_3216053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216053).length < 2 ^ (prefixWord ++ tailWord_3216053).sum := by decide
  have hdescent : baseEnd_3216053 < baseStart_3216053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216113 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 2, 3]
def baseStart_3216113 : Nat := 118140960795 + 3216113 * 2 ^ 59
def prefixEnd_3216113 : Nat := 4983230072969 + 3 ^ 40 * 3216113 * 2
def baseEnd_3216113 : Nat := 1100941205448987117864581

theorem tailTrace_3216113 : CollatzResearch.WordTrace tailWord_3216113 prefixEnd_3216113 1100941205448987117864581 := by
  unfold tailWord_3216113
  simp only [CollatzResearch.WordTrace]
  refine ⟨117301277797579344216020993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78200851865052896144013995 117301277797579344216020993)
  ·
    refine ⟨87975958348184508162015745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117301277797579344216020993 87975958348184508162015745)
    ·
      refine ⟨65981968761138381121511809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87975958348184508162015745 65981968761138381121511809)
      ·
        refine ⟨49486476570853785841133857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65981968761138381121511809 49486476570853785841133857)
        ·
          refine ⟨37114857428140339380850393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49486476570853785841133857 37114857428140339380850393)
          ·
            refine ⟨27836143071105254535637795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37114857428140339380850393 27836143071105254535637795)
            ·
              refine ⟨41754214606657881803456693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27836143071105254535637795 41754214606657881803456693)
              ·
                refine ⟨3914457619374176419074065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41754214606657881803456693 3914457619374176419074065)
                ·
                  refine ⟨2935843214530632314305549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3914457619374176419074065 2935843214530632314305549)
                  ·
                    refine ⟨1100941205448987117864581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2935843214530632314305549 1100941205448987117864581)
                    ·
                      rfl

theorem cell22_3216113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_3216113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216113 prefixEnd_3216113 := by exact prefixLift 3216113
  have htrace : WordTrace (prefixWord ++ tailWord_3216113) baseStart_3216113 baseEnd_3216113 := by
    simpa [prefixWord, tailWord_3216113, baseEnd_3216113] using wordTrace_append hprefix tailTrace_3216113
  have hstable : (prefixWord ++ tailWord_3216113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216113).length < 2 ^ (prefixWord ++ tailWord_3216113).sum := by decide
  have hdescent : baseEnd_3216113 < baseStart_3216113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216209 : List Nat := [1, 2, 2, 1, 6, 1, 3, 2, 1, 3]
def baseStart_3216209 : Nat := 118140960795 + 3216209 * 2 ^ 59
def prefixEnd_3216209 : Nat := 4983230072969 + 3 ^ 40 * 3216209 * 2
def baseEnd_3216209 : Nat := 1100974068210874867464287

theorem tailTrace_3216209 : CollatzResearch.WordTrace tailWord_3216209 prefixEnd_3216209 1100974068210874867464287 := by
  unfold tailWord_3216209
  simp only [CollatzResearch.WordTrace]
  refine ⟨117304779205231552611515681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78203186136821035074343787 117304779205231552611515681)
  ·
    refine ⟨87978584403923664458636761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117304779205231552611515681 87978584403923664458636761)
    ·
      refine ⟨65983938302942748343977571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87978584403923664458636761 65983938302942748343977571)
      ·
        refine ⟨98975907454414122515966357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65983938302942748343977571 98975907454414122515966357)
        ·
          refine ⟨4639495661925661992935923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98975907454414122515966357 4639495661925661992935923)
          ·
            refine ⟨6959243492888492989403885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639495661925661992935923 6959243492888492989403885)
            ·
              refine ⟨2609716309833184871026457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6959243492888492989403885 2609716309833184871026457)
              ·
                refine ⟨1957287232374888653269843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609716309833184871026457 1957287232374888653269843)
                ·
                  refine ⟨2935930848562332979904765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957287232374888653269843 2935930848562332979904765)
                  ·
                    refine ⟨1100974068210874867464287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2935930848562332979904765 1100974068210874867464287)
                    ·
                      rfl

theorem cell22_3216209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_3216209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216209 prefixEnd_3216209 := by exact prefixLift 3216209
  have htrace : WordTrace (prefixWord ++ tailWord_3216209) baseStart_3216209 baseEnd_3216209 := by
    simpa [prefixWord, tailWord_3216209, baseEnd_3216209] using wordTrace_append hprefix tailTrace_3216209
  have hstable : (prefixWord ++ tailWord_3216209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216209).length < 2 ^ (prefixWord ++ tailWord_3216209).sum := by decide
  have hdescent : baseEnd_3216209 < baseStart_3216209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216248 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 4, 3]
def baseStart_3216248 : Nat := 118140960795 + 3216248 * 2 ^ 59
def prefixEnd_3216248 : Nat := 4983230072969 + 3 ^ 40 * 3216248 * 2
def baseEnd_3216248 : Nat := 1100987418707891765739167

theorem tailTrace_3216248 : CollatzResearch.WordTrace tailWord_3216248 prefixEnd_3216248 1100987418707891765739167 := by
  unfold tailWord_3216248
  simp only [CollatzResearch.WordTrace]
  refine ⟨58653100826045131136092699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78204134434726841514790265 58653100826045131136092699)
  ·
    refine ⟨87979651239067696704139049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58653100826045131136092699 87979651239067696704139049)
    ·
      refine ⟨65984738429300772528104287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87979651239067696704139049 65984738429300772528104287)
      ·
        refine ⟨98977107643951158792156431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65984738429300772528104287 98977107643951158792156431)
        ·
          refine ⟨148465661465926738188234647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98977107643951158792156431 148465661465926738188234647)
          ·
            refine ⟨222698492198890107282351971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148465661465926738188234647 222698492198890107282351971)
            ·
              refine ⟨334047738298335160923527957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222698492198890107282351971 334047738298335160923527957)
              ·
                refine ⟨15658487732734460668290373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 334047738298335160923527957 15658487732734460668290373)
                ·
                  refine ⟨2935966449887711375304445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15658487732734460668290373 2935966449887711375304445)
                  ·
                    refine ⟨1100987418707891765739167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2935966449887711375304445 1100987418707891765739167)
                    ·
                      rfl

theorem cell22_3216248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_3216248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216248 prefixEnd_3216248 := by exact prefixLift 3216248
  have htrace : WordTrace (prefixWord ++ tailWord_3216248) baseStart_3216248 baseEnd_3216248 := by
    simpa [prefixWord, tailWord_3216248, baseEnd_3216248] using wordTrace_append hprefix tailTrace_3216248
  have hstable : (prefixWord ++ tailWord_3216248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216248).length < 2 ^ (prefixWord ++ tailWord_3216248).sum := by decide
  have hdescent : baseEnd_3216248 < baseStart_3216248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216261 : List Nat := [1, 3, 1, 1, 3, 13]
def baseStart_3216261 : Nat := 118140960795 + 3216261 * 2 ^ 59
def prefixEnd_3216261 : Nat := 4983230072969 + 3 ^ 40 * 3216261 * 2
def baseEnd_3216261 : Nat := 13592492208315605742767

theorem tailTrace_3216261 : CollatzResearch.WordTrace tailWord_3216261 prefixEnd_3216261 13592492208315605742767 := by
  unfold tailWord_3216261
  simp only [CollatzResearch.WordTrace]
  refine ⟨117306675801043165492408637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78204450534028776994939091 117306675801043165492408637)
  ·
    refine ⟨43990003425391187059653239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117306675801043165492408637 43990003425391187059653239)
    ·
      refine ⟨65985005138086780589479859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43990003425391187059653239 65985005138086780589479859)
      ·
        refine ⟨98977507707130170884219789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65985005138086780589479859 98977507707130170884219789)
        ·
          refine ⟨37116565390173814081582421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98977507707130170884219789 37116565390173814081582421)
          ·
            refine ⟨13592492208315605742767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 37116565390173814081582421 13592492208315605742767)
            ·
              rfl

theorem cell22_3216261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 13].length) (baseStart_3216261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216261 prefixEnd_3216261 := by exact prefixLift 3216261
  have htrace : WordTrace (prefixWord ++ tailWord_3216261) baseStart_3216261 baseEnd_3216261 := by
    simpa [prefixWord, tailWord_3216261, baseEnd_3216261] using wordTrace_append hprefix tailTrace_3216261
  have hstable : (prefixWord ++ tailWord_3216261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216261).length < 2 ^ (prefixWord ++ tailWord_3216261).sum := by decide
  have hdescent : baseEnd_3216261 < baseStart_3216261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216265 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 2, 3]
def baseStart_3216265 : Nat := 118140960795 + 3216265 * 2 ^ 59
def prefixEnd_3216265 : Nat := 4983230072969 + 3 ^ 40 * 3216265 * 2
def baseEnd_3216265 : Nat := 1100993238155309388064115

theorem tailTrace_3216265 : CollatzResearch.WordTrace tailWord_3216265 prefixEnd_3216265 1100993238155309388064115 := by
  unfold tailWord_3216265
  simp only [CollatzResearch.WordTrace]
  refine ⟨117306821693028674175554249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78204547795352449450369499 117306821693028674175554249)
  ·
    refine ⟨87980116269771505631665687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117306821693028674175554249 87980116269771505631665687)
    ·
      refine ⟨131970174404657258447498531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87980116269771505631665687 131970174404657258447498531)
      ·
        refine ⟨197955261606985887671247797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131970174404657258447498531 197955261606985887671247797)
        ·
          refine ⟨18558305775654926969179481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197955261606985887671247797 18558305775654926969179481)
          ·
            refine ⟨13918729331741195226884611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18558305775654926969179481 13918729331741195226884611)
            ·
              refine ⟨20878093997611792840326917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13918729331741195226884611 20878093997611792840326917)
              ·
                refine ⟨3914642624552211157561297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20878093997611792840326917 3914642624552211157561297)
                ·
                  refine ⟨2935981968414158368170973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3914642624552211157561297 2935981968414158368170973)
                  ·
                    refine ⟨1100993238155309388064115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2935981968414158368170973 1100993238155309388064115)
                    ·
                      rfl

theorem cell22_3216265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_3216265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216265 prefixEnd_3216265 := by exact prefixLift 3216265
  have htrace : WordTrace (prefixWord ++ tailWord_3216265) baseStart_3216265 baseEnd_3216265 := by
    simpa [prefixWord, tailWord_3216265, baseEnd_3216265] using wordTrace_append hprefix tailTrace_3216265
  have hstable : (prefixWord ++ tailWord_3216265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216265).length < 2 ^ (prefixWord ++ tailWord_3216265).sum := by decide
  have hdescent : baseEnd_3216265 < baseStart_3216265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216327 : List Nat := [1, 1, 4, 1, 1, 2, 4, 4, 1, 3]
def baseStart_3216327 : Nat := 118140960795 + 3216327 * 2 ^ 59
def prefixEnd_3216327 : Nat := 4983230072969 + 3 ^ 40 * 3216327 * 2
def baseEnd_3216327 : Nat := 1101014462022361893013925

theorem tailTrace_3216327 : CollatzResearch.WordTrace tailWord_3216327 prefixEnd_3216327 1101014462022361893013925 := by
  unfold tailWord_3216327
  simp only [CollatzResearch.WordTrace]
  refine ⟨117309083018804058764311235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78206055345869372509540823 117309083018804058764311235)
  ·
    refine ⟨175963624528206088146466853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117309083018804058764311235 175963624528206088146466853)
    ·
      refine ⟨32993179599038641527462535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175963624528206088146466853 32993179599038641527462535)
      ·
        refine ⟨49489769398557962291193803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32993179599038641527462535 49489769398557962291193803)
        ·
          refine ⟨74234654097836943436790705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49489769398557962291193803 74234654097836943436790705)
          ·
            refine ⟨55675990573377707577593029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74234654097836943436790705 55675990573377707577593029)
            ·
              refine ⟨10439248232508320170798693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55675990573377707577593029 10439248232508320170798693)
              ·
                refine ⟨1957359043595310032024755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10439248232508320170798693 1957359043595310032024755)
                ·
                  refine ⟨2936038565392965048037133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957359043595310032024755 2936038565392965048037133)
                  ·
                    refine ⟨1101014462022361893013925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936038565392965048037133 1101014462022361893013925)
                    ·
                      rfl

theorem cell22_3216327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_3216327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216327 prefixEnd_3216327 := by exact prefixLift 3216327
  have htrace : WordTrace (prefixWord ++ tailWord_3216327) baseStart_3216327 baseEnd_3216327 := by
    simpa [prefixWord, tailWord_3216327, baseEnd_3216327] using wordTrace_append hprefix tailTrace_3216327
  have hstable : (prefixWord ++ tailWord_3216327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216327).length < 2 ^ (prefixWord ++ tailWord_3216327).sum := by decide
  have hdescent : baseEnd_3216327 < baseStart_3216327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216333 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3216333 : Nat := 118140960795 + 3216333 * 2 ^ 59
def prefixEnd_3216333 : Nat := 4983230072969 + 3 ^ 40 * 3216333 * 2
def baseEnd_3216333 : Nat := 1101016515944979877363907

theorem tailTrace_3216333 : CollatzResearch.WordTrace tailWord_3216333 prefixEnd_3216333 1101016515944979877363907 := by
  unfold tailWord_3216333
  simp only [CollatzResearch.WordTrace]
  refine ⟨117309301856782321789029653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78206201237854881192686435 117309301856782321789029653)
  ·
    refine ⟨5498873524536671333860765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 117309301856782321789029653 5498873524536671333860765)
    ·
      refine ⟨2062077571701251750197787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5498873524536671333860765 2062077571701251750197787)
      ·
        refine ⟨3093116357551877625296681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062077571701251750197787 3093116357551877625296681)
        ·
          refine ⟨2319837268163908218972511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3093116357551877625296681 2319837268163908218972511)
          ·
            refine ⟨3479755902245862328458767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319837268163908218972511 3479755902245862328458767)
            ·
              refine ⟨5219633853368793492688151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479755902245862328458767 5219633853368793492688151)
              ·
                refine ⟨7829450780053190239032227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219633853368793492688151 7829450780053190239032227)
                ·
                  refine ⟨11744176170079785358548341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7829450780053190239032227 11744176170079785358548341)
                  ·
                    refine ⟨1101016515944979877363907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11744176170079785358548341 1101016515944979877363907)
                    ·
                      rfl

theorem cell22_3216333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3216333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216333 prefixEnd_3216333 := by exact prefixLift 3216333
  have htrace : WordTrace (prefixWord ++ tailWord_3216333) baseStart_3216333 baseEnd_3216333 := by
    simpa [prefixWord, tailWord_3216333, baseEnd_3216333] using wordTrace_append hprefix tailTrace_3216333
  have hstable : (prefixWord ++ tailWord_3216333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216333).length < 2 ^ (prefixWord ++ tailWord_3216333).sum := by decide
  have hdescent : baseEnd_3216333 < baseStart_3216333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216385 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 6]
def baseStart_3216385 : Nat := 118140960795 + 3216385 * 2 ^ 59
def prefixEnd_3216385 : Nat := 4983230072969 + 3 ^ 40 * 3216385 * 2
def baseEnd_3216385 : Nat := 367011438869223025021249

theorem tailTrace_3216385 : CollatzResearch.WordTrace tailWord_3216385 prefixEnd_3216385 367011438869223025021249 := by
  unfold tailWord_3216385
  simp only [CollatzResearch.WordTrace]
  refine ⟨117311198452593934669922609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78207465635062623113281739 117311198452593934669922609)
  ·
    refine ⟨87983398839445451002441957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117311198452593934669922609 87983398839445451002441957)
    ·
      refine ⟨16496887282396022062957867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87983398839445451002441957 16496887282396022062957867)
      ·
        refine ⟨24745330923594033094436801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16496887282396022062957867 24745330923594033094436801)
        ·
          refine ⟨18558998192695524820827601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24745330923594033094436801 18558998192695524820827601)
          ·
            refine ⟨13919248644521643615620701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18558998192695524820827601 13919248644521643615620701)
            ·
              refine ⟨5219718241695616355857763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13919248644521643615620701 5219718241695616355857763)
              ·
                refine ⟨7829577362543424533786645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219718241695616355857763 7829577362543424533786645)
                ·
                  refine ⟨367011438869223025021249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7829577362543424533786645 367011438869223025021249)
                  ·
                    rfl

theorem cell22_3216385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_3216385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216385 prefixEnd_3216385 := by exact prefixLift 3216385
  have htrace : WordTrace (prefixWord ++ tailWord_3216385) baseStart_3216385 baseEnd_3216385 := by
    simpa [prefixWord, tailWord_3216385, baseEnd_3216385] using wordTrace_append hprefix tailTrace_3216385
  have hstable : (prefixWord ++ tailWord_3216385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216385).length < 2 ^ (prefixWord ++ tailWord_3216385).sum := by decide
  have hdescent : baseEnd_3216385 < baseStart_3216385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216415 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 2, 4]
def baseStart_3216415 : Nat := 118140960795 + 3216415 * 2 ^ 59
def prefixEnd_3216415 : Nat := 4983230072969 + 3 ^ 40 * 3216415 * 2
def baseEnd_3216415 : Nat := 1101044586220758996813655

theorem tailTrace_3216415 : CollatzResearch.WordTrace tailWord_3216415 prefixEnd_3216415 1101044586220758996813655 := by
  unfold tailWord_3216415
  simp only [CollatzResearch.WordTrace]
  refine ⟨117312292642485249793514699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78208195094990166529009799 117312292642485249793514699)
  ·
    refine ⟨175968438963727874690272049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117312292642485249793514699 175968438963727874690272049)
    ·
      refine ⟨131976329222795906017704037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175968438963727874690272049 131976329222795906017704037)
      ·
        refine ⟨24745561729274232378319507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131976329222795906017704037 24745561729274232378319507)
        ·
          refine ⟨37118342593911348567479261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24745561729274232378319507 37118342593911348567479261)
          ·
            refine ⟨13919378472716755712804723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37118342593911348567479261 13919378472716755712804723)
            ·
              refine ⟨20879067709075133569207085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919378472716755712804723 20879067709075133569207085)
              ·
                refine ⟨7829650390903175088452657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20879067709075133569207085 7829650390903175088452657)
                ·
                  refine ⟨5872237793177381316339493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7829650390903175088452657 5872237793177381316339493)
                  ·
                    refine ⟨1101044586220758996813655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5872237793177381316339493 1101044586220758996813655)
                    ·
                      rfl

theorem cell22_3216415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_3216415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216415 prefixEnd_3216415 := by exact prefixLift 3216415
  have htrace : WordTrace (prefixWord ++ tailWord_3216415) baseStart_3216415 baseEnd_3216415 := by
    simpa [prefixWord, tailWord_3216415, baseEnd_3216415] using wordTrace_append hprefix tailTrace_3216415
  have hstable : (prefixWord ++ tailWord_3216415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216415).length < 2 ^ (prefixWord ++ tailWord_3216415).sum := by decide
  have hdescent : baseEnd_3216415 < baseStart_3216415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216436 : List Nat := [2, 5, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3216436 : Nat := 118140960795 + 3216436 * 2 ^ 59
def prefixEnd_3216436 : Nat := 4983230072969 + 3 ^ 40 * 3216436 * 2
def baseEnd_3216436 : Nat := 367017258316640647346197

theorem tailTrace_3216436 : CollatzResearch.WordTrace tailWord_3216436 prefixEnd_3216436 367017258316640647346197 := by
  unfold tailWord_3216436
  simp only [CollatzResearch.WordTrace]
  refine ⟨58656529287704585190014581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78208705716939446920019441 58656529287704585190014581)
  ·
    refine ⟨5499049620722304861563867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58656529287704585190014581 5499049620722304861563867)
    ·
      refine ⟨8248574431083457292345801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499049620722304861563867 8248574431083457292345801)
      ·
        refine ⟨6186430823312592969259351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8248574431083457292345801 6186430823312592969259351)
        ·
          refine ⟨9279646234968889453889027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186430823312592969259351 9279646234968889453889027)
          ·
            refine ⟨13919469352453334180833541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279646234968889453889027 13919469352453334180833541)
            ·
              refine ⟨2609900503585000158906289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13919469352453334180833541 2609900503585000158906289)
              ·
                refine ⟨1957425377688750119179717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609900503585000158906289 1957425377688750119179717)
                ·
                  refine ⟨367017258316640647346197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957425377688750119179717 367017258316640647346197)
                  ·
                    rfl

theorem cell22_3216436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3216436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216436 prefixEnd_3216436 := by exact prefixLift 3216436
  have htrace : WordTrace (prefixWord ++ tailWord_3216436) baseStart_3216436 baseEnd_3216436 := by
    simpa [prefixWord, tailWord_3216436, baseEnd_3216436] using wordTrace_append hprefix tailTrace_3216436
  have hstable : (prefixWord ++ tailWord_3216436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216436).length < 2 ^ (prefixWord ++ tailWord_3216436).sum := by decide
  have hdescent : baseEnd_3216436 < baseStart_3216436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216462 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_3216462 : Nat := 118140960795 + 3216462 * 2 ^ 59
def prefixEnd_3216462 : Nat := 4983230072969 + 3 ^ 40 * 3216462 * 2
def baseEnd_3216462 : Nat := 1101060675281266540888511

theorem tailTrace_3216462 : CollatzResearch.WordTrace tailWord_3216462 prefixEnd_3216462 1101060675281266540888511 := by
  unfold tailWord_3216462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14664250859164372102559455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78209337915543317880317093 14664250859164372102559455)
  ·
    refine ⟨21996376288746558153839183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14664250859164372102559455 21996376288746558153839183)
    ·
      refine ⟨32994564433119837230758775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21996376288746558153839183 32994564433119837230758775)
      ·
        refine ⟨49491846649679755846138163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32994564433119837230758775 49491846649679755846138163)
        ·
          refine ⟨74237769974519633769207245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49491846649679755846138163 74237769974519633769207245)
          ·
            refine ⟨27839163740444862663452717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74237769974519633769207245 27839163740444862663452717)
            ·
              refine ⟨10439686402666823498794769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27839163740444862663452717 10439686402666823498794769)
              ·
                refine ⟨7829764802000117624096077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10439686402666823498794769 7829764802000117624096077)
                ·
                  refine ⟨2936161800750044109036029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7829764802000117624096077 2936161800750044109036029)
                  ·
                    refine ⟨1101060675281266540888511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936161800750044109036029 1101060675281266540888511)
                    ·
                      rfl

theorem cell22_3216462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_3216462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216462 prefixEnd_3216462 := by exact prefixLift 3216462
  have htrace : WordTrace (prefixWord ++ tailWord_3216462) baseStart_3216462 baseEnd_3216462 := by
    simpa [prefixWord, tailWord_3216462, baseEnd_3216462] using wordTrace_append hprefix tailTrace_3216462
  have hstable : (prefixWord ++ tailWord_3216462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216462).length < 2 ^ (prefixWord ++ tailWord_3216462).sum := by decide
  have hdescent : baseEnd_3216462 < baseStart_3216462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216479 : List Nat := [1, 1, 2, 3, 1, 1, 6, 3, 1, 3]
def baseStart_3216479 : Nat := 118140960795 + 3216479 * 2 ^ 59
def prefixEnd_3216479 : Nat := 4983230072969 + 3 ^ 40 * 3216479 * 2
def baseEnd_3216479 : Nat := 1101066494728684163213459

theorem tailTrace_3216479 : CollatzResearch.WordTrace tailWord_3216479 prefixEnd_3216479 1101066494728684163213459 := by
  unfold tailWord_3216479
  simp only [CollatzResearch.WordTrace]
  refine ⟨117314626914253388723844491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78209751276168925815896327 117314626914253388723844491)
  ·
    refine ⟨175971940371380083085766737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117314626914253388723844491 175971940371380083085766737)
    ·
      refine ⟨131978955278535062314325053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175971940371380083085766737 131978955278535062314325053)
      ·
        refine ⟨49492108229450648367871895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131978955278535062314325053 49492108229450648367871895)
        ·
          refine ⟨74238162344175972551807843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49492108229450648367871895 74238162344175972551807843)
          ·
            refine ⟨111357243516263958827711765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74238162344175972551807843 111357243516263958827711765)
            ·
              refine ⟨5219870789824873070048989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111357243516263958827711765 5219870789824873070048989)
              ·
                refine ⟨1957451546184327401268371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5219870789824873070048989 1957451546184327401268371)
                ·
                  refine ⟨2936177319276491101902557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957451546184327401268371 2936177319276491101902557)
                  ·
                    refine ⟨1101066494728684163213459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936177319276491101902557 1101066494728684163213459)
                    ·
                      rfl

theorem cell22_3216479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 1, 3].length) (baseStart_3216479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216479 prefixEnd_3216479 := by exact prefixLift 3216479
  have htrace : WordTrace (prefixWord ++ tailWord_3216479) baseStart_3216479 baseEnd_3216479 := by
    simpa [prefixWord, tailWord_3216479, baseEnd_3216479] using wordTrace_append hprefix tailTrace_3216479
  have hstable : (prefixWord ++ tailWord_3216479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216479).length < 2 ^ (prefixWord ++ tailWord_3216479).sum := by decide
  have hdescent : baseEnd_3216479 < baseStart_3216479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216554 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_3216554 : Nat := 118140960795 + 3216554 * 2 ^ 59
def prefixEnd_3216554 : Nat := 4983230072969 + 3 ^ 40 * 3216554 * 2
def baseEnd_3216554 : Nat := 367030722920469655862743

theorem tailTrace_3216554 : CollatzResearch.WordTrace tailWord_3216554 prefixEnd_3216554 367030722920469655862743 := by
  unfold tailWord_3216554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29329340597245419133206179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78211574925987784355216477 29329340597245419133206179)
  ·
    refine ⟨43994010895868128699809269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29329340597245419133206179 43994010895868128699809269)
    ·
      refine ⟨4124438521487637065607119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43994010895868128699809269 4124438521487637065607119)
      ·
        refine ⟨6186657782231455598410679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124438521487637065607119 6186657782231455598410679)
        ·
          refine ⟨9279986673347183397616019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186657782231455598410679 9279986673347183397616019)
          ·
            refine ⟨13919980010020775096424029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279986673347183397616019 13919980010020775096424029)
            ·
              refine ⟨5219992503757790661159011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13919980010020775096424029 5219992503757790661159011)
              ·
                refine ⟨7829988755636685991738517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219992503757790661159011 7829988755636685991738517)
                ·
                  refine ⟨367030722920469655862743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7829988755636685991738517 367030722920469655862743)
                  ·
                    rfl

theorem cell22_3216554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_3216554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216554 prefixEnd_3216554 := by exact prefixLift 3216554
  have htrace : WordTrace (prefixWord ++ tailWord_3216554) baseStart_3216554 baseEnd_3216554 := by
    simpa [prefixWord, tailWord_3216554, baseEnd_3216554] using wordTrace_append hprefix tailTrace_3216554
  have hstable : (prefixWord ++ tailWord_3216554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216554).length < 2 ^ (prefixWord ++ tailWord_3216554).sum := by decide
  have hdescent : baseEnd_3216554 < baseStart_3216554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216569 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 2, 3]
def baseStart_3216569 : Nat := 118140960795 + 3216569 * 2 ^ 59
def prefixEnd_3216569 : Nat := 4983230072969 + 3 ^ 40 * 3216569 * 2
def baseEnd_3216569 : Nat := 1101097303567953928463183

theorem tailTrace_3216569 : CollatzResearch.WordTrace tailWord_3216569 prefixEnd_3216569 1101097303567953928463183 := by
  unfold tailWord_3216569
  simp only [CollatzResearch.WordTrace]
  refine ⟨117317909483927334094620761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78211939655951556063080507 117317909483927334094620761)
  ·
    refine ⟨87988432112945500570965571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117317909483927334094620761 87988432112945500570965571)
    ·
      refine ⟨131982648169418250856448357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87988432112945500570965571 131982648169418250856448357)
      ·
        refine ⟨24746746531765922035584067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131982648169418250856448357 24746746531765922035584067)
        ·
          refine ⟨37120119797648883053376101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24746746531765922035584067 37120119797648883053376101)
          ·
            refine ⟨6960022462059165572508019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37120119797648883053376101 6960022462059165572508019)
            ·
              refine ⟨10440033693088748358762029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6960022462059165572508019 10440033693088748358762029)
              ·
                refine ⟨3915012634908280634535761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10440033693088748358762029 3915012634908280634535761)
                ·
                  refine ⟨2936259476181210475901821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3915012634908280634535761 2936259476181210475901821)
                  ·
                    refine ⟨1101097303567953928463183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936259476181210475901821 1101097303567953928463183)
                    ·
                      rfl

theorem cell22_3216569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_3216569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216569 prefixEnd_3216569 := by exact prefixLift 3216569
  have htrace : WordTrace (prefixWord ++ tailWord_3216569) baseStart_3216569 baseEnd_3216569 := by
    simpa [prefixWord, tailWord_3216569, baseEnd_3216569] using wordTrace_append hprefix tailTrace_3216569
  have hstable : (prefixWord ++ tailWord_3216569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216569).length < 2 ^ (prefixWord ++ tailWord_3216569).sum := by decide
  have hdescent : baseEnd_3216569 < baseStart_3216569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216605 : List Nat := [1, 4, 3, 2, 3, 1, 2, 2, 4]
def baseStart_3216605 : Nat := 118140960795 + 3216605 * 2 ^ 59
def prefixEnd_3216605 : Nat := 4983230072969 + 3 ^ 40 * 3216605 * 2
def baseEnd_3216605 : Nat := 367036542367887278187691

theorem tailTrace_3216605 : CollatzResearch.WordTrace tailWord_3216605 prefixEnd_3216605 367036542367887278187691 := by
  unfold tailWord_3216605
  simp only [CollatzResearch.WordTrace]
  refine ⟨117319222511796912242931269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78212815007864608161954179 117319222511796912242931269)
  ·
    refine ⟨21997354220961921045549613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117319222511796912242931269 21997354220961921045549613)
    ·
      refine ⟨8249007832860720392081105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21997354220961921045549613 8249007832860720392081105)
      ·
        refine ⟨6186755874645540294060829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8249007832860720392081105 6186755874645540294060829)
        ·
          refine ⟨2320033452992077610272811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6186755874645540294060829 2320033452992077610272811)
          ·
            refine ⟨3480050179488116415409217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320033452992077610272811 3480050179488116415409217)
            ·
              refine ⟨2610037634616087311556913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480050179488116415409217 2610037634616087311556913)
              ·
                refine ⟨1957528225962065483667685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2610037634616087311556913 1957528225962065483667685)
                ·
                  refine ⟨367036542367887278187691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957528225962065483667685 367036542367887278187691)
                  ·
                    rfl

theorem cell22_3216605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_3216605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216605 prefixEnd_3216605 := by exact prefixLift 3216605
  have htrace : WordTrace (prefixWord ++ tailWord_3216605) baseStart_3216605 baseEnd_3216605 := by
    simpa [prefixWord, tailWord_3216605, baseEnd_3216605] using wordTrace_append hprefix tailTrace_3216605
  have hstable : (prefixWord ++ tailWord_3216605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216605).length < 2 ^ (prefixWord ++ tailWord_3216605).sum := by decide
  have hdescent : baseEnd_3216605 < baseStart_3216605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216627 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 5]
def baseStart_3216627 : Nat := 118140960795 + 3216627 * 2 ^ 59
def prefixEnd_3216627 : Nat := 4983230072969 + 3 ^ 40 * 3216627 * 2
def baseEnd_3216627 : Nat := 367039052717753703504335

theorem tailTrace_3216627 : CollatzResearch.WordTrace tailWord_3216627 prefixEnd_3216627 367039052717753703504335 := by
  unfold tailWord_3216627
  simp only [CollatzResearch.WordTrace]
  refine ⟨117320024917717210000232135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78213349945144806666821423 117320024917717210000232135)
  ·
    refine ⟨175980037376575815000348203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117320024917717210000232135 175980037376575815000348203)
    ·
      refine ⟨263970056064863722500522305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175980037376575815000348203 263970056064863722500522305)
      ·
        refine ⟨197977542048647791875391729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263970056064863722500522305 197977542048647791875391729)
        ·
          refine ⟨148483156536485843906543797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197977542048647791875391729 148483156536485843906543797)
          ·
            refine ⟨13920295925295547866238481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148483156536485843906543797 13920295925295547866238481)
            ·
              refine ⟨10440221943971660899678861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13920295925295547866238481 10440221943971660899678861)
              ·
                refine ⟨3915083228989372837379573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10440221943971660899678861 3915083228989372837379573)
                ·
                  refine ⟨367039052717753703504335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3915083228989372837379573 367039052717753703504335)
                  ·
                    rfl

theorem cell22_3216627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 5].length) (baseStart_3216627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216627 prefixEnd_3216627 := by exact prefixLift 3216627
  have htrace : WordTrace (prefixWord ++ tailWord_3216627) baseStart_3216627 baseEnd_3216627 := by
    simpa [prefixWord, tailWord_3216627, baseEnd_3216627] using wordTrace_append hprefix tailTrace_3216627
  have hstable : (prefixWord ++ tailWord_3216627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216627).length < 2 ^ (prefixWord ++ tailWord_3216627).sum := by decide
  have hdescent : baseEnd_3216627 < baseStart_3216627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216648 : List Nat := [2, 1, 3, 2, 4, 1, 2, 3, 1, 3]
def baseStart_3216648 : Nat := 118140960795 + 3216648 * 2 ^ 59
def prefixEnd_3216648 : Nat := 4983230072969 + 3 ^ 40 * 3216648 * 2
def baseEnd_3216648 : Nat := 1101124346882424055737941

theorem tailTrace_3216648 : CollatzResearch.WordTrace tailWord_3216648 prefixEnd_3216648 1101124346882424055737941 := by
  unfold tailWord_3216648
  simp only [CollatzResearch.WordTrace]
  refine ⟨58660395425320565293373299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78213860567094087057831065 58660395425320565293373299)
  ·
    refine ⟨87990593137980847940059949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58660395425320565293373299 87990593137980847940059949)
    ·
      refine ⟨32996472426742817977522481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87990593137980847940059949 32996472426742817977522481)
      ·
        refine ⟨24747354320057113483141861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32996472426742817977522481 24747354320057113483141861)
        ·
          refine ⟨4640128935010708778089099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24747354320057113483141861 4640128935010708778089099)
          ·
            refine ⟨6960193402516063167133649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640128935010708778089099 6960193402516063167133649)
            ·
              refine ⟨5220145051887047375350237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6960193402516063167133649 5220145051887047375350237)
              ·
                refine ⟨1957554394457642765756339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5220145051887047375350237 1957554394457642765756339)
                ·
                  refine ⟨2936331591686464148634509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957554394457642765756339 2936331591686464148634509)
                  ·
                    refine ⟨1101124346882424055737941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936331591686464148634509 1101124346882424055737941)
                    ·
                      rfl

theorem cell22_3216648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_3216648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216648 prefixEnd_3216648 := by exact prefixLift 3216648
  have htrace : WordTrace (prefixWord ++ tailWord_3216648) baseStart_3216648 baseEnd_3216648 := by
    simpa [prefixWord, tailWord_3216648, baseEnd_3216648] using wordTrace_append hprefix tailTrace_3216648
  have hstable : (prefixWord ++ tailWord_3216648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216648).length < 2 ^ (prefixWord ++ tailWord_3216648).sum := by decide
  have hdescent : baseEnd_3216648 < baseStart_3216648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216779 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 5]
def baseStart_3216779 : Nat := 118140960795 + 3216779 * 2 ^ 59
def prefixEnd_3216779 : Nat := 4983230072969 + 3 ^ 40 * 3216779 * 2
def baseEnd_3216779 : Nat := 367056396953194460237513

theorem tailTrace_3216779 : CollatzResearch.WordTrace tailWord_3216779 prefixEnd_3216779 367056396953194460237513 := by
  unfold tailWord_3216779
  simp only [CollatzResearch.WordTrace]
  refine ⟨117325568813166539959765391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78217045875444359973176927 117325568813166539959765391)
  ·
    refine ⟨175988353219749809939648087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117325568813166539959765391 175988353219749809939648087)
    ·
      refine ⟨263982529829624714909472131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175988353219749809939648087 263982529829624714909472131)
      ·
        refine ⟨395973794744437072364208197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263982529829624714909472131 395973794744437072364208197)
        ·
          refine ⟨74245086514581951068289037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395973794744437072364208197 74245086514581951068289037)
          ·
            refine ⟨27841907442968231650608389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74245086514581951068289037 27841907442968231650608389)
            ·
              refine ⟨5220357645556543434489073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27841907442968231650608389 5220357645556543434489073)
              ·
                refine ⟨3915268234167407575866805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5220357645556543434489073 3915268234167407575866805)
                ·
                  refine ⟨367056396953194460237513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3915268234167407575866805 367056396953194460237513)
                  ·
                    rfl

theorem cell22_3216779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 5].length) (baseStart_3216779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216779 prefixEnd_3216779 := by exact prefixLift 3216779
  have htrace : WordTrace (prefixWord ++ tailWord_3216779) baseStart_3216779 baseEnd_3216779 := by
    simpa [prefixWord, tailWord_3216779, baseEnd_3216779] using wordTrace_append hprefix tailTrace_3216779
  have hstable : (prefixWord ++ tailWord_3216779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216779).length < 2 ^ (prefixWord ++ tailWord_3216779).sum := by decide
  have hdescent : baseEnd_3216779 < baseStart_3216779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216794 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_3216794 : Nat := 118140960795 + 3216794 * 2 ^ 59
def prefixEnd_3216794 : Nat := 4983230072969 + 3 ^ 40 * 3216794 * 2
def baseEnd_3216794 : Nat := 1101174325666128341587493

theorem tailTrace_3216794 : CollatzResearch.WordTrace tailWord_3216794 prefixEnd_3216794 1101174325666128341587493 := by
  unfold tailWord_3216794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29331528977028049380390359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78217410605408131681040957 29331528977028049380390359)
  ·
    refine ⟨43997293465542074070585539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29331528977028049380390359 43997293465542074070585539)
    ·
      refine ⟨65995940198313111105878309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43997293465542074070585539 65995940198313111105878309)
      ·
        refine ⟨12374238787183708332352183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65995940198313111105878309 12374238787183708332352183)
        ·
          refine ⟨18561358180775562498528275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12374238787183708332352183 18561358180775562498528275)
          ·
            refine ⟨27842037271163343747792413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18561358180775562498528275 27842037271163343747792413)
            ·
              refine ⟨10440763976686253905422155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27842037271163343747792413 10440763976686253905422155)
              ·
                refine ⟨15661145965029380858133233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10440763976686253905422155 15661145965029380858133233)
                ·
                  refine ⟨11745859473772035643599925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15661145965029380858133233 11745859473772035643599925)
                  ·
                    refine ⟨1101174325666128341587493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11745859473772035643599925 1101174325666128341587493)
                    ·
                      rfl

theorem cell22_3216794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_3216794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216794 prefixEnd_3216794 := by exact prefixLift 3216794
  have htrace : WordTrace (prefixWord ++ tailWord_3216794) baseStart_3216794 baseEnd_3216794 := by
    simpa [prefixWord, tailWord_3216794, baseEnd_3216794] using wordTrace_append hprefix tailTrace_3216794
  have hstable : (prefixWord ++ tailWord_3216794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216794).length < 2 ^ (prefixWord ++ tailWord_3216794).sum := by decide
  have hdescent : baseEnd_3216794 < baseStart_3216794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216834 : List Nat := [3, 5, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3216834 : Nat := 118140960795 + 3216834 * 2 ^ 59
def prefixEnd_3216834 : Nat := 4983230072969 + 3 ^ 40 * 3216834 * 2
def baseEnd_3216834 : Nat := 1101188018483581570587371

theorem tailTrace_3216834 : CollatzResearch.WordTrace tailWord_3216834 prefixEnd_3216834 1101188018483581570587371 := by
  unfold tailWord_3216834
  simp only [CollatzResearch.WordTrace]
  refine ⟨29331893706991821088254389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78218383218644856235345037 29331893706991821088254389)
  ·
    refine ⟨2749865035030483227023849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29331893706991821088254389 2749865035030483227023849)
    ·
      refine ⟨2062398776272862420267887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2749865035030483227023849 2062398776272862420267887)
      ·
        refine ⟨3093598164409293630401831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062398776272862420267887 3093598164409293630401831)
        ·
          refine ⟨4640397246613940445602747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3093598164409293630401831 4640397246613940445602747)
          ·
            refine ⟨6960595869920910668404121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640397246613940445602747 6960595869920910668404121)
            ·
              refine ⟨5220446902440683001303091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6960595869920910668404121 5220446902440683001303091)
              ·
                refine ⟨7830670353661024501954637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220446902440683001303091 7830670353661024501954637)
                ·
                  refine ⟨2936501382622884188232989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7830670353661024501954637 2936501382622884188232989)
                  ·
                    refine ⟨1101188018483581570587371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936501382622884188232989 1101188018483581570587371)
                    ·
                      rfl

theorem cell22_3216834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3216834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216834 prefixEnd_3216834 := by exact prefixLift 3216834
  have htrace : WordTrace (prefixWord ++ tailWord_3216834) baseStart_3216834 baseEnd_3216834 := by
    simpa [prefixWord, tailWord_3216834, baseEnd_3216834] using wordTrace_append hprefix tailTrace_3216834
  have hstable : (prefixWord ++ tailWord_3216834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216834).length < 2 ^ (prefixWord ++ tailWord_3216834).sum := by decide
  have hdescent : baseEnd_3216834 < baseStart_3216834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216856 : List Nat := [2, 1, 2, 2, 2, 1, 2, 5, 2, 3]
def baseStart_3216856 : Nat := 118140960795 + 3216856 * 2 ^ 59
def prefixEnd_3216856 : Nat := 4983230072969 + 3 ^ 40 * 3216856 * 2
def baseEnd_3216856 : Nat := 1101195549533180846537303

theorem tailTrace_3216856 : CollatzResearch.WordTrace tailWord_3216856 prefixEnd_3216856 1101195549533180846537303 := by
  unfold tailWord_3216856
  simp only [CollatzResearch.WordTrace]
  refine ⟨58664188616943791055159211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78218918155925054740212281 58664188616943791055159211)
  ·
    refine ⟨87996282925415686582738817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58664188616943791055159211 87996282925415686582738817)
    ·
      refine ⟨65997212194061764937054113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87996282925415686582738817 65997212194061764937054113)
      ·
        refine ⟨49497909145546323702790585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65997212194061764937054113 49497909145546323702790585)
        ·
          refine ⟨37123431859159742777092939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49497909145546323702790585 37123431859159742777092939)
          ·
            refine ⟨55685147788739614165639409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37123431859159742777092939 55685147788739614165639409)
            ·
              refine ⟨41763860841554710624229557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55685147788739614165639409 41763860841554710624229557)
              ·
                refine ⟨3915361953895754121021521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41763860841554710624229557 3915361953895754121021521)
                ·
                  refine ⟨2936521465421815590766141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3915361953895754121021521 2936521465421815590766141)
                  ·
                    refine ⟨1101195549533180846537303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936521465421815590766141 1101195549533180846537303)
                    ·
                      rfl

theorem cell22_3216856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_3216856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216856 prefixEnd_3216856 := by exact prefixLift 3216856
  have htrace : WordTrace (prefixWord ++ tailWord_3216856) baseStart_3216856 baseEnd_3216856 := by
    simpa [prefixWord, tailWord_3216856, baseEnd_3216856] using wordTrace_append hprefix tailTrace_3216856
  have hstable : (prefixWord ++ tailWord_3216856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216856).length < 2 ^ (prefixWord ++ tailWord_3216856).sum := by decide
  have hdescent : baseEnd_3216856 < baseStart_3216856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216886 : List Nat := [5, 1, 1, 1, 2, 4, 8]
def baseStart_3216886 : Nat := 118140960795 + 3216886 * 2 ^ 59
def prefixEnd_3216886 : Nat := 4983230072969 + 3 ^ 40 * 3216886 * 2
def baseEnd_3216886 : Nat := 40785400709121139566193

theorem tailTrace_3216886 : CollatzResearch.WordTrace tailWord_3216886 prefixEnd_3216886 40785400709121139566193 := by
  unfold tailWord_3216886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7333091963986181077119407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78219647615852598155940341 7333091963986181077119407)
  ·
    refine ⟨10999637945979271615679111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7333091963986181077119407 10999637945979271615679111)
    ·
      refine ⟨16499456918968907423518667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10999637945979271615679111 16499456918968907423518667)
      ·
        refine ⟨24749185378453361135278001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16499456918968907423518667 24749185378453361135278001)
        ·
          refine ⟨18561889033840020851458501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24749185378453361135278001 18561889033840020851458501)
          ·
            refine ⟨3480354193845003909648469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18561889033840020851458501 3480354193845003909648469)
            ·
              refine ⟨40785400709121139566193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3480354193845003909648469 40785400709121139566193)
              ·
                rfl

theorem cell22_3216886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 8].length) (baseStart_3216886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216886 prefixEnd_3216886 := by exact prefixLift 3216886
  have htrace : WordTrace (prefixWord ++ tailWord_3216886) baseStart_3216886 baseEnd_3216886 := by
    simpa [prefixWord, tailWord_3216886, baseEnd_3216886] using wordTrace_append hprefix tailTrace_3216886
  have hstable : (prefixWord ++ tailWord_3216886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216886).length < 2 ^ (prefixWord ++ tailWord_3216886).sum := by decide
  have hdescent : baseEnd_3216886 < baseStart_3216886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216907 : List Nat := [1, 1, 1, 1, 9, 1, 2, 1, 2, 3]
def baseStart_3216907 : Nat := 118140960795 + 3216907 * 2 ^ 59
def prefixEnd_3216907 : Nat := 4983230072969 + 3 ^ 40 * 3216907 * 2
def baseEnd_3216907 : Nat := 1101213007875433713512147

theorem tailTrace_3216907 : CollatzResearch.WordTrace tailWord_3216907 prefixEnd_3216907 1101213007875433713512147 := by
  unfold tailWord_3216907
  simp only [CollatzResearch.WordTrace]
  refine ⟨117330237356702817820424975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78220158237801878546949983 117330237356702817820424975)
  ·
    refine ⟨175995356035054226730637463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117330237356702817820424975 175995356035054226730637463)
    ·
      refine ⟨263993034052581340095956195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175995356035054226730637463 263993034052581340095956195)
      ·
        refine ⟨395989551078872010143934293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263993034052581340095956195 395989551078872010143934293)
        ·
          refine ⟨2320251275852765684437115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 395989551078872010143934293 2320251275852765684437115)
          ·
            refine ⟨3480376913779148526655673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320251275852765684437115 3480376913779148526655673)
            ·
              refine ⟨2610282685334361394991755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480376913779148526655673 2610282685334361394991755)
              ·
                refine ⟨3915424028001542092487633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610282685334361394991755 3915424028001542092487633)
                ·
                  refine ⟨2936568021001156569365725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3915424028001542092487633 2936568021001156569365725)
                  ·
                    refine ⟨1101213007875433713512147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936568021001156569365725 1101213007875433713512147)
                    ·
                      rfl

theorem cell22_3216907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 2, 3].length) (baseStart_3216907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216907 prefixEnd_3216907 := by exact prefixLift 3216907
  have htrace : WordTrace (prefixWord ++ tailWord_3216907) baseStart_3216907 baseEnd_3216907 := by
    simpa [prefixWord, tailWord_3216907, baseEnd_3216907] using wordTrace_append hprefix tailTrace_3216907
  have hstable : (prefixWord ++ tailWord_3216907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216907).length < 2 ^ (prefixWord ++ tailWord_3216907).sum := by decide
  have hdescent : baseEnd_3216907 < baseStart_3216907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216952 : List Nat := [2, 1, 2, 1, 4, 4, 2, 2, 1, 3]
def baseStart_3216952 : Nat := 118140960795 + 3216952 * 2 ^ 59
def prefixEnd_3216952 : Nat := 4983230072969 + 3 ^ 40 * 3216952 * 2
def baseEnd_3216952 : Nat := 1101228412295068596137009

theorem tailTrace_3216952 : CollatzResearch.WordTrace tailWord_3216952 prefixEnd_3216952 1101228412295068596137009 := by
  unfold tailWord_3216952
  simp only [CollatzResearch.WordTrace]
  refine ⟨58665939320769895252906555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78221252427693193670542073 58665939320769895252906555)
  ·
    refine ⟨87998908981154842879359833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58665939320769895252906555 87998908981154842879359833)
    ·
      refine ⟨65999181735866132159519875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87998908981154842879359833 65999181735866132159519875)
      ·
        refine ⟨98998772603799198239279813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65999181735866132159519875 98998772603799198239279813)
        ·
          refine ⟨18562269863212349669864965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98998772603799198239279813 18562269863212349669864965)
          ·
            refine ⟨3480425599352315563099681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18562269863212349669864965 3480425599352315563099681)
            ·
              refine ⟨2610319199514236672324761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480425599352315563099681 2610319199514236672324761)
              ·
                refine ⟨1957739399635677504243571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2610319199514236672324761 1957739399635677504243571)
                ·
                  refine ⟨2936609099453516256365357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957739399635677504243571 2936609099453516256365357)
                  ·
                    refine ⟨1101228412295068596137009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936609099453516256365357 1101228412295068596137009)
                    ·
                      rfl

theorem cell22_3216952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_3216952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216952 prefixEnd_3216952 := by exact prefixLift 3216952
  have htrace : WordTrace (prefixWord ++ tailWord_3216952) baseStart_3216952 baseEnd_3216952 := by
    simpa [prefixWord, tailWord_3216952, baseEnd_3216952] using wordTrace_append hprefix tailTrace_3216952
  have hstable : (prefixWord ++ tailWord_3216952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216952).length < 2 ^ (prefixWord ++ tailWord_3216952).sum := by decide
  have hdescent : baseEnd_3216952 < baseStart_3216952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216961 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3216961 : Nat := 118140960795 + 3216961 * 2 ^ 59
def prefixEnd_3216961 : Nat := 4983230072969 + 3 ^ 40 * 3216961 * 2
def baseEnd_3216961 : Nat := 1101231493178995572661981

theorem tailTrace_3216961 : CollatzResearch.WordTrace tailWord_3216961 prefixEnd_3216961 1101231493178995572661981 := by
  unfold tailWord_3216961
  simp only [CollatzResearch.WordTrace]
  refine ⟨117332206898507185042890737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78221471265671456695260491 117332206898507185042890737)
  ·
    refine ⟨87999155173880388782168053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117332206898507185042890737 87999155173880388782168053)
    ·
      refine ⟨8249920797551286448328255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87999155173880388782168053 8249920797551286448328255)
      ·
        refine ⟨12374881196326929672492383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8249920797551286448328255 12374881196326929672492383)
        ·
          refine ⟨18562321794490394508738575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12374881196326929672492383 18562321794490394508738575)
          ·
            refine ⟨27843482691735591763107863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18562321794490394508738575 27843482691735591763107863)
            ·
              refine ⟨41765224037603387644661795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27843482691735591763107863 41765224037603387644661795)
              ·
                refine ⟨62647836056405081466992693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41765224037603387644661795 62647836056405081466992693)
                ·
                  refine ⟨5873234630287976387530565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62647836056405081466992693 5873234630287976387530565)
                  ·
                    refine ⟨1101231493178995572661981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5873234630287976387530565 1101231493178995572661981)
                    ·
                      rfl

theorem cell22_3216961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3216961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216961 prefixEnd_3216961 := by exact prefixLift 3216961
  have htrace : WordTrace (prefixWord ++ tailWord_3216961) baseStart_3216961 baseEnd_3216961 := by
    simpa [prefixWord, tailWord_3216961, baseEnd_3216961] using wordTrace_append hprefix tailTrace_3216961
  have hstable : (prefixWord ++ tailWord_3216961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216961).length < 2 ^ (prefixWord ++ tailWord_3216961).sum := by decide
  have hdescent : baseEnd_3216961 < baseStart_3216961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216993 : List Nat := [1, 2, 3, 1, 1, 3, 4, 3, 4]
def baseStart_3216993 : Nat := 118140960795 + 3216993 * 2 ^ 59
def prefixEnd_3216993 : Nat := 4983230072969 + 3 ^ 40 * 3216993 * 2
def baseEnd_3216993 : Nat := 367080815810986051953961

theorem tailTrace_3216993 : CollatzResearch.WordTrace tailWord_3216993 prefixEnd_3216993 367080815810986051953961 := by
  unfold tailWord_3216993
  simp only [CollatzResearch.WordTrace]
  refine ⟨117333374034391254508055633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78222249356260836338703755 117333374034391254508055633)
  ·
    refine ⟨88000030525793440881041725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117333374034391254508055633 88000030525793440881041725)
    ·
      refine ⟨33000011447172540330390647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88000030525793440881041725 33000011447172540330390647)
      ·
        refine ⟨49500017170758810495585971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33000011447172540330390647 49500017170758810495585971)
        ·
          refine ⟨74250025756138215743378957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49500017170758810495585971 74250025756138215743378957)
          ·
            refine ⟨27843759658551830903767109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74250025756138215743378957 27843759658551830903767109)
            ·
              refine ⟨5220704935978468294456333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27843759658551830903767109 5220704935978468294456333)
              ·
                refine ⟨1957764350991925610421125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5220704935978468294456333 1957764350991925610421125)
                ·
                  refine ⟨367080815810986051953961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957764350991925610421125 367080815810986051953961)
                  ·
                    rfl

theorem cell22_3216993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 4].length) (baseStart_3216993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216993 prefixEnd_3216993 := by exact prefixLift 3216993
  have htrace : WordTrace (prefixWord ++ tailWord_3216993) baseStart_3216993 baseEnd_3216993 := by
    simpa [prefixWord, tailWord_3216993, baseEnd_3216993] using wordTrace_append hprefix tailTrace_3216993
  have hstable : (prefixWord ++ tailWord_3216993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216993).length < 2 ^ (prefixWord ++ tailWord_3216993).sum := by decide
  have hdescent : baseEnd_3216993 < baseStart_3216993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3216995 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 1, 4]
def baseStart_3216995 : Nat := 118140960795 + 3216995 * 2 ^ 59
def prefixEnd_3216995 : Nat := 4983230072969 + 3 ^ 40 * 3216995 * 2
def baseEnd_3216995 : Nat := 1101243132073830817311877

theorem tailTrace_3216995 : CollatzResearch.WordTrace tailWord_3216995 prefixEnd_3216995 1101243132073830817311877 := by
  unfold tailWord_3216995
  simp only [CollatzResearch.WordTrace]
  refine ⟨117333446980384008849628439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78222297986922672566418959 117333446980384008849628439)
  ·
    refine ⟨176000170470576013274442659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117333446980384008849628439 176000170470576013274442659)
    ·
      refine ⟨264000255705864019911663989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176000170470576013274442659 264000255705864019911663989)
      ·
        refine ⟨24750023972424751866718499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 264000255705864019911663989 24750023972424751866718499)
        ·
          refine ⟨37125035958637127800077749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24750023972424751866718499 37125035958637127800077749)
          ·
            refine ⟨3480472121122230731257289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37125035958637127800077749 3480472121122230731257289)
            ·
              refine ⟨2610354090841673048442967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480472121122230731257289 2610354090841673048442967)
              ·
                refine ⟨3915531136262509572664451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610354090841673048442967 3915531136262509572664451)
                ·
                  refine ⟨5873296704393764358996677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3915531136262509572664451 5873296704393764358996677)
                  ·
                    refine ⟨1101243132073830817311877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5873296704393764358996677 1101243132073830817311877)
                    ·
                      rfl

theorem cell22_3216995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 4].length) (baseStart_3216995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3216995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3216995 prefixEnd_3216995 := by exact prefixLift 3216995
  have htrace : WordTrace (prefixWord ++ tailWord_3216995) baseStart_3216995 baseEnd_3216995 := by
    simpa [prefixWord, tailWord_3216995, baseEnd_3216995] using wordTrace_append hprefix tailTrace_3216995
  have hstable : (prefixWord ++ tailWord_3216995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3216995).length < 2 ^ (prefixWord ++ tailWord_3216995).sum := by decide
  have hdescent : baseEnd_3216995 < baseStart_3216995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3216995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217008 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 4, 3]
def baseStart_3217008 : Nat := 118140960795 + 3217008 * 2 ^ 59
def prefixEnd_3217008 : Nat := 4983230072969 + 3 ^ 40 * 3217008 * 2
def baseEnd_3217008 : Nat := 1101247582239503116736837

theorem tailTrace_3217008 : CollatzResearch.WordTrace tailWord_3217008 prefixEnd_3217008 1101247582239503116736837 := by
  unfold tailWord_3217008
  simp only [CollatzResearch.WordTrace]
  refine ⟨58666960564668456034925839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78222614086224608046567785 58666960564668456034925839)
  ·
    refine ⟨88000440847002684052388759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58666960564668456034925839 88000440847002684052388759)
    ·
      refine ⟨132000661270504026078583139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88000440847002684052388759 132000661270504026078583139)
      ·
        refine ⟨198000991905756039117874709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132000661270504026078583139 198000991905756039117874709)
        ·
          refine ⟨9281296495582314333650377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198000991905756039117874709 9281296495582314333650377)
          ·
            refine ⟨6960972371686735750237783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9281296495582314333650377 6960972371686735750237783)
            ·
              refine ⟨10441458557530103625356675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6960972371686735750237783 10441458557530103625356675)
              ·
                refine ⟨15662187836295155438035013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10441458557530103625356675 15662187836295155438035013)
                ·
                  refine ⟨2936660219305341644631565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15662187836295155438035013 2936660219305341644631565)
                  ·
                    refine ⟨1101247582239503116736837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936660219305341644631565 1101247582239503116736837)
                    ·
                      rfl

theorem cell22_3217008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_3217008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217008 prefixEnd_3217008 := by exact prefixLift 3217008
  have htrace : WordTrace (prefixWord ++ tailWord_3217008) baseStart_3217008 baseEnd_3217008 := by
    simpa [prefixWord, tailWord_3217008, baseEnd_3217008] using wordTrace_append hprefix tailTrace_3217008
  have hstable : (prefixWord ++ tailWord_3217008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217008).length < 2 ^ (prefixWord ++ tailWord_3217008).sum := by decide
  have hdescent : baseEnd_3217008 < baseStart_3217008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217038 : List Nat := [4, 1, 1, 3, 1, 2, 4, 6]
def baseStart_3217038 : Nat := 118140960795 + 3217038 * 2 ^ 59
def prefixEnd_3217038 : Nat := 4983230072969 + 3 ^ 40 * 3217038 * 2
def baseEnd_3217038 : Nat := 122361983539177004276305

theorem tailTrace_3217038 : CollatzResearch.WordTrace tailWord_3217038 prefixEnd_3217038 122361983539177004276305 := by
  unfold tailWord_3217038
  simp only [CollatzResearch.WordTrace]
  refine ⟨14666876914903528399180471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78223343546152151462295845 14666876914903528399180471)
  ·
    refine ⟨22000315372355292598770707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14666876914903528399180471 22000315372355292598770707)
    ·
      refine ⟨33000473058532938898156061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22000315372355292598770707 33000473058532938898156061)
      ·
        refine ⟨12375177396949852086808523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33000473058532938898156061 12375177396949852086808523)
        ·
          refine ⟨18562766095424778130212785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12375177396949852086808523 18562766095424778130212785)
          ·
            refine ⟨13922074571568583597659589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18562766095424778130212785 13922074571568583597659589)
            ·
              refine ⟨2610388982169109424561173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13922074571568583597659589 2610388982169109424561173)
              ·
                refine ⟨122361983539177004276305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2610388982169109424561173 122361983539177004276305)
                ·
                  rfl

theorem cell22_3217038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_3217038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217038 prefixEnd_3217038 := by exact prefixLift 3217038
  have htrace : WordTrace (prefixWord ++ tailWord_3217038) baseStart_3217038 baseEnd_3217038 := by
    simpa [prefixWord, tailWord_3217038, baseEnd_3217038] using wordTrace_append hprefix tailTrace_3217038
  have hstable : (prefixWord ++ tailWord_3217038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217038).length < 2 ^ (prefixWord ++ tailWord_3217038).sum := by decide
  have hdescent : baseEnd_3217038 < baseStart_3217038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217044 : List Nat := [2, 4, 2, 2, 3, 1, 1, 3, 4]
def baseStart_3217044 : Nat := 118140960795 + 3217044 * 2 ^ 59
def prefixEnd_3217044 : Nat := 4983230072969 + 3 ^ 40 * 3217044 * 2
def baseEnd_3217044 : Nat := 367086635258403674278909

theorem tailTrace_3217044 : CollatzResearch.WordTrace tailWord_3217044 prefixEnd_3217044 367086635258403674278909 := by
  unfold tailWord_3217044
  simp only [CollatzResearch.WordTrace]
  refine ⟨58667617078603245109081093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78223489438137660145441457 58667617078603245109081093)
  ·
    refine ⟨11000178202238108457952705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58667617078603245109081093 11000178202238108457952705)
    ·
      refine ⟨8250133651678581343464529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11000178202238108457952705 8250133651678581343464529)
      ·
        refine ⟨6187600238758936007598397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8250133651678581343464529 6187600238758936007598397)
        ·
          refine ⟨2320350089534601002849399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6187600238758936007598397 2320350089534601002849399)
          ·
            refine ⟨3480525134301901504274099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320350089534601002849399 3480525134301901504274099)
            ·
              refine ⟨5220787701452852256411149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480525134301901504274099 5220787701452852256411149)
              ·
                refine ⟨1957795388044819596154181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5220787701452852256411149 1957795388044819596154181)
                ·
                  refine ⟨367086635258403674278909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957795388044819596154181 367086635258403674278909)
                  ·
                    rfl

theorem cell22_3217044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_3217044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217044 prefixEnd_3217044 := by exact prefixLift 3217044
  have htrace : WordTrace (prefixWord ++ tailWord_3217044) baseStart_3217044 baseEnd_3217044 := by
    simpa [prefixWord, tailWord_3217044, baseEnd_3217044] using wordTrace_append hprefix tailTrace_3217044
  have hstable : (prefixWord ++ tailWord_3217044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217044).length < 2 ^ (prefixWord ++ tailWord_3217044).sum := by decide
  have hdescent : baseEnd_3217044 < baseStart_3217044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217055 : List Nat := [1, 1, 2, 7, 2, 1, 8]
def baseStart_3217055 : Nat := 118140960795 + 3217055 * 2 ^ 59
def prefixEnd_3217055 : Nat := 4983230072969 + 3 ^ 40 * 3217055 * 2
def baseEnd_3217055 : Nat := 40787543381481876326359

theorem tailTrace_3217055 : CollatzResearch.WordTrace tailWord_3217055 prefixEnd_3217055 40787543381481876326359 := by
  unfold tailWord_3217055
  simp only [CollatzResearch.WordTrace]
  refine ⟨117335635360166639096812619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78223756906777759397875079 117335635360166639096812619)
  ·
    refine ⟨176003453040249958645218929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117335635360166639096812619 176003453040249958645218929)
    ·
      refine ⟨132002589780187468983914197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176003453040249958645218929 132002589780187468983914197)
      ·
        refine ⟨3093810697973143804310489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 132002589780187468983914197 3093810697973143804310489)
        ·
          refine ⟨2320358023479857853232867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3093810697973143804310489 2320358023479857853232867)
          ·
            refine ⟨3480537035219786779849301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320358023479857853232867 3480537035219786779849301)
            ·
              refine ⟨40787543381481876326359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3480537035219786779849301 40787543381481876326359)
              ·
                rfl

theorem cell22_3217055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 8].length) (baseStart_3217055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217055 prefixEnd_3217055 := by exact prefixLift 3217055
  have htrace : WordTrace (prefixWord ++ tailWord_3217055) baseStart_3217055 baseEnd_3217055 := by
    simpa [prefixWord, tailWord_3217055, baseEnd_3217055] using wordTrace_append hprefix tailTrace_3217055
  have hstable : (prefixWord ++ tailWord_3217055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217055).length < 2 ^ (prefixWord ++ tailWord_3217055).sum := by decide
  have hdescent : baseEnd_3217055 < baseStart_3217055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217081 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_3217081 : Nat := 118140960795 + 3217081 * 2 ^ 59
def prefixEnd_3217081 : Nat := 4983230072969 + 3 ^ 40 * 3217081 * 2
def baseEnd_3217081 : Nat := 1101272571631355259661613

theorem tailTrace_3217081 : CollatzResearch.WordTrace tailWord_3217081 prefixEnd_3217081 1101272571631355259661613 := by
  unfold tailWord_3217081
  simp only [CollatzResearch.WordTrace]
  refine ⟨117336583658072445537259097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78224389105381630358172731 117336583658072445537259097)
  ·
    refine ⟨88002437743554334152944323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117336583658072445537259097 88002437743554334152944323)
    ·
      refine ⟨132003656615331501229416485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88002437743554334152944323 132003656615331501229416485)
      ·
        refine ⟨24750685615374656480515591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132003656615331501229416485 24750685615374656480515591)
        ·
          refine ⟨37126028423061984720773387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24750685615374656480515591 37126028423061984720773387)
          ·
            refine ⟨55689042634592977081160081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37126028423061984720773387 55689042634592977081160081)
            ·
              refine ⟨41766781975944732810870061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55689042634592977081160081 41766781975944732810870061)
              ·
                refine ⟨15662543240979274804076273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41766781975944732810870061 15662543240979274804076273)
                ·
                  refine ⟨11746907430734456103057205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15662543240979274804076273 11746907430734456103057205)
                  ·
                    refine ⟨1101272571631355259661613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11746907430734456103057205 1101272571631355259661613)
                    ·
                      rfl

theorem cell22_3217081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_3217081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217081 prefixEnd_3217081 := by exact prefixLift 3217081
  have htrace : WordTrace (prefixWord ++ tailWord_3217081) baseStart_3217081 baseEnd_3217081 := by
    simpa [prefixWord, tailWord_3217081, baseEnd_3217081] using wordTrace_append hprefix tailTrace_3217081
  have hstable : (prefixWord ++ tailWord_3217081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217081).length < 2 ^ (prefixWord ++ tailWord_3217081).sum := by decide
  have hdescent : baseEnd_3217081 < baseStart_3217081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217117 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 5]
def baseStart_3217117 : Nat := 118140960795 + 3217117 * 2 ^ 59
def prefixEnd_3217117 : Nat := 4983230072969 + 3 ^ 40 * 3217117 * 2
def baseEnd_3217117 : Nat := 367094965055687721920501

theorem tailTrace_3217117 : CollatzResearch.WordTrace tailWord_3217117 prefixEnd_3217117 367094965055687721920501 := by
  unfold tailWord_3217117
  simp only [CollatzResearch.WordTrace]
  refine ⟨117337896685942023685569605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78225264457294682457046403 117337896685942023685569605)
  ·
    refine ⟨22000855628614129441044301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117337896685942023685569605 22000855628614129441044301)
    ·
      refine ⟨8250320860730298540391613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22000855628614129441044301 8250320860730298540391613)
      ·
        refine ⟨3093870322773861952646855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8250320860730298540391613 3093870322773861952646855)
        ·
          refine ⟨4640805484160792928970283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3093870322773861952646855 4640805484160792928970283)
          ·
            refine ⟨6961208226241189393455425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640805484160792928970283 6961208226241189393455425)
            ·
              refine ⟨5220906169680892045091569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6961208226241189393455425 5220906169680892045091569)
              ·
                refine ⟨3915679627260669033818677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5220906169680892045091569 3915679627260669033818677)
                ·
                  refine ⟨367094965055687721920501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3915679627260669033818677 367094965055687721920501)
                  ·
                    rfl

theorem cell22_3217117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_3217117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217117 prefixEnd_3217117 := by exact prefixLift 3217117
  have htrace : WordTrace (prefixWord ++ tailWord_3217117) baseStart_3217117 baseEnd_3217117 := by
    simpa [prefixWord, tailWord_3217117, baseEnd_3217117] using wordTrace_append hprefix tailTrace_3217117
  have hstable : (prefixWord ++ tailWord_3217117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217117).length < 2 ^ (prefixWord ++ tailWord_3217117).sum := by decide
  have hdescent : baseEnd_3217117 < baseStart_3217117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217121 : List Nat := [1, 2, 3, 1, 6, 1, 2, 2, 1, 3]
def baseStart_3217121 : Nat := 118140960795 + 3217121 * 2 ^ 59
def prefixEnd_3217121 : Nat := 4983230072969 + 3 ^ 40 * 3217121 * 2
def baseEnd_3217121 : Nat := 1101286264448808488661491

theorem tailTrace_3217121 : CollatzResearch.WordTrace tailWord_3217121 prefixEnd_3217121 1101286264448808488661491 := by
  unfold tailWord_3217121
  simp only [CollatzResearch.WordTrace]
  refine ⟨117338042577927532368715217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78225361718618354912476811 117338042577927532368715217)
  ·
    refine ⟨88003531933445649276536413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117338042577927532368715217 88003531933445649276536413)
    ·
      refine ⟨33001324475042118478701155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88003531933445649276536413 33001324475042118478701155)
      ·
        refine ⟨49501986712563177718051733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33001324475042118478701155 49501986712563177718051733)
        ·
          refine ⟨2320405627151398955533675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49501986712563177718051733 2320405627151398955533675)
          ·
            refine ⟨3480608440727098433300513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320405627151398955533675 3480608440727098433300513)
            ·
              refine ⟨2610456330545323824975385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480608440727098433300513 2610456330545323824975385)
              ·
                refine ⟨1957842247908992868731539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2610456330545323824975385 1957842247908992868731539)
                ·
                  refine ⟨2936763371863489303097309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957842247908992868731539 2936763371863489303097309)
                  ·
                    refine ⟨1101286264448808488661491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936763371863489303097309 1101286264448808488661491)
                    ·
                      rfl

theorem cell22_3217121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_3217121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217121 prefixEnd_3217121 := by exact prefixLift 3217121
  have htrace : WordTrace (prefixWord ++ tailWord_3217121) baseStart_3217121 baseEnd_3217121 := by
    simpa [prefixWord, tailWord_3217121, baseEnd_3217121] using wordTrace_append hprefix tailTrace_3217121
  have hstable : (prefixWord ++ tailWord_3217121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217121).length < 2 ^ (prefixWord ++ tailWord_3217121).sum := by decide
  have hdescent : baseEnd_3217121 < baseStart_3217121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217239 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 3, 3]
def baseStart_3217239 : Nat := 118140960795 + 3217239 * 2 ^ 59
def prefixEnd_3217239 : Nat := 4983230072969 + 3 ^ 40 * 3217239 * 2
def baseEnd_3217239 : Nat := 1101326658260295514211129

theorem tailTrace_3217239 : CollatzResearch.WordTrace tailWord_3217239 prefixEnd_3217239 1101326658260295514211129 := by
  unfold tailWord_3217239
  simp only [CollatzResearch.WordTrace]
  refine ⟨117342346391500038521510771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78228230927666692347673847 117342346391500038521510771)
  ·
    refine ⟨176013519587250057782266157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117342346391500038521510771 176013519587250057782266157)
    ·
      refine ⟨66005069845218771668349809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176013519587250057782266157 66005069845218771668349809)
      ·
        refine ⟨49503802383914078751262357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66005069845218771668349809 49503802383914078751262357)
        ·
          refine ⟨2320490736745972441465423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49503802383914078751262357 2320490736745972441465423)
          ·
            refine ⟨3480736105118958662198135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320490736745972441465423 3480736105118958662198135)
            ·
              refine ⟨5221104157678437993297203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480736105118958662198135 5221104157678437993297203)
              ·
                refine ⟨7831656236517656989945805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221104157678437993297203 7831656236517656989945805)
                ·
                  refine ⟨2936871088694121371229677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7831656236517656989945805 2936871088694121371229677)
                  ·
                    refine ⟨1101326658260295514211129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936871088694121371229677 1101326658260295514211129)
                    ·
                      rfl

theorem cell22_3217239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_3217239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217239 prefixEnd_3217239 := by exact prefixLift 3217239
  have htrace : WordTrace (prefixWord ++ tailWord_3217239) baseStart_3217239 baseEnd_3217239 := by
    simpa [prefixWord, tailWord_3217239, baseEnd_3217239] using wordTrace_append hprefix tailTrace_3217239
  have hstable : (prefixWord ++ tailWord_3217239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217239).length < 2 ^ (prefixWord ++ tailWord_3217239).sum := by decide
  have hdescent : baseEnd_3217239 < baseStart_3217239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217280 : List Nat := [2, 1, 1, 2, 1, 2, 4, 5, 4]
def baseStart_3217280 : Nat := 118140960795 + 3217280 * 2 ^ 59
def prefixEnd_3217280 : Nat := 4983230072969 + 3 ^ 40 * 3217280 * 2
def baseEnd_3217280 : Nat := 367113564466061691312001

theorem tailTrace_3217280 : CollatzResearch.WordTrace tailWord_3217280 prefixEnd_3217280 367113564466061691312001 := by
  unfold tailWord_3217280
  simp only [CollatzResearch.WordTrace]
  refine ⟨58671920892175751261876647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78229227856234335015835529 58671920892175751261876647)
  ·
    refine ⟨88007881338263626892814971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58671920892175751261876647 88007881338263626892814971)
    ·
      refine ⟨132011822007395440339222457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88007881338263626892814971 132011822007395440339222457)
      ·
        refine ⟨99008866505546580254416843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132011822007395440339222457 99008866505546580254416843)
        ·
          refine ⟨148513299758319870381625265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99008866505546580254416843 148513299758319870381625265)
          ·
            refine ⟨111384974818739902786218949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148513299758319870381625265 111384974818739902786218949)
            ·
              refine ⟨20884682778513731772416053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111384974818739902786218949 20884682778513731772416053)
              ·
                refine ⟨1957939010485662353664005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20884682778513731772416053 1957939010485662353664005)
                ·
                  refine ⟨367113564466061691312001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957939010485662353664005 367113564466061691312001)
                  ·
                    rfl

theorem cell22_3217280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 4].length) (baseStart_3217280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217280 prefixEnd_3217280 := by exact prefixLift 3217280
  have htrace : WordTrace (prefixWord ++ tailWord_3217280) baseStart_3217280 baseEnd_3217280 := by
    simpa [prefixWord, tailWord_3217280, baseEnd_3217280] using wordTrace_append hprefix tailTrace_3217280
  have hstable : (prefixWord ++ tailWord_3217280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217280).length < 2 ^ (prefixWord ++ tailWord_3217280).sum := by decide
  have hdescent : baseEnd_3217280 < baseStart_3217280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217297 : List Nat := [1, 2, 2, 1, 1, 1, 8, 2, 4]
def baseStart_3217297 : Nat := 118140960795 + 3217297 * 2 ^ 59
def prefixEnd_3217297 : Nat := 4983230072969 + 3 ^ 40 * 3217297 * 2
def baseEnd_3217297 : Nat := 367115504281867565420317

theorem tailTrace_3217297 : CollatzResearch.WordTrace tailWord_3217297 prefixEnd_3217297 367115504281867565420317 := by
  unfold tailWord_3217297
  simp only [CollatzResearch.WordTrace]
  refine ⟨117344461825289914427122145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78229641216859942951414763 117344461825289914427122145)
  ·
    refine ⟨88008346368967435820341609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117344461825289914427122145 88008346368967435820341609)
    ·
      refine ⟨66006259776725576865256207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88008346368967435820341609 66006259776725576865256207)
      ·
        refine ⟨99009389665088365297884311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66006259776725576865256207 99009389665088365297884311)
        ·
          refine ⟨148514084497632547946826467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99009389665088365297884311 148514084497632547946826467)
          ·
            refine ⟨222771126746448821920239701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148514084497632547946826467 222771126746448821920239701)
            ·
              refine ⟨2610599141559947131877809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 222771126746448821920239701 2610599141559947131877809)
              ·
                refine ⟨1957949356169960348908357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2610599141559947131877809 1957949356169960348908357)
                ·
                  refine ⟨367115504281867565420317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1957949356169960348908357 367115504281867565420317)
                  ·
                    rfl

theorem cell22_3217297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 4].length) (baseStart_3217297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217297 prefixEnd_3217297 := by exact prefixLift 3217297
  have htrace : WordTrace (prefixWord ++ tailWord_3217297) baseStart_3217297 baseEnd_3217297 := by
    simpa [prefixWord, tailWord_3217297, baseEnd_3217297] using wordTrace_append hprefix tailTrace_3217297
  have hstable : (prefixWord ++ tailWord_3217297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217297).length < 2 ^ (prefixWord ++ tailWord_3217297).sum := by decide
  have hdescent : baseEnd_3217297 < baseStart_3217297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217338 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_3217338 : Nat := 118140960795 + 3217338 * 2 ^ 59
def prefixEnd_3217338 : Nat := 4983230072969 + 3 ^ 40 * 3217338 * 2
def baseEnd_3217338 : Nat := 1101360547983492255985825

theorem tailTrace_3217338 : CollatzResearch.WordTrace tailWord_3217338 prefixEnd_3217338 1101360547983492255985825 := by
  unfold tailWord_3217338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29336489304535344607341167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78230638145427585619576445 29336489304535344607341167)
  ·
    refine ⟨44004733956803016911011751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29336489304535344607341167 44004733956803016911011751)
    ·
      refine ⟨66007100935204525366517627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44004733956803016911011751 66007100935204525366517627)
      ·
        refine ⟨99010651402806788049776441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66007100935204525366517627 99010651402806788049776441)
        ·
          refine ⟨74257988552105091037332331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99010651402806788049776441 74257988552105091037332331)
          ·
            refine ⟨111386982828157636555998497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74257988552105091037332331 111386982828157636555998497)
            ·
              refine ⟨83540237121118227416998873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111386982828157636555998497 83540237121118227416998873)
              ·
                refine ⟨62655177840838670562749155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83540237121118227416998873 62655177840838670562749155)
                ·
                  refine ⟨93982766761258005844123733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62655177840838670562749155 93982766761258005844123733)
                  ·
                    refine ⟨1101360547983492255985825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93982766761258005844123733 1101360547983492255985825)
                    ·
                      rfl

theorem cell22_3217338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_3217338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217338 prefixEnd_3217338 := by exact prefixLift 3217338
  have htrace : WordTrace (prefixWord ++ tailWord_3217338) baseStart_3217338 baseEnd_3217338 := by
    simpa [prefixWord, tailWord_3217338, baseEnd_3217338] using wordTrace_append hprefix tailTrace_3217338
  have hstable : (prefixWord ++ tailWord_3217338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217338).length < 2 ^ (prefixWord ++ tailWord_3217338).sum := by decide
  have hdescent : baseEnd_3217338 < baseStart_3217338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217353 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 7]
def baseStart_3217353 : Nat := 118140960795 + 3217353 * 2 ^ 59
def prefixEnd_3217353 : Nat := 4983230072969 + 3 ^ 40 * 3217353 * 2
def baseEnd_3217353 : Nat := 367121894263345738953593

theorem tailTrace_3217353 : CollatzResearch.WordTrace tailWord_3217353 prefixEnd_3217353 367121894263345738953593 := by
  unfold tailWord_3217353
  simp only [CollatzResearch.WordTrace]
  refine ⟨117346504313087035991160713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78231002875391357327440475 117346504313087035991160713)
  ·
    refine ⟨88009878234815276993370535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117346504313087035991160713 88009878234815276993370535)
    ·
      refine ⟨132014817352222915490055803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88009878234815276993370535 132014817352222915490055803)
      ·
        refine ⟨198022226028334373235083705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132014817352222915490055803 198022226028334373235083705)
        ·
          refine ⟨148516669521250779926312779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198022226028334373235083705 148516669521250779926312779)
          ·
            refine ⟨222775004281876169889469169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148516669521250779926312779 222775004281876169889469169)
            ·
              refine ⟨167081253211407127417101877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222775004281876169889469169 167081253211407127417101877)
              ·
                refine ⟨15663867488569418195353301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167081253211407127417101877 15663867488569418195353301)
                ·
                  refine ⟨367121894263345738953593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15663867488569418195353301 367121894263345738953593)
                  ·
                    rfl

theorem cell22_3217353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_3217353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217353 prefixEnd_3217353 := by exact prefixLift 3217353
  have htrace : WordTrace (prefixWord ++ tailWord_3217353) baseStart_3217353 baseEnd_3217353 := by
    simpa [prefixWord, tailWord_3217353, baseEnd_3217353] using wordTrace_append hprefix tailTrace_3217353
  have hstable : (prefixWord ++ tailWord_3217353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217353).length < 2 ^ (prefixWord ++ tailWord_3217353).sum := by decide
  have hdescent : baseEnd_3217353 < baseStart_3217353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217414 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3217414 : Nat := 118140960795 + 3217414 * 2 ^ 59
def prefixEnd_3217414 : Nat := 4983230072969 + 3 ^ 40 * 3217414 * 2
def baseEnd_3217414 : Nat := 1101386564336653391085593

theorem tailTrace_3217414 : CollatzResearch.WordTrace tailWord_3217414 prefixEnd_3217414 1101386564336653391085593 := by
  unfold tailWord_3217414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3667147786433313856535353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78232486110577362272754197 3667147786433313856535353)
  ·
    refine ⟨2750360839824985392401515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3667147786433313856535353 2750360839824985392401515)
    ·
      refine ⟨4125541259737478088602273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750360839824985392401515 4125541259737478088602273)
      ·
        refine ⟨3094155944803108566451705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4125541259737478088602273 3094155944803108566451705)
        ·
          refine ⟨2320616958602331424838779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3094155944803108566451705 2320616958602331424838779)
          ·
            refine ⟨3480925437903497137258169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320616958602331424838779 3480925437903497137258169)
            ·
              refine ⟨2610694078427622852943627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480925437903497137258169 2610694078427622852943627)
              ·
                refine ⟨3916041117641434279415441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610694078427622852943627 3916041117641434279415441)
                ·
                  refine ⟨2937030838231075709561581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3916041117641434279415441 2937030838231075709561581)
                  ·
                    refine ⟨1101386564336653391085593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937030838231075709561581 1101386564336653391085593)
                    ·
                      rfl

theorem cell22_3217414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3217414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217414 prefixEnd_3217414 := by exact prefixLift 3217414
  have htrace : WordTrace (prefixWord ++ tailWord_3217414) baseStart_3217414 baseEnd_3217414 := by
    simpa [prefixWord, tailWord_3217414, baseEnd_3217414] using wordTrace_append hprefix tailTrace_3217414
  have hstable : (prefixWord ++ tailWord_3217414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217414).length < 2 ^ (prefixWord ++ tailWord_3217414).sum := by decide
  have hdescent : baseEnd_3217414 < baseStart_3217414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217434 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_3217434 : Nat := 118140960795 + 3217434 * 2 ^ 59
def prefixEnd_3217434 : Nat := 4983230072969 + 3 ^ 40 * 3217434 * 2
def baseEnd_3217434 : Nat := 1101393410745380005585531

theorem tailTrace_3217434 : CollatzResearch.WordTrace tailWord_3217434 prefixEnd_3217434 1101393410745380005585531 := by
  unfold tailWord_3217434
  simp only [CollatzResearch.WordTrace]
  refine ⟨29337364656448396706214839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78232972417195724549906237 29337364656448396706214839)
  ·
    refine ⟨44006046984672595059322259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29337364656448396706214839 44006046984672595059322259)
    ·
      refine ⟨66009070477008892588983389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44006046984672595059322259 66009070477008892588983389)
      ·
        refine ⟨24753401428878334720868771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66009070477008892588983389 24753401428878334720868771)
        ·
          refine ⟨37130102143317502081303157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24753401428878334720868771 37130102143317502081303157)
          ·
            refine ⟨3480947075936015820122171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37130102143317502081303157 3480947075936015820122171)
            ·
              refine ⟨5221420613904023730183257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480947075936015820122171 5221420613904023730183257)
              ·
                refine ⟨3916065460428017797637443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5221420613904023730183257 3916065460428017797637443)
                ·
                  refine ⟨5874098190642026696456165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916065460428017797637443 5874098190642026696456165)
                  ·
                    refine ⟨1101393410745380005585531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874098190642026696456165 1101393410745380005585531)
                    ·
                      rfl

theorem cell22_3217434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_3217434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217434 prefixEnd_3217434 := by exact prefixLift 3217434
  have htrace : WordTrace (prefixWord ++ tailWord_3217434) baseStart_3217434 baseEnd_3217434 := by
    simpa [prefixWord, tailWord_3217434, baseEnd_3217434] using wordTrace_append hprefix tailTrace_3217434
  have hstable : (prefixWord ++ tailWord_3217434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217434).length < 2 ^ (prefixWord ++ tailWord_3217434).sum := by decide
  have hdescent : baseEnd_3217434 < baseStart_3217434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217502 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3217502 : Nat := 118140960795 + 3217502 * 2 ^ 59
def prefixEnd_3217502 : Nat := 4983230072969 + 3 ^ 40 * 3217502 * 2
def baseEnd_3217502 : Nat := 1101416688535050494885323

theorem tailTrace_3217502 : CollatzResearch.WordTrace tailWord_3217502 prefixEnd_3217502 1101416688535050494885323 := by
  unfold tailWord_3217502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668992348693404304791845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78234625859698156292223173 14668992348693404304791845)
  ·
    refine ⟨2750436065380013307148471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14668992348693404304791845 2750436065380013307148471)
    ·
      refine ⟨4125654098070019960722707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750436065380013307148471 4125654098070019960722707)
      ·
        refine ⟨6188481147105029941084061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4125654098070019960722707 6188481147105029941084061)
        ·
          refine ⟨2320680430164386227906523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6188481147105029941084061 2320680430164386227906523)
          ·
            refine ⟨3481020645246579341859785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320680430164386227906523 3481020645246579341859785)
            ·
              refine ⟨2610765483934934506394839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481020645246579341859785 2610765483934934506394839)
              ·
                refine ⟨3916148225902401759592259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610765483934934506394839 3916148225902401759592259)
                ·
                  refine ⟨5874222338853602639388389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916148225902401759592259 5874222338853602639388389)
                  ·
                    refine ⟨1101416688535050494885323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874222338853602639388389 1101416688535050494885323)
                    ·
                      rfl

theorem cell22_3217502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3217502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217502 prefixEnd_3217502 := by exact prefixLift 3217502
  have htrace : WordTrace (prefixWord ++ tailWord_3217502) baseStart_3217502 baseEnd_3217502 := by
    simpa [prefixWord, tailWord_3217502, baseEnd_3217502] using wordTrace_append hprefix tailTrace_3217502
  have hstable : (prefixWord ++ tailWord_3217502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217502).length < 2 ^ (prefixWord ++ tailWord_3217502).sum := by decide
  have hdescent : baseEnd_3217502 < baseStart_3217502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217505 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 7]
def baseStart_3217505 : Nat := 118140960795 + 3217505 * 2 ^ 59
def prefixEnd_3217505 : Nat := 4983230072969 + 3 ^ 40 * 3217505 * 2
def baseEnd_3217505 : Nat := 367139238498786495686771

theorem tailTrace_3217505 : CollatzResearch.WordTrace tailWord_3217505 prefixEnd_3217505 367139238498786495686771 := by
  unfold tailWord_3217505
  simp only [CollatzResearch.WordTrace]
  refine ⟨117352048208536365950693969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78234698805690910633795979 117352048208536365950693969)
  ·
    refine ⟨88014036156402274463020477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117352048208536365950693969 88014036156402274463020477)
    ·
      refine ⟨33005263558650852923632679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88014036156402274463020477 33005263558650852923632679)
      ·
        refine ⟨49507895337976279385449019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33005263558650852923632679 49507895337976279385449019)
        ·
          refine ⟨74261843006964419078173529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49507895337976279385449019 74261843006964419078173529)
          ·
            refine ⟨55696382255223314308630147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74261843006964419078173529 55696382255223314308630147)
            ·
              refine ⟨83544573382834971462945221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55696382255223314308630147 83544573382834971462945221)
              ·
                refine ⟨15664607509281557149302229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83544573382834971462945221 15664607509281557149302229)
                ·
                  refine ⟨367139238498786495686771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15664607509281557149302229 367139238498786495686771)
                  ·
                    rfl

theorem cell22_3217505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_3217505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217505 prefixEnd_3217505 := by exact prefixLift 3217505
  have htrace : WordTrace (prefixWord ++ tailWord_3217505) baseStart_3217505 baseEnd_3217505 := by
    simpa [prefixWord, tailWord_3217505, baseEnd_3217505] using wordTrace_append hprefix tailTrace_3217505
  have hstable : (prefixWord ++ tailWord_3217505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217505).length < 2 ^ (prefixWord ++ tailWord_3217505).sum := by decide
  have hdescent : baseEnd_3217505 < baseStart_3217505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217522 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_3217522 : Nat := 118140960795 + 3217522 * 2 ^ 59
def prefixEnd_3217522 : Nat := 4983230072969 + 3 ^ 40 * 3217522 * 2
def baseEnd_3217522 : Nat := 367141178314592369795087

theorem tailTrace_3217522 : CollatzResearch.WordTrace tailWord_3217522 prefixEnd_3217522 367141178314592369795087 := by
  unfold tailWord_3217522
  simp only [CollatzResearch.WordTrace]
  refine ⟨29338167062368694463515705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78235112166316518569375213 29338167062368694463515705)
  ·
    refine ⟨22003625296776520847636779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29338167062368694463515705 22003625296776520847636779)
    ·
      refine ⟨33005437945164781271455169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22003625296776520847636779 33005437945164781271455169)
      ·
        refine ⟨24754078458873585953591377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33005437945164781271455169 24754078458873585953591377)
        ·
          refine ⟨18565558844155189465193533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24754078458873585953591377 18565558844155189465193533)
          ·
            refine ⟨6962084566558196049447575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18565558844155189465193533 6962084566558196049447575)
            ·
              refine ⟨10443126849837294074171363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962084566558196049447575 10443126849837294074171363)
              ·
                refine ⟨15664690274755941111257045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10443126849837294074171363 15664690274755941111257045)
                ·
                  refine ⟨367141178314592369795087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15664690274755941111257045 367141178314592369795087)
                  ·
                    rfl

theorem cell22_3217522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_3217522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217522 prefixEnd_3217522 := by exact prefixLift 3217522
  have htrace : WordTrace (prefixWord ++ tailWord_3217522) baseStart_3217522 baseEnd_3217522 := by
    simpa [prefixWord, tailWord_3217522, baseEnd_3217522] using wordTrace_append hprefix tailTrace_3217522
  have hstable : (prefixWord ++ tailWord_3217522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217522).length < 2 ^ (prefixWord ++ tailWord_3217522).sum := by decide
  have hdescent : baseEnd_3217522 < baseStart_3217522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217526 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_3217526 : Nat := 118140960795 + 3217526 * 2 ^ 59
def prefixEnd_3217526 : Nat := 4983230072969 + 3 ^ 40 * 3217526 * 2
def baseEnd_3217526 : Nat := 1101424904225522432285249

theorem tailTrace_3217526 : CollatzResearch.WordTrace tailWord_3217526 prefixEnd_3217526 1101424904225522432285249 := by
  unfold tailWord_3217526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334550883841267908575527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78235209427640191024805621 7334550883841267908575527)
  ·
    refine ⟨11001826325761901862863291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7334550883841267908575527 11001826325761901862863291)
    ·
      refine ⟨16502739488642852794294937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11001826325761901862863291 16502739488642852794294937)
      ·
        refine ⟨12377054616482139595721203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16502739488642852794294937 12377054616482139595721203)
        ·
          refine ⟨18565581924723209393581805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12377054616482139595721203 18565581924723209393581805)
          ·
            refine ⟨6962093221771203522593177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18565581924723209393581805 6962093221771203522593177)
            ·
              refine ⟨5221569916328402641944883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6962093221771203522593177 5221569916328402641944883)
              ·
                refine ⟨7832354874492603962917325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221569916328402641944883 7832354874492603962917325)
                ·
                  refine ⟨2937133077934726486093997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7832354874492603962917325 2937133077934726486093997)
                  ·
                    refine ⟨1101424904225522432285249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937133077934726486093997 1101424904225522432285249)
                    ·
                      rfl

theorem cell22_3217526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_3217526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217526 prefixEnd_3217526 := by exact prefixLift 3217526
  have htrace : WordTrace (prefixWord ++ tailWord_3217526) baseStart_3217526 baseEnd_3217526 := by
    simpa [prefixWord, tailWord_3217526, baseEnd_3217526] using wordTrace_append hprefix tailTrace_3217526
  have hstable : (prefixWord ++ tailWord_3217526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217526).length < 2 ^ (prefixWord ++ tailWord_3217526).sum := by decide
  have hdescent : baseEnd_3217526 < baseStart_3217526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217539 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 5]
def baseStart_3217539 : Nat := 118140960795 + 3217539 * 2 ^ 59
def prefixEnd_3217539 : Nat := 4983230072969 + 3 ^ 40 * 3217539 * 2
def baseEnd_3217539 : Nat := 367143118130398243903403

theorem tailTrace_3217539 : CollatzResearch.WordTrace tailWord_3217539 prefixEnd_3217539 367143118130398243903403 := by
  unfold tailWord_3217539
  simp only [CollatzResearch.WordTrace]
  refine ⟨117353288290413189757431671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78235525526942126504954447 117353288290413189757431671)
  ·
    refine ⟨176029932435619784636147507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117353288290413189757431671 176029932435619784636147507)
    ·
      refine ⟨264044898653429676954221261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176029932435619784636147507 264044898653429676954221261)
      ·
        refine ⟨99016836995036128857832973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264044898653429676954221261 99016836995036128857832973)
        ·
          refine ⟨37131313873138548321687365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99016836995036128857832973 37131313873138548321687365)
          ·
            refine ⟨6962121351213477810316381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37131313873138548321687365 6962121351213477810316381)
            ·
              refine ⟨2610795506705054178868643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6962121351213477810316381 2610795506705054178868643)
              ·
                refine ⟨3916193260057581268302965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610795506705054178868643 3916193260057581268302965)
                ·
                  refine ⟨367143118130398243903403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3916193260057581268302965 367143118130398243903403)
                  ·
                    rfl

theorem cell22_3217539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 5].length) (baseStart_3217539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217539 prefixEnd_3217539 := by exact prefixLift 3217539
  have htrace : WordTrace (prefixWord ++ tailWord_3217539) baseStart_3217539 baseEnd_3217539 := by
    simpa [prefixWord, tailWord_3217539, baseEnd_3217539] using wordTrace_append hprefix tailTrace_3217539
  have hstable : (prefixWord ++ tailWord_3217539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217539).length < 2 ^ (prefixWord ++ tailWord_3217539).sum := by decide
  have hdescent : baseEnd_3217539 < baseStart_3217539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217560 : List Nat := [2, 1, 2, 4, 4, 1, 1, 3, 1, 3]
def baseStart_3217560 : Nat := 118140960795 + 3217560 * 2 ^ 59
def prefixEnd_3217560 : Nat := 4983230072969 + 3 ^ 40 * 3217560 * 2
def baseEnd_3217560 : Nat := 1101436543120357676935145

theorem tailTrace_3217560 : CollatzResearch.WordTrace tailWord_3217560 prefixEnd_3217560 1101436543120357676935145 := by
  unfold tailWord_3217560
  simp only [CollatzResearch.WordTrace]
  refine ⟨58677027111668555171973067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78236036148891406895964089 58677027111668555171973067)
  ·
    refine ⟨88015540667502832757959601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58677027111668555171973067 88015540667502832757959601)
    ·
      refine ⟨66011655500627124568469701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88015540667502832757959601 66011655500627124568469701)
      ·
        refine ⟨12377185406367585856588069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66011655500627124568469701 12377185406367585856588069)
        ·
          refine ⟨2320722263693922348110263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12377185406367585856588069 2320722263693922348110263)
          ·
            refine ⟨3481083395540883522165395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320722263693922348110263 3481083395540883522165395)
            ·
              refine ⟨5221625093311325283248093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481083395540883522165395 5221625093311325283248093)
              ·
                refine ⟨1958109409991746981218035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5221625093311325283248093 1958109409991746981218035)
                ·
                  refine ⟨2937164114987620471827053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958109409991746981218035 2937164114987620471827053)
                  ·
                    refine ⟨1101436543120357676935145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937164114987620471827053 1101436543120357676935145)
                    ·
                      rfl

theorem cell22_3217560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_3217560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217560 prefixEnd_3217560 := by exact prefixLift 3217560
  have htrace : WordTrace (prefixWord ++ tailWord_3217560) baseStart_3217560 baseEnd_3217560 := by
    simpa [prefixWord, tailWord_3217560, baseEnd_3217560] using wordTrace_append hprefix tailTrace_3217560
  have hstable : (prefixWord ++ tailWord_3217560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217560).length < 2 ^ (prefixWord ++ tailWord_3217560).sum := by decide
  have hdescent : baseEnd_3217560 < baseStart_3217560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217569 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3217569 : Nat := 118140960795 + 3217569 * 2 ^ 59
def prefixEnd_3217569 : Nat := 4983230072969 + 3 ^ 40 * 3217569 * 2
def baseEnd_3217569 : Nat := 1101439624004284653460117

theorem tailTrace_3217569 : CollatzResearch.WordTrace tailWord_3217569 prefixEnd_3217569 1101439624004284653460117 := by
  unfold tailWord_3217569
  simp only [CollatzResearch.WordTrace]
  refine ⟨117354382480304504881023761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78236254986869669920682507 117354382480304504881023761)
  ·
    refine ⟨88015786860228378660767821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117354382480304504881023761 88015786860228378660767821)
    ·
      refine ⟨33005920072585641997787933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88015786860228378660767821 33005920072585641997787933)
      ·
        refine ⟨12377220027219615749170475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33005920072585641997787933 12377220027219615749170475)
        ·
          refine ⟨18565830040829423623755713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12377220027219615749170475 18565830040829423623755713)
          ·
            refine ⟨13924372530622067717816785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18565830040829423623755713 13924372530622067717816785)
            ·
              refine ⟨10443279397966550788362589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13924372530622067717816785 10443279397966550788362589)
              ·
                refine ⟨3916229774237456545635971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10443279397966550788362589 3916229774237456545635971)
                ·
                  refine ⟨5874344661356184818453957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916229774237456545635971 5874344661356184818453957)
                  ·
                    refine ⟨1101439624004284653460117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874344661356184818453957 1101439624004284653460117)
                    ·
                      rfl

theorem cell22_3217569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3217569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217569 prefixEnd_3217569 := by exact prefixLift 3217569
  have htrace : WordTrace (prefixWord ++ tailWord_3217569) baseStart_3217569 baseEnd_3217569 := by
    simpa [prefixWord, tailWord_3217569, baseEnd_3217569] using wordTrace_append hprefix tailTrace_3217569
  have hstable : (prefixWord ++ tailWord_3217569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217569).length < 2 ^ (prefixWord ++ tailWord_3217569).sum := by decide
  have hdescent : baseEnd_3217569 < baseStart_3217569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217597 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_3217597 : Nat := 118140960795 + 3217597 * 2 ^ 59
def prefixEnd_3217597 : Nat := 4983230072969 + 3 ^ 40 * 3217597 * 2
def baseEnd_3217597 : Nat := 1101449208976501913760031

theorem tailTrace_3217597 : CollatzResearch.WordTrace tailWord_3217597 prefixEnd_3217597 1101449208976501913760031 := by
  unfold tailWord_3217597
  simp only [CollatzResearch.WordTrace]
  refine ⟨117355403724203065663043045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78236935816135377108695363 117355403724203065663043045)
  ·
    refine ⟨22004138198288074811820571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117355403724203065663043045 22004138198288074811820571)
    ·
      refine ⟨33006207297432112217730857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22004138198288074811820571 33006207297432112217730857)
      ·
        refine ⟨24754655473074084163298143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33006207297432112217730857 24754655473074084163298143)
        ·
          refine ⟨37131983209611126244947215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24754655473074084163298143 37131983209611126244947215)
          ·
            refine ⟨55697974814416689367420823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37131983209611126244947215 55697974814416689367420823)
            ·
              refine ⟨83546962221625034051131235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55697974814416689367420823 83546962221625034051131235)
              ·
                refine ⟨125320443332437551076696853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83546962221625034051131235 125320443332437551076696853)
                ·
                  refine ⟨5874395781208010206720165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125320443332437551076696853 5874395781208010206720165)
                  ·
                    refine ⟨1101449208976501913760031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874395781208010206720165 1101449208976501913760031)
                    ·
                      rfl

theorem cell22_3217597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_3217597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217597 prefixEnd_3217597 := by exact prefixLift 3217597
  have htrace : WordTrace (prefixWord ++ tailWord_3217597) baseStart_3217597 baseEnd_3217597 := by
    simpa [prefixWord, tailWord_3217597, baseEnd_3217597] using wordTrace_append hprefix tailTrace_3217597
  have hstable : (prefixWord ++ tailWord_3217597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217597).length < 2 ^ (prefixWord ++ tailWord_3217597).sum := by decide
  have hdescent : baseEnd_3217597 < baseStart_3217597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217614 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_3217614 : Nat := 118140960795 + 3217614 * 2 ^ 59
def prefixEnd_3217614 : Nat := 4983230072969 + 3 ^ 40 * 3217614 * 2
def baseEnd_3217614 : Nat := 1101455028423919536084979

theorem tailTrace_3217614 : CollatzResearch.WordTrace tailWord_3217614 prefixEnd_3217614 1101455028423919536084979 := by
  unfold tailWord_3217614
  simp only [CollatzResearch.WordTrace]
  refine ⟨14669502970642684695801487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78237349176760985044274597 14669502970642684695801487)
  ·
    refine ⟨22004254455964027043702231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14669502970642684695801487 22004254455964027043702231)
    ·
      refine ⟨33006381683946040565553347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22004254455964027043702231 33006381683946040565553347)
      ·
        refine ⟨49509572525919060848330021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33006381683946040565553347 49509572525919060848330021)
        ·
          refine ⟨9283044848609823909061879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49509572525919060848330021 9283044848609823909061879)
          ·
            refine ⟨13924567272914735863592819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9283044848609823909061879 13924567272914735863592819)
            ·
              refine ⟨20886850909372103795389229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13924567272914735863592819 20886850909372103795389229)
              ·
                refine ⟨7832569091014538923270961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20886850909372103795389229 7832569091014538923270961)
                ·
                  refine ⟨5874426818260904192453221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7832569091014538923270961 5874426818260904192453221)
                  ·
                    refine ⟨1101455028423919536084979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874426818260904192453221 1101455028423919536084979)
                    ·
                      rfl

theorem cell22_3217614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_3217614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217614 prefixEnd_3217614 := by exact prefixLift 3217614
  have htrace : WordTrace (prefixWord ++ tailWord_3217614) baseStart_3217614 baseEnd_3217614 := by
    simpa [prefixWord, tailWord_3217614, baseEnd_3217614] using wordTrace_append hprefix tailTrace_3217614
  have hstable : (prefixWord ++ tailWord_3217614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217614).length < 2 ^ (prefixWord ++ tailWord_3217614).sum := by decide
  have hdescent : baseEnd_3217614 < baseStart_3217614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217635 : List Nat := [1, 1, 1, 8, 1, 2, 2, 2, 4]
def baseStart_3217635 : Nat := 118140960795 + 3217635 * 2 ^ 59
def prefixEnd_3217635 : Nat := 4983230072969 + 3 ^ 40 * 3217635 * 2
def baseEnd_3217635 : Nat := 367154072384360827103305

theorem tailTrace_3217635 : CollatzResearch.WordTrace tailWord_3217635 prefixEnd_3217635 367154072384360827103305 := by
  unfold tailWord_3217635
  simp only [CollatzResearch.WordTrace]
  refine ⟨117356789698065398152926359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78237859798710265435284239 117356789698065398152926359)
  ·
    refine ⟨176035184547098097229389539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117356789698065398152926359 176035184547098097229389539)
    ·
      refine ⟨264052776820647145844084309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176035184547098097229389539 264052776820647145844084309)
      ·
        refine ⟨3094368478366958740360363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 264052776820647145844084309 3094368478366958740360363)
        ·
          refine ⟨4641552717550438110540545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094368478366958740360363 4641552717550438110540545)
          ·
            refine ⟨3481164538162828582905409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4641552717550438110540545 3481164538162828582905409)
            ·
              refine ⟨2610873403622121437179057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481164538162828582905409 2610873403622121437179057)
              ·
                refine ⟨1958155052716591077884293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2610873403622121437179057 1958155052716591077884293)
                ·
                  refine ⟨367154072384360827103305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958155052716591077884293 367154072384360827103305)
                  ·
                    rfl

theorem cell22_3217635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 4].length) (baseStart_3217635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217635 prefixEnd_3217635 := by exact prefixLift 3217635
  have htrace : WordTrace (prefixWord ++ tailWord_3217635) baseStart_3217635 baseEnd_3217635 := by
    simpa [prefixWord, tailWord_3217635, baseEnd_3217635] using wordTrace_append hprefix tailTrace_3217635
  have hstable : (prefixWord ++ tailWord_3217635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217635).length < 2 ^ (prefixWord ++ tailWord_3217635).sum := by decide
  have hdescent : baseEnd_3217635 < baseStart_3217635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217642 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_3217642 : Nat := 118140960795 + 3217642 * 2 ^ 59
def prefixEnd_3217642 : Nat := 4983230072969 + 3 ^ 40 * 3217642 * 2
def baseEnd_3217642 : Nat := 1101464613396136796384893

theorem tailTrace_3217642 : CollatzResearch.WordTrace tailWord_3217642 prefixEnd_3217642 1101464613396136796384893 := by
  unfold tailWord_3217642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29339261252260009587107795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78238030006026692232287453 29339261252260009587107795)
  ·
    refine ⟨44008891878390014380661693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29339261252260009587107795 44008891878390014380661693)
    ·
      refine ⟨16503334454396255392748135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44008891878390014380661693 16503334454396255392748135)
      ·
        refine ⟨24755001681594383089122203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16503334454396255392748135 24755001681594383089122203)
        ·
          refine ⟨37132502522391574633683305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24755001681594383089122203 37132502522391574633683305)
          ·
            refine ⟨27849376891793680975262479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37132502522391574633683305 27849376891793680975262479)
            ·
              refine ⟨41774065337690521462893719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27849376891793680975262479 41774065337690521462893719)
              ·
                refine ⟨62661098006535782194340579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41774065337690521462893719 62661098006535782194340579)
                ·
                  refine ⟨93991647009803673291510869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62661098006535782194340579 93991647009803673291510869)
                  ·
                    refine ⟨1101464613396136796384893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93991647009803673291510869 1101464613396136796384893)
                    ·
                      rfl

theorem cell22_3217642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_3217642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217642 prefixEnd_3217642 := by exact prefixLift 3217642
  have htrace : WordTrace (prefixWord ++ tailWord_3217642) baseStart_3217642 baseEnd_3217642 := by
    simpa [prefixWord, tailWord_3217642, baseEnd_3217642] using wordTrace_append hprefix tailTrace_3217642
  have hstable : (prefixWord ++ tailWord_3217642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217642).length < 2 ^ (prefixWord ++ tailWord_3217642).sum := by decide
  have hdescent : baseEnd_3217642 < baseStart_3217642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217644 : List Nat := [2, 2, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_3217644 : Nat := 118140960795 + 3217644 * 2 ^ 59
def prefixEnd_3217644 : Nat := 4983230072969 + 3 ^ 40 * 3217644 * 2
def baseEnd_3217644 : Nat := 1101465298037009457834887

theorem tailTrace_3217644 : CollatzResearch.WordTrace tailWord_3217644 prefixEnd_3217644 1101465298037009457834887 := by
  unfold tailWord_3217644
  simp only [CollatzResearch.WordTrace]
  refine ⟨58678558977516396345001993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78238078636688528460002657 58678558977516396345001993)
  ·
    refine ⟨44008919233137297258751495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58678558977516396345001993 44008919233137297258751495)
    ·
      refine ⟨66013378849705945888127243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44008919233137297258751495 66013378849705945888127243)
      ·
        refine ⟨99020068274558918832190865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66013378849705945888127243 99020068274558918832190865)
        ·
          refine ⟨74265051205919189124143149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99020068274558918832190865 74265051205919189124143149)
          ·
            refine ⟨27849394202219695921553681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74265051205919189124143149 27849394202219695921553681)
            ·
              refine ⟨20887045651664771941165261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27849394202219695921553681 20887045651664771941165261)
              ·
                refine ⟨7832642119374289477936973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20887045651664771941165261 7832642119374289477936973)
                ·
                  refine ⟨2937240794765358554226365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7832642119374289477936973 2937240794765358554226365)
                  ·
                    refine ⟨1101465298037009457834887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937240794765358554226365 1101465298037009457834887)
                    ·
                      rfl

theorem cell22_3217644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_3217644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217644 prefixEnd_3217644 := by exact prefixLift 3217644
  have htrace : WordTrace (prefixWord ++ tailWord_3217644) baseStart_3217644 baseEnd_3217644 := by
    simpa [prefixWord, tailWord_3217644, baseEnd_3217644] using wordTrace_append hprefix tailTrace_3217644
  have hstable : (prefixWord ++ tailWord_3217644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217644).length < 2 ^ (prefixWord ++ tailWord_3217644).sum := by decide
  have hdescent : baseEnd_3217644 < baseStart_3217644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217678 : List Nat := [4, 1, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_3217678 : Nat := 118140960795 + 3217678 * 2 ^ 59
def prefixEnd_3217678 : Nat := 4983230072969 + 3 ^ 40 * 3217678 * 2
def baseEnd_3217678 : Nat := 1101476936931844702484783

theorem tailTrace_3217678 : CollatzResearch.WordTrace tailWord_3217678 prefixEnd_3217678 1101476936931844702484783 := by
  unfold tailWord_3217678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14669794754613702062092711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78238905357939744331161125 14669794754613702062092711)
  ·
    refine ⟨22004692131920553093139067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14669794754613702062092711 22004692131920553093139067)
    ·
      refine ⟨33007038197880829639708601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22004692131920553093139067 33007038197880829639708601)
      ·
        refine ⟨24755278648410622229781451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33007038197880829639708601 24755278648410622229781451)
        ·
          refine ⟨37132917972615933344672177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24755278648410622229781451 37132917972615933344672177)
          ·
            refine ⟨27849688479461950008504133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37132917972615933344672177 27849688479461950008504133)
            ·
              refine ⟨5221816589899115626594525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27849688479461950008504133 5221816589899115626594525)
              ·
                refine ⟨1958181221212168359972947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5221816589899115626594525 1958181221212168359972947)
                ·
                  refine ⟨2937271831818252539959421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958181221212168359972947 2937271831818252539959421)
                  ·
                    refine ⟨1101476936931844702484783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937271831818252539959421 1101476936931844702484783)
                    ·
                      rfl

theorem cell22_3217678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_3217678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217678 prefixEnd_3217678 := by exact prefixLift 3217678
  have htrace : WordTrace (prefixWord ++ tailWord_3217678) baseStart_3217678 baseEnd_3217678 := by
    simpa [prefixWord, tailWord_3217678, baseEnd_3217678] using wordTrace_append hprefix tailTrace_3217678
  have hstable : (prefixWord ++ tailWord_3217678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217678).length < 2 ^ (prefixWord ++ tailWord_3217678).sum := by decide
  have hdescent : baseEnd_3217678 < baseStart_3217678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217721 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_3217721 : Nat := 118140960795 + 3217721 * 2 ^ 59
def prefixEnd_3217721 : Nat := 4983230072969 + 3 ^ 40 * 3217721 * 2
def baseEnd_3217721 : Nat := 1101491656710606923659651

theorem tailTrace_3217721 : CollatzResearch.WordTrace tailWord_3217721 prefixEnd_3217721 1101491656710606923659651 := by
  unfold tailWord_3217721
  simp only [CollatzResearch.WordTrace]
  refine ⟨117359926375753834840557017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78239950917169223227038011 117359926375753834840557017)
  ·
    refine ⟨88019944781815376130417763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117359926375753834840557017 88019944781815376130417763)
    ·
      refine ⟨132029917172723064195626645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88019944781815376130417763 132029917172723064195626645)
      ·
        refine ⟨6188902367471393634169999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 132029917172723064195626645 6188902367471393634169999)
        ·
          refine ⟨9283353551207090451254999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6188902367471393634169999 9283353551207090451254999)
          ·
            refine ⟨13925030326810635676882499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9283353551207090451254999 13925030326810635676882499)
            ·
              refine ⟨20887545490215953515323749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13925030326810635676882499 20887545490215953515323749)
              ·
                refine ⟨3916414779415491284123203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20887545490215953515323749 3916414779415491284123203)
                ·
                  refine ⟨5874622169123236926184805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916414779415491284123203 5874622169123236926184805)
                  ·
                    refine ⟨1101491656710606923659651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874622169123236926184805 1101491656710606923659651)
                    ·
                      rfl

theorem cell22_3217721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_3217721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217721 prefixEnd_3217721 := by exact prefixLift 3217721
  have htrace : WordTrace (prefixWord ++ tailWord_3217721) baseStart_3217721 baseEnd_3217721 := by
    simpa [prefixWord, tailWord_3217721, baseEnd_3217721] using wordTrace_append hprefix tailTrace_3217721
  have hstable : (prefixWord ++ tailWord_3217721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217721).length < 2 ^ (prefixWord ++ tailWord_3217721).sum := by decide
  have hdescent : baseEnd_3217721 < baseStart_3217721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217736 : List Nat := [2, 1, 3, 1, 1, 2, 5, 3, 4]
def baseStart_3217736 : Nat := 118140960795 + 3217736 * 2 ^ 59
def prefixEnd_3217736 : Nat := 4983230072969 + 3 ^ 40 * 3217736 * 2
def baseEnd_3217736 : Nat := 367165597172383961511535

theorem tailTrace_3217736 : CollatzResearch.WordTrace tailWord_3217736 prefixEnd_3217736 367165597172383961511535 := by
  unfold tailWord_3217736
  simp only [CollatzResearch.WordTrace]
  refine ⟨58680236735349746201176531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78240315647132994934902041 58680236735349746201176531)
  ·
    refine ⟨88020355103024619301764797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58680236735349746201176531 88020355103024619301764797)
    ·
      refine ⟨33007633163634232238161799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88020355103024619301764797 33007633163634232238161799)
      ·
        refine ⟨49511449745451348357242699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33007633163634232238161799 49511449745451348357242699)
        ·
          refine ⟨74267174618177022535864049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49511449745451348357242699 74267174618177022535864049)
          ·
            refine ⟨55700380963632766901898037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74267174618177022535864049 55700380963632766901898037)
            ·
              refine ⟨5221910715340571897052941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55700380963632766901898037 5221910715340571897052941)
              ·
                refine ⟨1958216518252714461394853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5221910715340571897052941 1958216518252714461394853)
                ·
                  refine ⟨367165597172383961511535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958216518252714461394853 367165597172383961511535)
                  ·
                    rfl

theorem cell22_3217736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 4].length) (baseStart_3217736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217736 prefixEnd_3217736 := by exact prefixLift 3217736
  have htrace : WordTrace (prefixWord ++ tailWord_3217736) baseStart_3217736 baseEnd_3217736 := by
    simpa [prefixWord, tailWord_3217736, baseEnd_3217736] using wordTrace_append hprefix tailTrace_3217736
  have hstable : (prefixWord ++ tailWord_3217736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217736).length < 2 ^ (prefixWord ++ tailWord_3217736).sum := by decide
  have hdescent : baseEnd_3217736 < baseStart_3217736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217751 : List Nat := [1, 1, 3, 2, 3, 1, 2, 4, 2, 3]
def baseStart_3217751 : Nat := 118140960795 + 3217751 * 2 ^ 59
def prefixEnd_3217751 : Nat := 4983230072969 + 3 ^ 40 * 3217751 * 2
def baseEnd_3217751 : Nat := 1101501926323696845409559

theorem tailTrace_3217751 : CollatzResearch.WordTrace tailWord_3217751 prefixEnd_3217751 1101501926323696845409559 := by
  unfold tailWord_3217751
  simp only [CollatzResearch.WordTrace]
  refine ⟨117361020565645149964149107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78240680377096766642766071 117361020565645149964149107)
  ·
    refine ⟨176041530848467724946223661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117361020565645149964149107 176041530848467724946223661)
    ·
      refine ⟨66015574068175396854833873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176041530848467724946223661 66015574068175396854833873)
      ·
        refine ⟨49511680551131547641125405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66015574068175396854833873 49511680551131547641125405)
        ·
          refine ⟨18566880206674330365422027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49511680551131547641125405 18566880206674330365422027)
          ·
            refine ⟨27850320310011495548133041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18566880206674330365422027 27850320310011495548133041)
            ·
              refine ⟨20887740232508621661099781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27850320310011495548133041 20887740232508621661099781)
              ·
                refine ⟨3916451293595366561456209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20887740232508621661099781 3916451293595366561456209)
                ·
                  refine ⟨2937338470196524921092157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3916451293595366561456209 2937338470196524921092157)
                  ·
                    refine ⟨1101501926323696845409559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937338470196524921092157 1101501926323696845409559)
                    ·
                      rfl

theorem cell22_3217751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_3217751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217751 prefixEnd_3217751 := by exact prefixLift 3217751
  have htrace : WordTrace (prefixWord ++ tailWord_3217751) baseStart_3217751 baseEnd_3217751 := by
    simpa [prefixWord, tailWord_3217751, baseEnd_3217751] using wordTrace_append hprefix tailTrace_3217751
  have hstable : (prefixWord ++ tailWord_3217751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217751).length < 2 ^ (prefixWord ++ tailWord_3217751).sum := by decide
  have hdescent : baseEnd_3217751 < baseStart_3217751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217764 : List Nat := [2, 3, 1, 1, 3, 1, 4, 7]
def baseStart_3217764 : Nat := 118140960795 + 3217764 * 2 ^ 59
def prefixEnd_3217764 : Nat := 4983230072969 + 3 ^ 40 * 3217764 * 2
def baseEnd_3217764 : Nat := 122389597387707682759391

theorem tailTrace_3217764 : CollatzResearch.WordTrace tailWord_3217764 prefixEnd_3217764 122389597387707682759391 := by
  unfold tailWord_3217764
  simp only [CollatzResearch.WordTrace]
  refine ⟨58680747357299026592186173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78240996476398702122914897 58680747357299026592186173)
  ·
    refine ⟨22005280258987134972069815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58680747357299026592186173 22005280258987134972069815)
    ·
      refine ⟨33007920388480702458104723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22005280258987134972069815 33007920388480702458104723)
      ·
        refine ⟨49511880582721053687157085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33007920388480702458104723 49511880582721053687157085)
        ·
          refine ⟨18566955218520395132683907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49511880582721053687157085 18566955218520395132683907)
          ·
            refine ⟨27850432827780592699025861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18566955218520395132683907 27850432827780592699025861)
            ·
              refine ⟨5221956155208861131067349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27850432827780592699025861 5221956155208861131067349)
              ·
                refine ⟨122389597387707682759391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5221956155208861131067349 122389597387707682759391)
                ·
                  rfl

theorem cell22_3217764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 7].length) (baseStart_3217764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217764 prefixEnd_3217764 := by exact prefixLift 3217764
  have htrace : WordTrace (prefixWord ++ tailWord_3217764) baseStart_3217764 baseEnd_3217764 := by
    simpa [prefixWord, tailWord_3217764, baseEnd_3217764] using wordTrace_append hprefix tailTrace_3217764
  have hstable : (prefixWord ++ tailWord_3217764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217764).length < 2 ^ (prefixWord ++ tailWord_3217764).sum := by decide
  have hdescent : baseEnd_3217764 < baseStart_3217764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217768 : List Nat := [2, 1, 4, 2, 2, 2, 1, 3, 2, 3]
def baseStart_3217768 : Nat := 118140960795 + 3217768 * 2 ^ 59
def prefixEnd_3217768 : Nat := 4983230072969 + 3 ^ 40 * 3217768 * 2
def baseEnd_3217768 : Nat := 1101507745771114467734507

theorem tailTrace_3217768 : CollatzResearch.WordTrace tailWord_3217768 prefixEnd_3217768 1101507745771114467734507 := by
  unfold tailWord_3217768
  simp only [CollatzResearch.WordTrace]
  refine ⟨58680820303291780933758979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78241093737722374578345305 58680820303291780933758979)
  ·
    refine ⟨88021230454937671400638469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58680820303291780933758979 88021230454937671400638469)
    ·
      refine ⟨16503980710300813387619713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88021230454937671400638469 16503980710300813387619713)
      ·
        refine ⟨12377985532725610040714785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16503980710300813387619713 12377985532725610040714785)
        ·
          refine ⟨9283489149544207530536089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12377985532725610040714785 9283489149544207530536089)
          ·
            refine ⟨6962616862158155647902067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9283489149544207530536089 6962616862158155647902067)
            ·
              refine ⟨10443925293237233471853101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962616862158155647902067 10443925293237233471853101)
              ·
                refine ⟨3916471984963962551944913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10443925293237233471853101 3916471984963962551944913)
                ·
                  refine ⟨2937353988722971913958685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3916471984963962551944913 2937353988722971913958685)
                  ·
                    refine ⟨1101507745771114467734507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937353988722971913958685 1101507745771114467734507)
                    ·
                      rfl

theorem cell22_3217768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_3217768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217768 prefixEnd_3217768 := by exact prefixLift 3217768
  have htrace : WordTrace (prefixWord ++ tailWord_3217768) baseStart_3217768 baseEnd_3217768 := by
    simpa [prefixWord, tailWord_3217768, baseEnd_3217768] using wordTrace_append hprefix tailTrace_3217768
  have hstable : (prefixWord ++ tailWord_3217768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217768).length < 2 ^ (prefixWord ++ tailWord_3217768).sum := by decide
  have hdescent : baseEnd_3217768 < baseStart_3217768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217824 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_3217824 : Nat := 118140960795 + 3217824 * 2 ^ 59
def prefixEnd_3217824 : Nat := 4983230072969 + 3 ^ 40 * 3217824 * 2
def baseEnd_3217824 : Nat := 1101526915715548988334335

theorem tailTrace_3217824 : CollatzResearch.WordTrace tailWord_3217824 prefixEnd_3217824 1101526915715548988334335 := by
  unfold tailWord_3217824
  simp only [CollatzResearch.WordTrace]
  refine ⟨58681841547190341715778263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78242455396253788954371017 58681841547190341715778263)
  ·
    refine ⟨88022762320785512573667395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58681841547190341715778263 88022762320785512573667395)
    ·
      refine ⟨132034143481178268860501093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88022762320785512573667395 132034143481178268860501093)
      ·
        refine ⟨24756401902720925411343955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132034143481178268860501093 24756401902720925411343955)
        ·
          refine ⟨37134602854081388117015933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24756401902720925411343955 37134602854081388117015933)
          ·
            refine ⟨13925476070280520543880975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37134602854081388117015933 13925476070280520543880975)
            ·
              refine ⟨20888214105420780815821463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13925476070280520543880975 20888214105420780815821463)
              ·
                refine ⟨31332321158131171223732195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20888214105420780815821463 31332321158131171223732195)
                ·
                  refine ⟨46998481737196756835598293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31332321158131171223732195 46998481737196756835598293)
                  ·
                    refine ⟨1101526915715548988334335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46998481737196756835598293 1101526915715548988334335)
                    ·
                      rfl

theorem cell22_3217824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_3217824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217824 prefixEnd_3217824 := by exact prefixLift 3217824
  have htrace : WordTrace (prefixWord ++ tailWord_3217824) baseStart_3217824 baseEnd_3217824 := by
    simpa [prefixWord, tailWord_3217824, baseEnd_3217824] using wordTrace_append hprefix tailTrace_3217824
  have hstable : (prefixWord ++ tailWord_3217824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217824).length < 2 ^ (prefixWord ++ tailWord_3217824).sum := by decide
  have hdescent : baseEnd_3217824 < baseStart_3217824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217826 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_3217826 : Nat := 118140960795 + 3217826 * 2 ^ 59
def prefixEnd_3217826 : Nat := 4983230072969 + 3 ^ 40 * 3217826 * 2
def baseEnd_3217826 : Nat := 367175866785473883261443

theorem tailTrace_3217826 : CollatzResearch.WordTrace tailWord_3217826 prefixEnd_3217826 367175866785473883261443 := by
  unfold tailWord_3217826
  simp only [CollatzResearch.WordTrace]
  refine ⟨29340939010093359443282333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78242504026915625182086221 29340939010093359443282333)
  ·
    refine ⟨11002852128785009791230875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29340939010093359443282333 11002852128785009791230875)
    ·
      refine ⟨16504278193177514686846313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11002852128785009791230875 16504278193177514686846313)
      ·
        refine ⟨12378208644883136015134735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16504278193177514686846313 12378208644883136015134735)
        ·
          refine ⟨18567312967324704022702103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378208644883136015134735 18567312967324704022702103)
          ·
            refine ⟨27850969450987056034053155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18567312967324704022702103 27850969450987056034053155)
            ·
              refine ⟨41776454176480584051079733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27850969450987056034053155 41776454176480584051079733)
              ·
                refine ⟨3916542579045054754788725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41776454176480584051079733 3916542579045054754788725)
                ·
                  refine ⟨367175866785473883261443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3916542579045054754788725 367175866785473883261443)
                  ·
                    rfl

theorem cell22_3217826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_3217826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217826 prefixEnd_3217826 := by exact prefixLift 3217826
  have htrace : WordTrace (prefixWord ++ tailWord_3217826) baseStart_3217826 baseEnd_3217826 := by
    simpa [prefixWord, tailWord_3217826, baseEnd_3217826] using wordTrace_append hprefix tailTrace_3217826
  have hstable : (prefixWord ++ tailWord_3217826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217826).length < 2 ^ (prefixWord ++ tailWord_3217826).sum := by decide
  have hdescent : baseEnd_3217826 < baseStart_3217826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217834 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3217834 : Nat := 118140960795 + 3217834 * 2 ^ 59
def prefixEnd_3217834 : Nat := 4983230072969 + 3 ^ 40 * 3217834 * 2
def baseEnd_3217834 : Nat := 1101530338919912295584305

theorem tailTrace_3217834 : CollatzResearch.WordTrace tailWord_3217834 prefixEnd_3217834 1101530338919912295584305 := by
  unfold tailWord_3217834
  simp only [CollatzResearch.WordTrace]
  refine ⟨29341011956086113784855139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78242698549562970092947037 29341011956086113784855139)
  ·
    refine ⟨44011517934129170677282709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29341011956086113784855139 44011517934129170677282709)
    ·
      refine ⟨2063039903162304875497627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44011517934129170677282709 2063039903162304875497627)
      ·
        refine ⟨3094559854743457313246441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063039903162304875497627 3094559854743457313246441)
        ·
          refine ⟨2320919891057592984934831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3094559854743457313246441 2320919891057592984934831)
          ·
            refine ⟨3481379836586389477402247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320919891057592984934831 3481379836586389477402247)
            ·
              refine ⟨5222069754879584216103371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481379836586389477402247 5222069754879584216103371)
              ·
                refine ⟨7833104632319376324155057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5222069754879584216103371 7833104632319376324155057)
                ·
                  refine ⟨5874828474239532243116293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7833104632319376324155057 5874828474239532243116293)
                  ·
                    refine ⟨1101530338919912295584305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874828474239532243116293 1101530338919912295584305)
                    ·
                      rfl

theorem cell22_3217834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3217834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217834 prefixEnd_3217834 := by exact prefixLift 3217834
  have htrace : WordTrace (prefixWord ++ tailWord_3217834) baseStart_3217834 baseEnd_3217834 := by
    simpa [prefixWord, tailWord_3217834, baseEnd_3217834] using wordTrace_append hprefix tailTrace_3217834
  have hstable : (prefixWord ++ tailWord_3217834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217834).length < 2 ^ (prefixWord ++ tailWord_3217834).sum := by decide
  have hdescent : baseEnd_3217834 < baseStart_3217834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217860 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 5]
def baseStart_3217860 : Nat := 118140960795 + 3217860 * 2 ^ 59
def prefixEnd_3217860 : Nat := 4983230072969 + 3 ^ 40 * 3217860 * 2
def baseEnd_3217860 : Nat := 367179746417085631478075

theorem tailTrace_3217860 : CollatzResearch.WordTrace tailWord_3217860 prefixEnd_3217860 367179746417085631478075 := by
  unfold tailWord_3217860
  simp only [CollatzResearch.WordTrace]
  refine ⟨58682498061125130789933517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78243330748166841053244689 58682498061125130789933517)
  ·
    refine ⟨22005936772921924046225069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58682498061125130789933517 22005936772921924046225069)
    ·
      refine ⟨8252226289845721517334401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22005936772921924046225069 8252226289845721517334401)
      ·
        refine ⟨6189169717384291138000801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8252226289845721517334401 6189169717384291138000801)
        ·
          refine ⟨4641877288038218353500601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6189169717384291138000801 4641877288038218353500601)
          ·
            refine ⟨3481407966028663765125451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4641877288038218353500601 3481407966028663765125451)
            ·
              refine ⟨5222111949042995647688177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481407966028663765125451 5222111949042995647688177)
              ·
                refine ⟨3916583961782246735766133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5222111949042995647688177 3916583961782246735766133)
                ·
                  refine ⟨367179746417085631478075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3916583961782246735766133 367179746417085631478075)
                  ·
                    rfl

theorem cell22_3217860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_3217860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217860 prefixEnd_3217860 := by exact prefixLift 3217860
  have htrace : WordTrace (prefixWord ++ tailWord_3217860) baseStart_3217860 baseEnd_3217860 := by
    simpa [prefixWord, tailWord_3217860, baseEnd_3217860] using wordTrace_append hprefix tailTrace_3217860
  have hstable : (prefixWord ++ tailWord_3217860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217860).length < 2 ^ (prefixWord ++ tailWord_3217860).sum := by decide
  have hdescent : baseEnd_3217860 < baseStart_3217860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217899 : List Nat := [1, 1, 1, 1, 2, 3, 5, 8]
def baseStart_3217899 : Nat := 118140960795 + 3217899 * 2 ^ 59
def prefixEnd_3217899 : Nat := 4983230072969 + 3 ^ 40 * 3217899 * 2
def baseEnd_3217899 : Nat := 122394732194252643634345

theorem tailTrace_3217899 : CollatzResearch.WordTrace tailWord_3217899 prefixEnd_3217899 122394732194252643634345 := by
  unfold tailWord_3217899
  simp only [CollatzResearch.WordTrace]
  refine ⟨117366418569108971240536751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78244279046072647493691167 117366418569108971240536751)
  ·
    refine ⟨176049627853663456860805127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117366418569108971240536751 176049627853663456860805127)
    ·
      refine ⟨264074441780495185291207691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176049627853663456860805127 264074441780495185291207691)
      ·
        refine ⟨396111662670742777936811537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264074441780495185291207691 396111662670742777936811537)
        ·
          refine ⟨297083747003057083452608653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396111662670742777936811537 297083747003057083452608653)
          ·
            refine ⟨111406405126146406294728245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297083747003057083452608653 111406405126146406294728245)
            ·
              refine ⟨10444350480576225590130773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111406405126146406294728245 10444350480576225590130773)
              ·
                refine ⟨122394732194252643634345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10444350480576225590130773 122394732194252643634345)
                ·
                  rfl

theorem cell22_3217899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 8].length) (baseStart_3217899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217899 prefixEnd_3217899 := by exact prefixLift 3217899
  have htrace : WordTrace (prefixWord ++ tailWord_3217899) baseStart_3217899 baseEnd_3217899 := by
    simpa [prefixWord, tailWord_3217899, baseEnd_3217899] using wordTrace_append hprefix tailTrace_3217899
  have hstable : (prefixWord ++ tailWord_3217899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217899).length < 2 ^ (prefixWord ++ tailWord_3217899).sum := by decide
  have hdescent : baseEnd_3217899 < baseStart_3217899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217922 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3217922 : Nat := 118140960795 + 3217922 * 2 ^ 59
def prefixEnd_3217922 : Nat := 4983230072969 + 3 ^ 40 * 3217922 * 2
def baseEnd_3217922 : Nat := 367186821039436466461345

theorem tailTrace_3217922 : CollatzResearch.WordTrace tailWord_3217922 prefixEnd_3217922 367186821039436466461345 := by
  unfold tailWord_3217922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29341814362006411542156005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78244838298683764112416013 29341814362006411542156005)
  ·
    refine ⟨5501590192876202164154251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29341814362006411542156005 5501590192876202164154251)
    ·
      refine ⟨8252385289314303246231377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5501590192876202164154251 8252385289314303246231377)
      ·
        refine ⟨6189288966985727434673533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8252385289314303246231377 6189288966985727434673533)
        ·
          refine ⟨2320983362619647788002575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6189288966985727434673533 2320983362619647788002575)
          ·
            refine ⟨3481475043929471682003863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320983362619647788002575 3481475043929471682003863)
            ·
              refine ⟨5222212565894207523005795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481475043929471682003863 5222212565894207523005795)
              ·
                refine ⟨7833318848841311284508693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5222212565894207523005795 7833318848841311284508693)
                ·
                  refine ⟨367186821039436466461345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7833318848841311284508693 367186821039436466461345)
                  ·
                    rfl

theorem cell22_3217922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3217922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217922 prefixEnd_3217922 := by exact prefixLift 3217922
  have htrace : WordTrace (prefixWord ++ tailWord_3217922) baseStart_3217922 baseEnd_3217922 := by
    simpa [prefixWord, tailWord_3217922, baseEnd_3217922] using wordTrace_append hprefix tailTrace_3217922
  have hstable : (prefixWord ++ tailWord_3217922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217922).length < 2 ^ (prefixWord ++ tailWord_3217922).sum := by decide
  have hdescent : baseEnd_3217922 < baseStart_3217922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217976 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_3217976 : Nat := 118140960795 + 3217976 * 2 ^ 59
def prefixEnd_3217976 : Nat := 4983230072969 + 3 ^ 40 * 3217976 * 2
def baseEnd_3217976 : Nat := 1101578948421871258533869

theorem tailTrace_3217976 : CollatzResearch.WordTrace tailWord_3217976 prefixEnd_3217976 1101578948421871258533869 := by
  unfold tailWord_3217976
  simp only [CollatzResearch.WordTrace]
  refine ⟨58684613494915006695544891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78246151326553342260726521 58684613494915006695544891)
  ·
    refine ⟨88026920242372510043317337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58684613494915006695544891 88026920242372510043317337)
    ·
      refine ⟨66020190181779382532488003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88026920242372510043317337 66020190181779382532488003)
      ·
        refine ⟨99030285272669073798732005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66020190181779382532488003 99030285272669073798732005)
        ·
          refine ⟨18568178488625451337262251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99030285272669073798732005 18568178488625451337262251)
          ·
            refine ⟨27852267732938177005893377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18568178488625451337262251 27852267732938177005893377)
            ·
              refine ⟨20889200799703632754420033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27852267732938177005893377 20889200799703632754420033)
              ·
                refine ⟨15666900599777724565815025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20889200799703632754420033 15666900599777724565815025)
                ·
                  refine ⟨11750175449833293424361269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15666900599777724565815025 11750175449833293424361269)
                  ·
                    refine ⟨1101578948421871258533869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11750175449833293424361269 1101578948421871258533869)
                    ·
                      rfl

theorem cell22_3217976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_3217976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217976 prefixEnd_3217976 := by exact prefixLift 3217976
  have htrace : WordTrace (prefixWord ++ tailWord_3217976) baseStart_3217976 baseEnd_3217976 := by
    simpa [prefixWord, tailWord_3217976, baseEnd_3217976] using wordTrace_append hprefix tailTrace_3217976
  have hstable : (prefixWord ++ tailWord_3217976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217976).length < 2 ^ (prefixWord ++ tailWord_3217976).sum := by decide
  have hdescent : baseEnd_3217976 < baseStart_3217976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3217978 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_3217978 : Nat := 118140960795 + 3217978 * 2 ^ 59
def prefixEnd_3217978 : Nat := 4983230072969 + 3 ^ 40 * 3217978 * 2
def baseEnd_3217978 : Nat := 367193211020914639994621

theorem tailTrace_3217978 : CollatzResearch.WordTrace tailWord_3217978 prefixEnd_3217978 367193211020914639994621 := by
  unfold tailWord_3217978
  simp only [CollatzResearch.WordTrace]
  refine ⟨29342324983955691933165647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78246199957215178488441725 29342324983955691933165647)
  ·
    refine ⟨44013487475933537899748471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29342324983955691933165647 44013487475933537899748471)
    ·
      refine ⟨66020231213900306849622707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44013487475933537899748471 66020231213900306849622707)
      ·
        refine ⟨99030346820850460274434061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66020231213900306849622707 99030346820850460274434061)
        ·
          refine ⟨37136380057818922602912773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99030346820850460274434061 37136380057818922602912773)
          ·
            refine ⟨6963071260841047988046145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37136380057818922602912773 6963071260841047988046145)
            ·
              refine ⟨5222303445630785991034609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6963071260841047988046145 5222303445630785991034609)
              ·
                refine ⟨3916727584223089493275957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5222303445630785991034609 3916727584223089493275957)
                ·
                  refine ⟨367193211020914639994621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3916727584223089493275957 367193211020914639994621)
                  ·
                    rfl

theorem cell22_3217978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_3217978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3217978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3217978 prefixEnd_3217978 := by exact prefixLift 3217978
  have htrace : WordTrace (prefixWord ++ tailWord_3217978) baseStart_3217978 baseEnd_3217978 := by
    simpa [prefixWord, tailWord_3217978, baseEnd_3217978] using wordTrace_append hprefix tailTrace_3217978
  have hstable : (prefixWord ++ tailWord_3217978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3217978).length < 2 ^ (prefixWord ++ tailWord_3217978).sum := by decide
  have hdescent : baseEnd_3217978 < baseStart_3217978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3217978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218074 : List Nat := [3, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_3218074 : Nat := 118140960795 + 3218074 * 2 ^ 59
def prefixEnd_3218074 : Nat := 4983230072969 + 3 ^ 40 * 3218074 * 2
def baseEnd_3218074 : Nat := 367204165274877223194523

theorem tailTrace_3218074 : CollatzResearch.WordTrace tailWord_3218074 prefixEnd_3218074 367204165274877223194523 := by
  unfold tailWord_3218074
  simp only [CollatzResearch.WordTrace]
  refine ⟨29343200335868744032039319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78248534228983317418771517 29343200335868744032039319)
  ·
    refine ⟨44014800503803116048058979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29343200335868744032039319 44014800503803116048058979)
    ·
      refine ⟨66022200755704674072088469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44014800503803116048058979 66022200755704674072088469)
      ·
        refine ⟨3094790660423656597129147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66022200755704674072088469 3094790660423656597129147)
        ·
          refine ⟨4642185990635484895693721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094790660423656597129147 4642185990635484895693721)
          ·
            refine ⟨3481639492976613671770291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4642185990635484895693721 3481639492976613671770291)
            ·
              refine ⟨5222459239464920507655437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481639492976613671770291 5222459239464920507655437)
              ·
                refine ⟨1958422214799345190370789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5222459239464920507655437 1958422214799345190370789)
                ·
                  refine ⟨367204165274877223194523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958422214799345190370789 367204165274877223194523)
                  ·
                    rfl

theorem cell22_3218074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_3218074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218074 prefixEnd_3218074 := by exact prefixLift 3218074
  have htrace : WordTrace (prefixWord ++ tailWord_3218074) baseStart_3218074 baseEnd_3218074 := by
    simpa [prefixWord, tailWord_3218074, baseEnd_3218074] using wordTrace_append hprefix tailTrace_3218074
  have hstable : (prefixWord ++ tailWord_3218074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218074).length < 2 ^ (prefixWord ++ tailWord_3218074).sum := by decide
  have hdescent : baseEnd_3218074 < baseStart_3218074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218087 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3218087 : Nat := 118140960795 + 3218087 * 2 ^ 59
def prefixEnd_3218087 : Nat := 4983230072969 + 3 ^ 40 * 3218087 * 2
def baseEnd_3218087 : Nat := 1101616945990303969008529

theorem tailTrace_3218087 : CollatzResearch.WordTrace tailWord_3218087 prefixEnd_3218087 1101616945990303969008529 := by
  unfold tailWord_3218087
  simp only [CollatzResearch.WordTrace]
  refine ⟨117373275492427879348380515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78248850328285252898920343 117373275492427879348380515)
  ·
    refine ⟨176059913238641819022570773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117373275492427879348380515 176059913238641819022570773)
    ·
      refine ⟨8252808433061335266683005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176059913238641819022570773 8252808433061335266683005)
      ·
        refine ⟨3094803162398000725006127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8252808433061335266683005 3094803162398000725006127)
        ·
          refine ⟨4642204743597001087509191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094803162398000725006127 4642204743597001087509191)
          ·
            refine ⟨6963307115395501631263787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4642204743597001087509191 6963307115395501631263787)
            ·
              refine ⟨10444960673093252446895681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963307115395501631263787 10444960673093252446895681)
              ·
                refine ⟨7833720504819939335171761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10444960673093252446895681 7833720504819939335171761)
                ·
                  refine ⟨5875290378614954501378821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7833720504819939335171761 5875290378614954501378821)
                  ·
                    refine ⟨1101616945990303969008529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5875290378614954501378821 1101616945990303969008529)
                    ·
                      rfl

theorem cell22_3218087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3218087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218087 prefixEnd_3218087 := by exact prefixLift 3218087
  have htrace : WordTrace (prefixWord ++ tailWord_3218087) baseStart_3218087 baseEnd_3218087 := by
    simpa [prefixWord, tailWord_3218087, baseEnd_3218087] using wordTrace_append hprefix tailTrace_3218087
  have hstable : (prefixWord ++ tailWord_3218087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218087).length < 2 ^ (prefixWord ++ tailWord_3218087).sum := by decide
  have hdescent : baseEnd_3218087 < baseStart_3218087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218102 : List Nat := [5, 1, 3, 1, 2, 1, 2, 7]
def baseStart_3218102 : Nat := 118140960795 + 3218102 * 2 ^ 59
def prefixEnd_3218102 : Nat := 4983230072969 + 3 ^ 40 * 3218102 * 2
def baseEnd_3218102 : Nat := 122402453421872103320387

theorem tailTrace_3218102 : CollatzResearch.WordTrace tailWord_3218102 prefixEnd_3218102 122402453421872103320387 := by
  unfold tailWord_3218102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7335863911710846056886035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78249215058249024606784373 7335863911710846056886035)
  ·
    refine ⟨11003795867566269085329053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7335863911710846056886035 11003795867566269085329053)
    ·
      refine ⟨4126423450337350906998395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11003795867566269085329053 4126423450337350906998395)
      ·
        refine ⟨6189635175506026360497593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4126423450337350906998395 6189635175506026360497593)
        ·
          refine ⟨4642226381629519770373195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6189635175506026360497593 4642226381629519770373195)
          ·
            refine ⟨6963339572444279655559793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4642226381629519770373195 6963339572444279655559793)
            ·
              refine ⟨5222504679333209741669845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6963339572444279655559793 5222504679333209741669845)
              ·
                refine ⟨122402453421872103320387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5222504679333209741669845 122402453421872103320387)
                ·
                  rfl

theorem cell22_3218102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_3218102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218102 prefixEnd_3218102 := by exact prefixLift 3218102
  have htrace : WordTrace (prefixWord ++ tailWord_3218102) baseStart_3218102 baseEnd_3218102 := by
    simpa [prefixWord, tailWord_3218102, baseEnd_3218102] using wordTrace_append hprefix tailTrace_3218102
  have hstable : (prefixWord ++ tailWord_3218102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218102).length < 2 ^ (prefixWord ++ tailWord_3218102).sum := by decide
  have hdescent : baseEnd_3218102 < baseStart_3218102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218190 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_3218190 : Nat := 118140960795 + 3218190 * 2 ^ 59
def prefixEnd_3218190 : Nat := 4983230072969 + 3 ^ 40 * 3218190 * 2
def baseEnd_3218190 : Nat := 1101652204995246033683213

theorem tailTrace_3218190 : CollatzResearch.WordTrace tailWord_3218190 prefixEnd_3218190 1101652204995246033683213 := by
  unfold tailWord_3218190
  simp only [CollatzResearch.WordTrace]
  refine ⟨14672129026381840992422503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78251354807369818626253349 14672129026381840992422503)
  ·
    refine ⟨22008193539572761488633755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14672129026381840992422503 22008193539572761488633755)
    ·
      refine ⟨33012290309359142232950633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22008193539572761488633755 33012290309359142232950633)
      ·
        refine ⟨24759217732019356674712975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33012290309359142232950633 24759217732019356674712975)
        ·
          refine ⟨37138826598029035012069463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24759217732019356674712975 37138826598029035012069463)
          ·
            refine ⟨55708239897043552518104195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37138826598029035012069463 55708239897043552518104195)
            ·
              refine ⟨83562359845565328777156293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55708239897043552518104195 83562359845565328777156293)
              ·
                refine ⟨15667942471043499145716805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83562359845565328777156293 15667942471043499145716805)
                ·
                  refine ⟨2937739213320656089821901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15667942471043499145716805 2937739213320656089821901)
                  ·
                    refine ⟨1101652204995246033683213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937739213320656089821901 1101652204995246033683213)
                    ·
                      rfl

theorem cell22_3218190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_3218190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218190 prefixEnd_3218190 := by exact prefixLift 3218190
  have htrace : WordTrace (prefixWord ++ tailWord_3218190) baseStart_3218190 baseEnd_3218190 := by
    simpa [prefixWord, tailWord_3218190, baseEnd_3218190] using wordTrace_append hprefix tailTrace_3218190
  have hstable : (prefixWord ++ tailWord_3218190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218190).length < 2 ^ (prefixWord ++ tailWord_3218190).sum := by decide
  have hdescent : baseEnd_3218190 < baseStart_3218190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218194 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3218194 : Nat := 118140960795 + 3218194 * 2 ^ 59
def prefixEnd_3218194 : Nat := 4983230072969 + 3 ^ 40 * 3218194 * 2
def baseEnd_3218194 : Nat := 1101653574276991356583201

theorem tailTrace_3218194 : CollatzResearch.WordTrace tailWord_3218194 prefixEnd_3218194 1101653574276991356583201 := by
  unfold tailWord_3218194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29344294525760059155631409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78251452068693491081683757 29344294525760059155631409)
  ·
    refine ⟨22008220894320044366723557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29344294525760059155631409 22008220894320044366723557)
    ·
      refine ⟨4126541417685008318760667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22008220894320044366723557 4126541417685008318760667)
      ·
        refine ⟨6189812126527512478141001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4126541417685008318760667 6189812126527512478141001)
        ·
          refine ⟨4642359094895634358605751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6189812126527512478141001 4642359094895634358605751)
          ·
            refine ⟨6963538642343451537908627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4642359094895634358605751 6963538642343451537908627)
            ·
              refine ⟨10445307963515177306862941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963538642343451537908627 10445307963515177306862941)
              ·
                refine ⟨3916990486318191490073603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10445307963515177306862941 3916990486318191490073603)
                ·
                  refine ⟨5875485729477287235110405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916990486318191490073603 5875485729477287235110405)
                  ·
                    refine ⟨1101653574276991356583201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5875485729477287235110405 1101653574276991356583201)
                    ·
                      rfl

theorem cell22_3218194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3218194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218194 prefixEnd_3218194 := by exact prefixLift 3218194
  have htrace : WordTrace (prefixWord ++ tailWord_3218194) baseStart_3218194 baseEnd_3218194 := by
    simpa [prefixWord, tailWord_3218194, baseEnd_3218194] using wordTrace_append hprefix tailTrace_3218194
  have hstable : (prefixWord ++ tailWord_3218194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218194).length < 2 ^ (prefixWord ++ tailWord_3218194).sum := by decide
  have hdescent : baseEnd_3218194 < baseStart_3218194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218207 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 2, 3]
def baseStart_3218207 : Nat := 118140960795 + 3218207 * 2 ^ 59
def prefixEnd_3218207 : Nat := 4983230072969 + 3 ^ 40 * 3218207 * 2
def baseEnd_3218207 : Nat := 1101658024442663656008161

theorem tailTrace_3218207 : CollatzResearch.WordTrace tailWord_3218207 prefixEnd_3218207 1101658024442663656008161 := by
  unfold tailWord_3218207
  simp only [CollatzResearch.WordTrace]
  refine ⟨117377652251993139842748875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78251768167995426561832583 117377652251993139842748875)
  ·
    refine ⟨176066478377989709764123313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117377652251993139842748875 176066478377989709764123313)
    ·
      refine ⟨132049858783492282323092485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176066478377989709764123313 132049858783492282323092485)
      ·
        refine ⟨24759348521904802935579841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132049858783492282323092485 24759348521904802935579841)
        ·
          refine ⟨18569511391428602201684881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24759348521904802935579841 18569511391428602201684881)
          ·
            refine ⟨13927133543571451651263661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18569511391428602201684881 13927133543571451651263661)
            ·
              refine ⟨5222675078839294369223873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13927133543571451651263661 5222675078839294369223873)
              ·
                refine ⟨3917006309129470776917905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5222675078839294369223873 3917006309129470776917905)
                ·
                  refine ⟨2937754731847103082688429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3917006309129470776917905 2937754731847103082688429)
                  ·
                    refine ⟨1101658024442663656008161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937754731847103082688429 1101658024442663656008161)
                    ·
                      rfl

theorem cell22_3218207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_3218207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218207 prefixEnd_3218207 := by exact prefixLift 3218207
  have htrace : WordTrace (prefixWord ++ tailWord_3218207) baseStart_3218207 baseEnd_3218207 := by
    simpa [prefixWord, tailWord_3218207, baseEnd_3218207] using wordTrace_append hprefix tailTrace_3218207
  have hstable : (prefixWord ++ tailWord_3218207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218207).length < 2 ^ (prefixWord ++ tailWord_3218207).sum := by decide
  have hdescent : baseEnd_3218207 < baseStart_3218207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218248 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 9]
def baseStart_3218248 : Nat := 118140960795 + 3218248 * 2 ^ 59
def prefixEnd_3218248 : Nat := 4983230072969 + 3 ^ 40 * 3218248 * 2
def baseEnd_3218248 : Nat := 367224019860184405244345

theorem tailTrace_3218248 : CollatzResearch.WordTrace tailWord_3218248 prefixEnd_3218248 367224019860184405244345 := by
  unfold tailWord_3218248
  simp only [CollatzResearch.WordTrace]
  refine ⟨58689573822422301922495699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78252765096563069229994265 58689573822422301922495699)
  ·
    refine ⟨88034360733633452883743549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58689573822422301922495699 88034360733633452883743549)
    ·
      refine ⟨33012885275112544831403831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88034360733633452883743549 33012885275112544831403831)
      ·
        refine ⟨49519327912668817247105747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33012885275112544831403831 49519327912668817247105747)
        ·
          refine ⟨74278991869003225870658621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49519327912668817247105747 74278991869003225870658621)
          ·
            refine ⟨27854621950876209701496983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74278991869003225870658621 27854621950876209701496983)
            ·
              refine ⟨41781932926314314552245475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27854621950876209701496983 41781932926314314552245475)
              ·
                refine ⟨62672899389471471828368213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41781932926314314552245475 62672899389471471828368213)
                ·
                  refine ⟨367224019860184405244345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62672899389471471828368213 367224019860184405244345)
                  ·
                    rfl

theorem cell22_3218248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_3218248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218248 prefixEnd_3218248 := by exact prefixLift 3218248
  have htrace : WordTrace (prefixWord ++ tailWord_3218248) baseStart_3218248 baseEnd_3218248 := by
    simpa [prefixWord, tailWord_3218248, baseEnd_3218248] using wordTrace_append hprefix tailTrace_3218248
  have hstable : (prefixWord ++ tailWord_3218248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218248).length < 2 ^ (prefixWord ++ tailWord_3218248).sum := by decide
  have hdescent : baseEnd_3218248 < baseStart_3218248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218327 : List Nat := [1, 1, 3, 3, 1, 2, 3, 4, 4]
def baseStart_3218327 : Nat := 118140960795 + 3218327 * 2 ^ 59
def prefixEnd_3218327 : Nat := 4983230072969 + 3 ^ 40 * 3218327 * 2
def baseEnd_3218327 : Nat := 367233034298341114335931

theorem tailTrace_3218327 : CollatzResearch.WordTrace tailWord_3218327 prefixEnd_3218327 367233034298341114335931 := by
  unfold tailWord_3218327
  simp only [CollatzResearch.WordTrace]
  refine ⟨117382029011558400337117235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78254686007705600224744823 117382029011558400337117235)
  ·
    refine ⟨176073043517337600505675853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117382029011558400337117235 176073043517337600505675853)
    ·
      refine ⟨66027391319001600189628445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176073043517337600505675853 66027391319001600189628445)
      ·
        refine ⟨24760271744625600071110667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66027391319001600189628445 24760271744625600071110667)
        ·
          refine ⟨37140407616938400106666001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24760271744625600071110667 37140407616938400106666001)
          ·
            refine ⟨27855305712703800079999501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37140407616938400106666001 27855305712703800079999501)
            ·
              refine ⟨10445739642263925029999813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27855305712703800079999501 10445739642263925029999813)
              ·
                refine ⟨1958576182924485943124965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10445739642263925029999813 1958576182924485943124965)
                ·
                  refine ⟨367233034298341114335931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958576182924485943124965 367233034298341114335931)
                  ·
                    rfl

theorem cell22_3218327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 4].length) (baseStart_3218327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218327 prefixEnd_3218327 := by exact prefixLift 3218327
  have htrace : WordTrace (prefixWord ++ tailWord_3218327) baseStart_3218327 baseEnd_3218327 := by
    simpa [prefixWord, tailWord_3218327, baseEnd_3218327] using wordTrace_append hprefix tailTrace_3218327
  have hstable : (prefixWord ++ tailWord_3218327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218327).length < 2 ^ (prefixWord ++ tailWord_3218327).sum := by decide
  have hdescent : baseEnd_3218327 < baseStart_3218327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218340 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_3218340 : Nat := 118140960795 + 3218340 * 2 ^ 59
def prefixEnd_3218340 : Nat := 4983230072969 + 3 ^ 40 * 3218340 * 2
def baseEnd_3218340 : Nat := 1101703553060695642432753

theorem tailTrace_3218340 : CollatzResearch.WordTrace tailWord_3218340 prefixEnd_3218340 1101703553060695642432753 := by
  unfold tailWord_3218340
  simp only [CollatzResearch.WordTrace]
  refine ⟨58691251580255651778670237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78255002107007535704893649 58691251580255651778670237)
  ·
    refine ⟨22009219342595869417001339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58691251580255651778670237 22009219342595869417001339)
    ·
      refine ⟨33013829013893804125502009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22009219342595869417001339 33013829013893804125502009)
      ·
        refine ⟨24760371760420353094126507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33013829013893804125502009 24760371760420353094126507)
        ·
          refine ⟨37140557640630529641189761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24760371760420353094126507 37140557640630529641189761)
          ·
            refine ⟨27855418230472897230892321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37140557640630529641189761 27855418230472897230892321)
            ·
              refine ⟨20891563672854672923169241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27855418230472897230892321 20891563672854672923169241)
              ·
                refine ⟨15668672754641004692376931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20891563672854672923169241 15668672754641004692376931)
                ·
                  refine ⟨23503009131961507038565397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15668672754641004692376931 23503009131961507038565397)
                  ·
                    refine ⟨1101703553060695642432753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23503009131961507038565397 1101703553060695642432753)
                    ·
                      rfl

theorem cell22_3218340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_3218340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218340 prefixEnd_3218340 := by exact prefixLift 3218340
  have htrace : WordTrace (prefixWord ++ tailWord_3218340) baseStart_3218340 baseEnd_3218340 := by
    simpa [prefixWord, tailWord_3218340, baseEnd_3218340] using wordTrace_append hprefix tailTrace_3218340
  have hstable : (prefixWord ++ tailWord_3218340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218340).length < 2 ^ (prefixWord ++ tailWord_3218340).sum := by decide
  have hdescent : baseEnd_3218340 < baseStart_3218340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218376 : List Nat := [2, 1, 3, 1, 5, 2, 1, 2, 2, 3]
def baseStart_3218376 : Nat := 118140960795 + 3218376 * 2 ^ 59
def prefixEnd_3218376 : Nat := 4983230072969 + 3 ^ 40 * 3218376 * 2
def baseEnd_3218376 : Nat := 1101715876596403548532643

theorem tailTrace_3218376 : CollatzResearch.WordTrace tailWord_3218376 prefixEnd_3218376 1101715876596403548532643 := by
  unfold tailWord_3218376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58691908094190440852825491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78255877458920587803767321 58691908094190440852825491)
  ·
    refine ⟨88037862141285661279238237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58691908094190440852825491 88037862141285661279238237)
    ·
      refine ⟨33014198302982122979714339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88037862141285661279238237 33014198302982122979714339)
      ·
        refine ⟨49521297454473184469571509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33014198302982122979714339 49521297454473184469571509)
        ·
          refine ⟨4642621636356861044022329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49521297454473184469571509 4642621636356861044022329)
          ·
            refine ⟨3481966227267645783016747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4642621636356861044022329 3481966227267645783016747)
            ·
              refine ⟨5222949340901468674525121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481966227267645783016747 5222949340901468674525121)
              ·
                refine ⟨3917212005676101505893841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5222949340901468674525121 3917212005676101505893841)
                ·
                  refine ⟨2937909004257076129420381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3917212005676101505893841 2937909004257076129420381)
                  ·
                    refine ⟨1101715876596403548532643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937909004257076129420381 1101715876596403548532643)
                    ·
                      rfl

theorem cell22_3218376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_3218376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218376 prefixEnd_3218376 := by exact prefixLift 3218376
  have htrace : WordTrace (prefixWord ++ tailWord_3218376) baseStart_3218376 baseEnd_3218376 := by
    simpa [prefixWord, tailWord_3218376, baseEnd_3218376] using wordTrace_append hprefix tailTrace_3218376
  have hstable : (prefixWord ++ tailWord_3218376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218376).length < 2 ^ (prefixWord ++ tailWord_3218376).sum := by decide
  have hdescent : baseEnd_3218376 < baseStart_3218376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218524 : List Nat := [2, 2, 4, 1, 1, 1, 5, 6]
def baseStart_3218524 : Nat := 118140960795 + 3218524 * 2 ^ 59
def prefixEnd_3218524 : Nat := 4983230072969 + 3 ^ 40 * 3218524 * 2
def baseEnd_3218524 : Nat := 122418504446775610648021

theorem tailTrace_3218524 : CollatzResearch.WordTrace tailWord_3218524 prefixEnd_3218524 122418504446775610648021 := by
  unfold tailWord_3218524
  simp only [CollatzResearch.WordTrace]
  refine ⟨58694607095922351491019313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78259476127896468654692417 58694607095922351491019313)
  ·
    refine ⟨44020955321941763618264485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58694607095922351491019313 44020955321941763618264485)
    ·
      refine ⟨8253929122864080678424591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44020955321941763618264485 8253929122864080678424591)
      ·
        refine ⟨12380893684296121017636887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8253929122864080678424591 12380893684296121017636887)
        ·
          refine ⟨18571340526444181526455331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12380893684296121017636887 18571340526444181526455331)
          ·
            refine ⟨27857010789666272289682997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18571340526444181526455331 27857010789666272289682997)
            ·
              refine ⟨2611594761531213027157781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27857010789666272289682997 2611594761531213027157781)
              ·
                refine ⟨122418504446775610648021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2611594761531213027157781 122418504446775610648021)
                ·
                  rfl

theorem cell22_3218524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 6].length) (baseStart_3218524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218524 prefixEnd_3218524 := by exact prefixLift 3218524
  have htrace : WordTrace (prefixWord ++ tailWord_3218524) baseStart_3218524 baseEnd_3218524 := by
    simpa [prefixWord, tailWord_3218524, baseEnd_3218524] using wordTrace_append hprefix tailTrace_3218524
  have hstable : (prefixWord ++ tailWord_3218524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218524).length < 2 ^ (prefixWord ++ tailWord_3218524).sum := by decide
  have hdescent : baseEnd_3218524 < baseStart_3218524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218556 : List Nat := [2, 2, 2, 1, 1, 3, 1, 6, 1, 3]
def baseStart_3218556 : Nat := 118140960795 + 3218556 * 2 ^ 59
def prefixEnd_3218556 : Nat := 4983230072969 + 3 ^ 40 * 3218556 * 2
def baseEnd_3218556 : Nat := 1101777494274943079032091

theorem tailTrace_3218556 : CollatzResearch.WordTrace tailWord_3218556 prefixEnd_3218556 1101777494274943079032091 := by
  unfold tailWord_3218556
  simp only [CollatzResearch.WordTrace]
  refine ⟨58695190663864386223601761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78260254218485848298135681 58695190663864386223601761)
  ·
    refine ⟨44021392997898289667701321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58695190663864386223601761 44021392997898289667701321)
    ·
      refine ⟨33016044748423717250775991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44021392997898289667701321 33016044748423717250775991)
      ·
        refine ⟨49524067122635575876163987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33016044748423717250775991 49524067122635575876163987)
        ·
          refine ⟨74286100683953363814245981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49524067122635575876163987 74286100683953363814245981)
          ·
            refine ⟨27857287756482511430342243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74286100683953363814245981 27857287756482511430342243)
            ·
              refine ⟨41785931634723767145513365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27857287756482511430342243 41785931634723767145513365)
              ·
                refine ⟨1958715545377676584945939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41785931634723767145513365 1958715545377676584945939)
                ·
                  refine ⟨2938073318066514877418909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958715545377676584945939 2938073318066514877418909)
                  ·
                    refine ⟨1101777494274943079032091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938073318066514877418909 1101777494274943079032091)
                    ·
                      rfl

theorem cell22_3218556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_3218556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218556 prefixEnd_3218556 := by exact prefixLift 3218556
  have htrace : WordTrace (prefixWord ++ tailWord_3218556) baseStart_3218556 baseEnd_3218556 := by
    simpa [prefixWord, tailWord_3218556, baseEnd_3218556] using wordTrace_append hprefix tailTrace_3218556
  have hstable : (prefixWord ++ tailWord_3218556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218556).length < 2 ^ (prefixWord ++ tailWord_3218556).sum := by decide
  have hdescent : baseEnd_3218556 < baseStart_3218556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218590 : List Nat := [4, 3, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3218590 : Nat := 118140960795 + 3218590 * 2 ^ 59
def prefixEnd_3218590 : Nat := 4983230072969 + 3 ^ 40 * 3218590 * 2
def baseEnd_3218590 : Nat := 1101789133169778323681987

theorem tailTrace_3218590 : CollatzResearch.WordTrace tailWord_3218590 prefixEnd_3218590 1101789133169778323681987 := by
  unfold tailWord_3218590
  simp only [CollatzResearch.WordTrace]
  refine ⟨14673952676200699531742653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78261080939737064169294149 14673952676200699531742653)
  ·
    refine ⟨5502732253575262324403495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14673952676200699531742653 5502732253575262324403495)
    ·
      refine ⟨8254098380362893486605243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5502732253575262324403495 8254098380362893486605243)
      ·
        refine ⟨12381147570544340229907865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8254098380362893486605243 12381147570544340229907865)
        ·
          refine ⟨9285860677908255172430899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12381147570544340229907865 9285860677908255172430899)
          ·
            refine ⟨13928791016862382758646349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9285860677908255172430899 13928791016862382758646349)
            ·
              refine ⟨5223296631323393534492381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13928791016862382758646349 5223296631323393534492381)
              ·
                refine ⟨1958736236746272575434643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5223296631323393534492381 1958736236746272575434643)
                ·
                  refine ⟨2938104355119408863151965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958736236746272575434643 2938104355119408863151965)
                  ·
                    refine ⟨1101789133169778323681987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938104355119408863151965 1101789133169778323681987)
                    ·
                      rfl

theorem cell22_3218590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3218590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218590 prefixEnd_3218590 := by exact prefixLift 3218590
  have htrace : WordTrace (prefixWord ++ tailWord_3218590) baseStart_3218590 baseEnd_3218590 := by
    simpa [prefixWord, tailWord_3218590, baseEnd_3218590] using wordTrace_append hprefix tailTrace_3218590
  have hstable : (prefixWord ++ tailWord_3218590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218590).length < 2 ^ (prefixWord ++ tailWord_3218590).sum := by decide
  have hdescent : baseEnd_3218590 < baseStart_3218590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218627 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 1, 6]
def baseStart_3218627 : Nat := 118140960795 + 3218627 * 2 ^ 59
def prefixEnd_3218627 : Nat := 4983230072969 + 3 ^ 40 * 3218627 * 2
def baseEnd_3218627 : Nat := 1101801799025922560506873

theorem tailTrace_3218627 : CollatzResearch.WordTrace tailWord_3218627 prefixEnd_3218627 1101801799025922560506873 := by
  unfold tailWord_3218627
  simp only [CollatzResearch.WordTrace]
  refine ⟨117392970910471551573038135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78261980606981034382025423 117392970910471551573038135)
  ·
    refine ⟨176089456365707327359557203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117392970910471551573038135 176089456365707327359557203)
    ·
      refine ⟨264134184548560991039335805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176089456365707327359557203 264134184548560991039335805)
      ·
        refine ⟨99050319205710371639750927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264134184548560991039335805 99050319205710371639750927)
        ·
          refine ⟨148575478808565557459626391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99050319205710371639750927 148575478808565557459626391)
          ·
            refine ⟨222863218212848336189439587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148575478808565557459626391 222863218212848336189439587)
            ·
              refine ⟨334294827319272504284159381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222863218212848336189439587 334294827319272504284159381)
              ·
                refine ⟨15670070030590898638319971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 334294827319272504284159381 15670070030590898638319971)
                ·
                  refine ⟨23505105045886347957479957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15670070030590898638319971 23505105045886347957479957)
                  ·
                    refine ⟨1101801799025922560506873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23505105045886347957479957 1101801799025922560506873)
                    ·
                      rfl

theorem cell22_3218627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_3218627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218627 prefixEnd_3218627 := by exact prefixLift 3218627
  have htrace : WordTrace (prefixWord ++ tailWord_3218627) baseStart_3218627 baseEnd_3218627 := by
    simpa [prefixWord, tailWord_3218627, baseEnd_3218627] using wordTrace_append hprefix tailTrace_3218627
  have hstable : (prefixWord ++ tailWord_3218627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218627).length < 2 ^ (prefixWord ++ tailWord_3218627).sum := by decide
  have hdescent : baseEnd_3218627 < baseStart_3218627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218691 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 3, 3]
def baseStart_3218691 : Nat := 118140960795 + 3218691 * 2 ^ 59
def prefixEnd_3218691 : Nat := 4983230072969 + 3 ^ 40 * 3218691 * 2
def baseEnd_3218691 : Nat := 1101823707533847726906677

theorem tailTrace_3218691 : CollatzResearch.WordTrace tailWord_3218691 prefixEnd_3218691 1101823707533847726906677 := by
  unfold tailWord_3218691
  simp only [CollatzResearch.WordTrace]
  refine ⟨117395305182239690503367927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78263536788159793668911951 117395305182239690503367927)
  ·
    refine ⟨176092957773359535755051891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117395305182239690503367927 176092957773359535755051891)
    ·
      refine ⟨264139436660039303632577837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176092957773359535755051891 264139436660039303632577837)
      ·
        refine ⟨99052288747514738862216689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264139436660039303632577837 99052288747514738862216689)
        ·
          refine ⟨74289216560636054146662517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99052288747514738862216689 74289216560636054146662517)
          ·
            refine ⟨6964614052559630076249611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74289216560636054146662517 6964614052559630076249611)
            ·
              refine ⟨10446921078839445114374417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964614052559630076249611 10446921078839445114374417)
              ·
                refine ⟨7835190809129583835780813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10446921078839445114374417 7835190809129583835780813)
                ·
                  refine ⟨2938196553423593938417805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7835190809129583835780813 2938196553423593938417805)
                  ·
                    refine ⟨1101823707533847726906677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938196553423593938417805 1101823707533847726906677)
                    ·
                      rfl

theorem cell22_3218691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 3].length) (baseStart_3218691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218691 prefixEnd_3218691 := by exact prefixLift 3218691
  have htrace : WordTrace (prefixWord ++ tailWord_3218691) baseStart_3218691 baseEnd_3218691 := by
    simpa [prefixWord, tailWord_3218691, baseEnd_3218691] using wordTrace_append hprefix tailTrace_3218691
  have hstable : (prefixWord ++ tailWord_3218691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218691).length < 2 ^ (prefixWord ++ tailWord_3218691).sum := by decide
  have hdescent : baseEnd_3218691 < baseStart_3218691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218738 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_3218738 : Nat := 118140960795 + 3218738 * 2 ^ 59
def prefixEnd_3218738 : Nat := 4983230072969 + 3 ^ 40 * 3218738 * 2
def baseEnd_3218738 : Nat := 367279932198118423660511

theorem tailTrace_3218738 : CollatzResearch.WordTrace tailWord_3218738 prefixEnd_3218738 367279932198118423660511 := by
  unfold tailWord_3218738
  simp only [CollatzResearch.WordTrace]
  refine ⟨29349254853267354382582217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78264679608712945020219245 29349254853267354382582217)
  ·
    refine ⟨22011941139950515786936663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29349254853267354382582217 22011941139950515786936663)
    ·
      refine ⟨33017911709925773680404995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22011941139950515786936663 33017911709925773680404995)
      ·
        refine ⟨49526867564888660520607493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33017911709925773680404995 49526867564888660520607493)
        ·
          refine ⟨9286287668416623847613905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49526867564888660520607493 9286287668416623847613905)
          ·
            refine ⟨6964715751312467885710429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9286287668416623847613905 6964715751312467885710429)
            ·
              refine ⟨2611768406742175457141411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6964715751312467885710429 2611768406742175457141411)
              ·
                refine ⟨3917652610113263185712117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611768406742175457141411 3917652610113263185712117)
                ·
                  refine ⟨367279932198118423660511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3917652610113263185712117 367279932198118423660511)
                  ·
                    rfl

theorem cell22_3218738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_3218738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218738 prefixEnd_3218738 := by exact prefixLift 3218738
  have htrace : WordTrace (prefixWord ++ tailWord_3218738) baseStart_3218738 baseEnd_3218738 := by
    simpa [prefixWord, tailWord_3218738, baseEnd_3218738] using wordTrace_append hprefix tailTrace_3218738
  have hstable : (prefixWord ++ tailWord_3218738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218738).length < 2 ^ (prefixWord ++ tailWord_3218738).sum := by decide
  have hdescent : baseEnd_3218738 < baseStart_3218738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218751 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 1, 4]
def baseStart_3218751 : Nat := 118140960795 + 3218751 * 2 ^ 59
def prefixEnd_3218751 : Nat := 4983230072969 + 3 ^ 40 * 3218751 * 2
def baseEnd_3218751 : Nat := 1101844246760027570406493

theorem tailTrace_3218751 : CollatzResearch.WordTrace tailWord_3218751 prefixEnd_3218751 1101844246760027570406493 := by
  unfold tailWord_3218751
  simp only [CollatzResearch.WordTrace]
  refine ⟨117397493562022320750552107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78264995708014880500368071 117397493562022320750552107)
  ·
    refine ⟨176096240343033481125828161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117397493562022320750552107 176096240343033481125828161)
    ·
      refine ⟨132072180257275110844371121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176096240343033481125828161 132072180257275110844371121)
      ·
        refine ⟨99054135192956333133278341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132072180257275110844371121 99054135192956333133278341)
        ·
          refine ⟨18572650348679312462489689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99054135192956333133278341 18572650348679312462489689)
          ·
            refine ⟨13929487761509484346867267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18572650348679312462489689 13929487761509484346867267)
            ·
              refine ⟨20894231642264226520300901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13929487761509484346867267 20894231642264226520300901)
              ·
                refine ⟨3917668432924542472556419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20894231642264226520300901 3917668432924542472556419)
                ·
                  refine ⟨5876502649386813708834629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3917668432924542472556419 5876502649386813708834629)
                  ·
                    refine ⟨1101844246760027570406493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5876502649386813708834629 1101844246760027570406493)
                    ·
                      rfl

theorem cell22_3218751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_3218751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218751 prefixEnd_3218751 := by exact prefixLift 3218751
  have htrace : WordTrace (prefixWord ++ tailWord_3218751) baseStart_3218751 baseEnd_3218751 := by
    simpa [prefixWord, tailWord_3218751, baseEnd_3218751] using wordTrace_append hprefix tailTrace_3218751
  have hstable : (prefixWord ++ tailWord_3218751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218751).length < 2 ^ (prefixWord ++ tailWord_3218751).sum := by decide
  have hdescent : baseEnd_3218751 < baseStart_3218751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218809 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_3218809 : Nat := 118140960795 + 3218809 * 2 ^ 59
def prefixEnd_3218809 : Nat := 4983230072969 + 3 ^ 40 * 3218809 * 2
def baseEnd_3218809 : Nat := 1101864101345334752456315

theorem tailTrace_3218809 : CollatzResearch.WordTrace tailWord_3218809 prefixEnd_3218809 1101864101345334752456315 := by
  unfold tailWord_3218809
  simp only [CollatzResearch.WordTrace]
  refine ⟨117399608995812196656163481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78266405997208131104108987 117399608995812196656163481)
  ·
    refine ⟨88049706746859147492122611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117399608995812196656163481 88049706746859147492122611)
    ·
      refine ⟨132074560120288721238183917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88049706746859147492122611 132074560120288721238183917)
      ·
        refine ⟨49527960045108270464318969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132074560120288721238183917 49527960045108270464318969)
        ·
          refine ⟨37145970033831202848239227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49527960045108270464318969 37145970033831202848239227)
          ·
            refine ⟨55718955050746804272358841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37145970033831202848239227 55718955050746804272358841)
            ·
              refine ⟨41789216288060103204269131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55718955050746804272358841 41789216288060103204269131)
              ·
                refine ⟨62683824432090154806403697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41789216288060103204269131 62683824432090154806403697)
                ·
                  refine ⟨47012868324067616104802773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62683824432090154806403697 47012868324067616104802773)
                  ·
                    refine ⟨1101864101345334752456315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47012868324067616104802773 1101864101345334752456315)
                    ·
                      rfl

theorem cell22_3218809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_3218809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218809 prefixEnd_3218809 := by exact prefixLift 3218809
  have htrace : WordTrace (prefixWord ++ tailWord_3218809) baseStart_3218809 baseEnd_3218809 := by
    simpa [prefixWord, tailWord_3218809, baseEnd_3218809] using wordTrace_append hprefix tailTrace_3218809
  have hstable : (prefixWord ++ tailWord_3218809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218809).length < 2 ^ (prefixWord ++ tailWord_3218809).sum := by decide
  have hdescent : baseEnd_3218809 < baseStart_3218809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3218834 : List Nat := [3, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_3218834 : Nat := 118140960795 + 3218834 * 2 ^ 59
def prefixEnd_3218834 : Nat := 4983230072969 + 3 ^ 40 * 3218834 * 2
def baseEnd_3218834 : Nat := 367290886452081006860413

theorem tailTrace_3218834 : CollatzResearch.WordTrace tailWord_3218834 prefixEnd_3218834 367290886452081006860413 := by
  unfold tailWord_3218834
  simp only [CollatzResearch.WordTrace]
  refine ⟨29350130205180406481455889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78267013880481083950549037 29350130205180406481455889)
  ·
    refine ⟨22012597653885304861091917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29350130205180406481455889 22012597653885304861091917)
    ·
      refine ⟨8254724120206989322909469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22012597653885304861091917 8254724120206989322909469)
      ·
        refine ⟨3095521545077620996091051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8254724120206989322909469 3095521545077620996091051)
        ·
          refine ⟨4643282317616431494136577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3095521545077620996091051 4643282317616431494136577)
          ·
            refine ⟨3482461738212323620602433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4643282317616431494136577 3482461738212323620602433)
            ·
              refine ⟨2611846303659242715451825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3482461738212323620602433 2611846303659242715451825)
              ·
                refine ⟨1958884727744432036588869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611846303659242715451825 1958884727744432036588869)
                ·
                  refine ⟨367290886452081006860413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1958884727744432036588869 367290886452081006860413)
                  ·
                    rfl

theorem cell22_3218834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_3218834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3218834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3218834 prefixEnd_3218834 := by exact prefixLift 3218834
  have htrace : WordTrace (prefixWord ++ tailWord_3218834) baseStart_3218834 baseEnd_3218834 := by
    simpa [prefixWord, tailWord_3218834, baseEnd_3218834] using wordTrace_append hprefix tailTrace_3218834
  have hstable : (prefixWord ++ tailWord_3218834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3218834).length < 2 ^ (prefixWord ++ tailWord_3218834).sum := by decide
  have hdescent : baseEnd_3218834 < baseStart_3218834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3218834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219014 : List Nat := [6, 1, 1, 1, 4, 1, 1, 7]
def baseStart_3219014 : Nat := 118140960795 + 3219014 * 2 ^ 59
def prefixEnd_3219014 : Nat := 4983230072969 + 3 ^ 40 * 3219014 * 2
def baseEnd_3219014 : Nat := 122437141892753616786743

theorem tailTrace_3219014 : CollatzResearch.WordTrace tailWord_3219014 prefixEnd_3219014 122437141892753616786743 := by
  unfold tailWord_3219014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3668971436252172395855503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78271390640046344444917397 3668971436252172395855503)
  ·
    refine ⟨5503457154378258593783255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3668971436252172395855503 5503457154378258593783255)
    ·
      refine ⟨8255185731567387890674883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5503457154378258593783255 8255185731567387890674883)
      ·
        refine ⟨12382778597351081836012325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8255185731567387890674883 12382778597351081836012325)
        ·
          refine ⟨2321770987003327844252311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12382778597351081836012325 2321770987003327844252311)
          ·
            refine ⟨3482656480504991766378467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321770987003327844252311 3482656480504991766378467)
            ·
              refine ⟨5223984720757487649567701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482656480504991766378467 5223984720757487649567701)
              ·
                refine ⟨122437141892753616786743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5223984720757487649567701 122437141892753616786743)
                ·
                  rfl

theorem cell22_3219014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_3219014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219014 prefixEnd_3219014 := by exact prefixLift 3219014
  have htrace : WordTrace (prefixWord ++ tailWord_3219014) baseStart_3219014 baseEnd_3219014 := by
    simpa [prefixWord, tailWord_3219014, baseEnd_3219014] using wordTrace_append hprefix tailTrace_3219014
  have hstable : (prefixWord ++ tailWord_3219014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219014).length < 2 ^ (prefixWord ++ tailWord_3219014).sum := by decide
  have hdescent : baseEnd_3219014 < baseStart_3219014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219051 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 2, 9]
def baseStart_3219051 : Nat := 118140960795 + 3219051 * 2 ^ 59
def prefixEnd_3219051 : Nat := 4983230072969 + 3 ^ 40 * 3219051 * 2
def baseEnd_3219051 : Nat := 1101946942890926787905573

theorem tailTrace_3219051 : CollatzResearch.WordTrace tailWord_3219051 prefixEnd_3219051 1101946942890926787905573 := by
  unfold tailWord_3219051
  simp only [CollatzResearch.WordTrace]
  refine ⟨117408435460935471986473007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78272290307290314657648671 117408435460935471986473007)
  ·
    refine ⟨176112653191403207979709511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117408435460935471986473007 176112653191403207979709511)
    ·
      refine ⟨264168979787104811969564267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176112653191403207979709511 264168979787104811969564267)
      ·
        refine ⟨396253469680657217954346401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264168979787104811969564267 396253469680657217954346401)
        ·
          refine ⟨297190102260492913465759801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396253469680657217954346401 297190102260492913465759801)
          ·
            refine ⟨222892576695369685099319851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297190102260492913465759801 222892576695369685099319851)
            ·
              refine ⟨334338865043054527648979777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222892576695369685099319851 334338865043054527648979777)
              ·
                refine ⟨250754148782290895736734833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334338865043054527648979777 250754148782290895736734833)
                ·
                  refine ⟨188065611586718171802551125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250754148782290895736734833 188065611586718171802551125)
                  ·
                    refine ⟨1101946942890926787905573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 188065611586718171802551125 1101946942890926787905573)
                    ·
                      rfl

theorem cell22_3219051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_3219051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219051 prefixEnd_3219051 := by exact prefixLift 3219051
  have htrace : WordTrace (prefixWord ++ tailWord_3219051) baseStart_3219051 baseEnd_3219051 := by
    simpa [prefixWord, tailWord_3219051, baseEnd_3219051] using wordTrace_append hprefix tailTrace_3219051
  have hstable : (prefixWord ++ tailWord_3219051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219051).length < 2 ^ (prefixWord ++ tailWord_3219051).sum := by decide
  have hdescent : baseEnd_3219051 < baseStart_3219051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219102 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_3219102 : Nat := 118140960795 + 3219102 * 2 ^ 59
def prefixEnd_3219102 : Nat := 4983230072969 + 3 ^ 40 * 3219102 * 2
def baseEnd_3219102 : Nat := 1101964401233179654880417

theorem tailTrace_3219102 : CollatzResearch.WordTrace tailWord_3219102 prefixEnd_3219102 1101964401233179654880417 := by
  unfold tailWord_3219102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14676286947968838462072445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78273530389167138464386373 14676286947968838462072445)
  ·
    refine ⟨5503607605488314423277167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14676286947968838462072445 5503607605488314423277167)
    ·
      refine ⟨8255411408232471634915751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5503607605488314423277167 8255411408232471634915751)
      ·
        refine ⟨12383117112348707452373627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8255411408232471634915751 12383117112348707452373627)
        ·
          refine ⟨18574675668523061178560441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12383117112348707452373627 18574675668523061178560441)
          ·
            refine ⟨13931006751392295883920331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18574675668523061178560441 13931006751392295883920331)
            ·
              refine ⟨20896510127088443825880497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13931006751392295883920331 20896510127088443825880497)
              ·
                refine ⟨15672382595316332869410373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20896510127088443825880497 15672382595316332869410373)
                ·
                  refine ⟨2938571736621812413014445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15672382595316332869410373 2938571736621812413014445)
                  ·
                    refine ⟨1101964401233179654880417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938571736621812413014445 1101964401233179654880417)
                    ·
                      rfl

theorem cell22_3219102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_3219102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219102 prefixEnd_3219102 := by exact prefixLift 3219102
  have htrace : WordTrace (prefixWord ++ tailWord_3219102) baseStart_3219102 baseEnd_3219102 := by
    simpa [prefixWord, tailWord_3219102, baseEnd_3219102] using wordTrace_append hprefix tailTrace_3219102
  have hstable : (prefixWord ++ tailWord_3219102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219102).length < 2 ^ (prefixWord ++ tailWord_3219102).sum := by decide
  have hdescent : baseEnd_3219102 < baseStart_3219102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219181 : List Nat := [1, 5, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_3219181 : Nat := 118140960795 + 3219181 * 2 ^ 59
def prefixEnd_3219181 : Nat := 4983230072969 + 3 ^ 40 * 3219181 * 2
def baseEnd_3219181 : Nat := 1101991444547649782155175

theorem tailTrace_3219181 : CollatzResearch.WordTrace tailWord_3219181 prefixEnd_3219181 1101991444547649782155175 := by
  unfold tailWord_3219181
  simp only [CollatzResearch.WordTrace]
  refine ⟨117413176950464504188705397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78275451300309669459136931 117413176950464504188705397)
  ·
    refine ⟨11007485339106047267691131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117413176950464504188705397 11007485339106047267691131)
    ·
      refine ⟨16511228008659070901536697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11007485339106047267691131 16511228008659070901536697)
      ·
        refine ⟨12383421006494303176152523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16511228008659070901536697 12383421006494303176152523)
        ·
          refine ⟨18575131509741454764228785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12383421006494303176152523 18575131509741454764228785)
          ·
            refine ⟨13931348632306091073171589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18575131509741454764228785 13931348632306091073171589)
            ·
              refine ⟨2612127868557392076219673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13931348632306091073171589 2612127868557392076219673)
              ·
                refine ⟨1959095901418044057164755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612127868557392076219673 1959095901418044057164755)
                ·
                  refine ⟨2938643852127066085747133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959095901418044057164755 2938643852127066085747133)
                  ·
                    refine ⟨1101991444547649782155175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938643852127066085747133 1101991444547649782155175)
                    ·
                      rfl

theorem cell22_3219181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_3219181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219181 prefixEnd_3219181 := by exact prefixLift 3219181
  have htrace : WordTrace (prefixWord ++ tailWord_3219181) baseStart_3219181 baseEnd_3219181 := by
    simpa [prefixWord, tailWord_3219181, baseEnd_3219181] using wordTrace_append hprefix tailTrace_3219181
  have hstable : (prefixWord ++ tailWord_3219181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219181).length < 2 ^ (prefixWord ++ tailWord_3219181).sum := by decide
  have hdescent : baseEnd_3219181 < baseStart_3219181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219235 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 2, 4]
def baseStart_3219235 : Nat := 118140960795 + 3219235 * 2 ^ 59
def prefixEnd_3219235 : Nat := 4983230072969 + 3 ^ 40 * 3219235 * 2
def baseEnd_3219235 : Nat := 1102009929851211641305009

theorem tailTrace_3219235 : CollatzResearch.WordTrace tailWord_3219235 prefixEnd_3219235 1102009929851211641305009 := by
  unfold tailWord_3219235
  simp only [CollatzResearch.WordTrace]
  refine ⟨117415146492268871411171159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78276764328179247607447439 117415146492268871411171159)
  ·
    refine ⟨176122719738403307116756739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117415146492268871411171159 176122719738403307116756739)
    ·
      refine ⟨264184079607604960675135109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176122719738403307116756739 264184079607604960675135109)
      ·
        refine ⟨49534514926425930126587833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264184079607604960675135109 49534514926425930126587833)
        ·
          refine ⟨37150886194819447594940875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49534514926425930126587833 37150886194819447594940875)
          ·
            refine ⟨55726329292229171392411313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37150886194819447594940875 55726329292229171392411313)
            ·
              refine ⟨41794746969171878544308485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55726329292229171392411313 41794746969171878544308485)
              ·
                refine ⟨7836515056719727227057841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41794746969171878544308485 7836515056719727227057841)
                ·
                  refine ⟨5877386292539795420293381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7836515056719727227057841 5877386292539795420293381)
                  ·
                    refine ⟨1102009929851211641305009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5877386292539795420293381 1102009929851211641305009)
                    ·
                      rfl

theorem cell22_3219235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 4].length) (baseStart_3219235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219235 prefixEnd_3219235 := by exact prefixLift 3219235
  have htrace : WordTrace (prefixWord ++ tailWord_3219235) baseStart_3219235 baseEnd_3219235 := by
    simpa [prefixWord, tailWord_3219235, baseEnd_3219235] using wordTrace_append hprefix tailTrace_3219235
  have hstable : (prefixWord ++ tailWord_3219235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219235).length < 2 ^ (prefixWord ++ tailWord_3219235).sum := by decide
  have hdescent : baseEnd_3219235 < baseStart_3219235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219237 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_3219237 : Nat := 118140960795 + 3219237 * 2 ^ 59
def prefixEnd_3219237 : Nat := 4983230072969 + 3 ^ 40 * 3219237 * 2
def baseEnd_3219237 : Nat := 1102010614492084302755003

theorem tailTrace_3219237 : CollatzResearch.WordTrace tailWord_3219237 prefixEnd_3219237 1102010614492084302755003 := by
  unfold tailWord_3219237
  simp only [CollatzResearch.WordTrace]
  refine ⟨117415219438261625752743965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78276812958841083835162643 117415219438261625752743965)
  ·
    refine ⟨44030707289348109657278987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117415219438261625752743965 44030707289348109657278987)
    ·
      refine ⟨66046060934022164485918481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44030707289348109657278987 66046060934022164485918481)
      ·
        refine ⟨49534545700516623364438861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66046060934022164485918481 49534545700516623364438861)
        ·
          refine ⟨18575454637693733761664573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49534545700516623364438861 18575454637693733761664573)
          ·
            refine ⟨6965795489135150160624215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18575454637693733761664573 6965795489135150160624215)
            ·
              refine ⟨10448693233702725240936323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6965795489135150160624215 10448693233702725240936323)
              ·
                refine ⟨15673039850554087861404485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10448693233702725240936323 15673039850554087861404485)
                ·
                  refine ⟨2938694971978891474013341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15673039850554087861404485 2938694971978891474013341)
                  ·
                    refine ⟨1102010614492084302755003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938694971978891474013341 1102010614492084302755003)
                    ·
                      rfl

theorem cell22_3219237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_3219237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219237 prefixEnd_3219237 := by exact prefixLift 3219237
  have htrace : WordTrace (prefixWord ++ tailWord_3219237) baseStart_3219237 baseEnd_3219237 := by
    simpa [prefixWord, tailWord_3219237, baseEnd_3219237] using wordTrace_append hprefix tailTrace_3219237
  have hstable : (prefixWord ++ tailWord_3219237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219237).length < 2 ^ (prefixWord ++ tailWord_3219237).sum := by decide
  have hdescent : baseEnd_3219237 < baseStart_3219237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219252 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3219252 : Nat := 118140960795 + 3219252 * 2 ^ 59
def prefixEnd_3219252 : Nat := 4983230072969 + 3 ^ 40 * 3219252 * 2
def baseEnd_3219252 : Nat := 1102015749298629263629957

theorem tailTrace_3219252 : CollatzResearch.WordTrace tailWord_3219252 prefixEnd_3219252 1102015749298629263629957 := by
  unfold tailWord_3219252
  simp only [CollatzResearch.WordTrace]
  refine ⟨58707883266603641657270005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78277177688804855543026673 58707883266603641657270005)
  ·
    refine ⟨5503864056244091405369063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58707883266603641657270005 5503864056244091405369063)
    ·
      refine ⟨8255796084366137108053595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5503864056244091405369063 8255796084366137108053595)
      ·
        refine ⟨12383694126549205662080393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8255796084366137108053595 12383694126549205662080393)
        ·
          refine ⟨9287770594911904246560295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12383694126549205662080393 9287770594911904246560295)
          ·
            refine ⟨13931655892367856369840443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9287770594911904246560295 13931655892367856369840443)
            ·
              refine ⟨20897483838551784554760665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13931655892367856369840443 20897483838551784554760665)
              ·
                refine ⟨15673112878913838416070499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20897483838551784554760665 15673112878913838416070499)
                ·
                  refine ⟨23509669318370757624105749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15673112878913838416070499 23509669318370757624105749)
                  ·
                    refine ⟨1102015749298629263629957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23509669318370757624105749 1102015749298629263629957)
                    ·
                      rfl

theorem cell22_3219252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3219252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219252 prefixEnd_3219252 := by exact prefixLift 3219252
  have htrace : WordTrace (prefixWord ++ tailWord_3219252) baseStart_3219252 baseEnd_3219252 := by
    simpa [prefixWord, tailWord_3219252, baseEnd_3219252] using wordTrace_append hprefix tailTrace_3219252
  have hstable : (prefixWord ++ tailWord_3219252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219252).length < 2 ^ (prefixWord ++ tailWord_3219252).sum := by decide
  have hdescent : baseEnd_3219252 < baseStart_3219252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219254 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3219254 : Nat := 118140960795 + 3219254 * 2 ^ 59
def prefixEnd_3219254 : Nat := 4983230072969 + 3 ^ 40 * 3219254 * 2
def baseEnd_3219254 : Nat := 1102016433939501925079951

theorem tailTrace_3219254 : CollatzResearch.WordTrace tailWord_3219254 prefixEnd_3219254 1102016433939501925079951 := by
  unfold tailWord_3219254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7338489967450002353507051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78277226319466691770741877 7338489967450002353507051)
  ·
    refine ⟨11007734951175003530260577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7338489967450002353507051 11007734951175003530260577)
    ·
      refine ⟨8255801213381252647695433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11007734951175003530260577 8255801213381252647695433)
      ·
        refine ⟨6191850910035939485771575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8255801213381252647695433 6191850910035939485771575)
        ·
          refine ⟨9287776365053909228657363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6191850910035939485771575 9287776365053909228657363)
          ·
            refine ⟨13931664547580863842986045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9287776365053909228657363 13931664547580863842986045)
            ·
              refine ⟨5224374205342823941119767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13931664547580863842986045 5224374205342823941119767)
              ·
                refine ⟨7836561308014235911679651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224374205342823941119767 7836561308014235911679651)
                ·
                  refine ⟨11754841962021353867519477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7836561308014235911679651 11754841962021353867519477)
                  ·
                    refine ⟨1102016433939501925079951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11754841962021353867519477 1102016433939501925079951)
                    ·
                      rfl

theorem cell22_3219254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3219254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219254 prefixEnd_3219254 := by exact prefixLift 3219254
  have htrace : WordTrace (prefixWord ++ tailWord_3219254) baseStart_3219254 baseEnd_3219254 := by
    simpa [prefixWord, tailWord_3219254, baseEnd_3219254] using wordTrace_append hprefix tailTrace_3219254
  have hstable : (prefixWord ++ tailWord_3219254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219254).length < 2 ^ (prefixWord ++ tailWord_3219254).sum := by decide
  have hdescent : baseEnd_3219254 < baseStart_3219254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219267 : List Nat := [1, 1, 1, 3, 1, 7, 2, 6]
def baseStart_3219267 : Nat := 118140960795 + 3219267 * 2 ^ 59
def prefixEnd_3219267 : Nat := 4983230072969 + 3 ^ 40 * 3219267 * 2
def baseEnd_3219267 : Nat := 122446764900574913833879

theorem tailTrace_3219267 : CollatzResearch.WordTrace tailWord_3219267 prefixEnd_3219267 122446764900574913833879 := by
  unfold tailWord_3219267
  simp only [CollatzResearch.WordTrace]
  refine ⟨117416313628152940876336055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78277542418768627250890703 117416313628152940876336055)
  ·
    refine ⟨176124470442229411314504083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117416313628152940876336055 176124470442229411314504083)
    ·
      refine ⟨264186705663344116971756125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176124470442229411314504083 264186705663344116971756125)
      ·
        refine ⟨99070014623754043864408547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264186705663344116971756125 99070014623754043864408547)
        ·
          refine ⟨148605021935631065796612821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99070014623754043864408547 148605021935631065796612821)
          ·
            refine ⟨3482930201616353104608113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 148605021935631065796612821 3482930201616353104608113)
            ·
              refine ⟨2612197651212264828456085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3482930201616353104608113 2612197651212264828456085)
              ·
                refine ⟨122446764900574913833879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2612197651212264828456085 122446764900574913833879)
                ·
                  rfl

theorem cell22_3219267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 6].length) (baseStart_3219267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219267 prefixEnd_3219267 := by exact prefixLift 3219267
  have htrace : WordTrace (prefixWord ++ tailWord_3219267) baseStart_3219267 baseEnd_3219267 := by
    simpa [prefixWord, tailWord_3219267, baseEnd_3219267] using wordTrace_append hprefix tailTrace_3219267
  have hstable : (prefixWord ++ tailWord_3219267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219267).length < 2 ^ (prefixWord ++ tailWord_3219267).sum := by decide
  have hdescent : baseEnd_3219267 < baseStart_3219267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219295 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 7]
def baseStart_3219295 : Nat := 118140960795 + 3219295 * 2 ^ 59
def prefixEnd_3219295 : Nat := 4983230072969 + 3 ^ 40 * 3219295 * 2
def baseEnd_3219295 : Nat := 367343489692463828268275

theorem tailTrace_3219295 : CollatzResearch.WordTrace tailWord_3219295 prefixEnd_3219295 367343489692463828268275 := by
  unfold tailWord_3219295
  simp only [CollatzResearch.WordTrace]
  refine ⟨117417334872051501658355339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78278223248034334438903559 117417334872051501658355339)
  ·
    refine ⟨176126002308077252487533009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117417334872051501658355339 176126002308077252487533009)
    ·
      refine ⟨132094501731057939365649757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176126002308077252487533009 132094501731057939365649757)
      ·
        refine ⟨49535438149146727262118659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132094501731057939365649757 49535438149146727262118659)
        ·
          refine ⟨74303157223720090893177989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49535438149146727262118659 74303157223720090893177989)
          ·
            refine ⟨13931841979447517042470873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74303157223720090893177989 13931841979447517042470873)
            ·
              refine ⟨10448881484585637781853155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13931841979447517042470873 10448881484585637781853155)
              ·
                refine ⟨15673322226878456672779733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10448881484585637781853155 15673322226878456672779733)
                ·
                  refine ⟨367343489692463828268275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15673322226878456672779733 367343489692463828268275)
                  ·
                    rfl

theorem cell22_3219295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 7].length) (baseStart_3219295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219295 prefixEnd_3219295 := by exact prefixLift 3219295
  have htrace : WordTrace (prefixWord ++ tailWord_3219295) baseStart_3219295 baseEnd_3219295 := by
    simpa [prefixWord, tailWord_3219295, baseEnd_3219295] using wordTrace_append hprefix tailTrace_3219295
  have hstable : (prefixWord ++ tailWord_3219295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219295).length < 2 ^ (prefixWord ++ tailWord_3219295).sum := by decide
  have hdescent : baseEnd_3219295 < baseStart_3219295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219434 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_3219434 : Nat := 118140960795 + 3219434 * 2 ^ 59
def prefixEnd_3219434 : Nat := 4983230072969 + 3 ^ 40 * 3219434 * 2
def baseEnd_3219434 : Nat := 1102078051618041455579399

theorem tailTrace_3219434 : CollatzResearch.WordTrace tailWord_3219434 prefixEnd_3219434 1102078051618041455579399 := by
  unfold tailWord_3219434
  simp only [CollatzResearch.WordTrace]
  refine ⟨29355601154636982099416339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78281603079031952265110237 29355601154636982099416339)
  ·
    refine ⟨44033401731955473149124509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29355601154636982099416339 44033401731955473149124509)
    ·
      refine ⟨16512525649483302430921691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44033401731955473149124509 16512525649483302430921691)
      ·
        refine ⟨24768788474224953646382537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16512525649483302430921691 24768788474224953646382537)
        ·
          refine ⟨18576591355668715234786903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24768788474224953646382537 18576591355668715234786903)
          ·
            refine ⟨27864887033503072852180355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18576591355668715234786903 27864887033503072852180355)
            ·
              refine ⟨41797330550254609278270533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27864887033503072852180355 41797330550254609278270533)
              ·
                refine ⟨7836999478172739239675725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41797330550254609278270533 7836999478172739239675725)
                ·
                  refine ⟨2938874804314777214878397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7836999478172739239675725 2938874804314777214878397)
                  ·
                    refine ⟨1102078051618041455579399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938874804314777214878397 1102078051618041455579399)
                    ·
                      rfl

theorem cell22_3219434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_3219434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219434 prefixEnd_3219434 := by exact prefixLift 3219434
  have htrace : WordTrace (prefixWord ++ tailWord_3219434) baseStart_3219434 baseEnd_3219434 := by
    simpa [prefixWord, tailWord_3219434, baseEnd_3219434] using wordTrace_append hprefix tailTrace_3219434
  have hstable : (prefixWord ++ tailWord_3219434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219434).length < 2 ^ (prefixWord ++ tailWord_3219434).sum := by decide
  have hdescent : baseEnd_3219434 < baseStart_3219434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219451 : List Nat := [1, 1, 1, 1, 1, 3, 7, 3, 1, 3]
def baseStart_3219451 : Nat := 118140960795 + 3219451 * 2 ^ 59
def prefixEnd_3219451 : Nat := 4983230072969 + 3 ^ 40 * 3219451 * 2
def baseEnd_3219451 : Nat := 1102083871065459077904347

theorem tailTrace_3219451 : CollatzResearch.WordTrace tailWord_3219451 prefixEnd_3219451 1102083871065459077904347 := by
  unfold tailWord_3219451
  simp only [CollatzResearch.WordTrace]
  refine ⟨117423024659486340301034207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78282016439657560200689471 117423024659486340301034207)
  ·
    refine ⟨176134536989229510451551311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117423024659486340301034207 176134536989229510451551311)
    ·
      refine ⟨264201805483844265677326967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176134536989229510451551311 264201805483844265677326967)
      ·
        refine ⟨396302708225766398515990451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264201805483844265677326967 396302708225766398515990451)
        ·
          refine ⟨594454062338649597773985677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396302708225766398515990451 594454062338649597773985677)
          ·
            refine ⟨222920273376993599165244629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 594454062338649597773985677 222920273376993599165244629)
            ·
              refine ⟨5224693907273287480435421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 222920273376993599165244629 5224693907273287480435421)
              ·
                refine ⟨1959260215227482805163283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5224693907273287480435421 1959260215227482805163283)
                ·
                  refine ⟨2938890322841224207744925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959260215227482805163283 2938890322841224207744925)
                  ·
                    refine ⟨1102083871065459077904347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938890322841224207744925 1102083871065459077904347)
                    ·
                      rfl

theorem cell22_3219451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 3].length) (baseStart_3219451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219451 prefixEnd_3219451 := by exact prefixLift 3219451
  have htrace : WordTrace (prefixWord ++ tailWord_3219451) baseStart_3219451 baseEnd_3219451 := by
    simpa [prefixWord, tailWord_3219451, baseEnd_3219451] using wordTrace_append hprefix tailTrace_3219451
  have hstable : (prefixWord ++ tailWord_3219451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219451).length < 2 ^ (prefixWord ++ tailWord_3219451).sum := by decide
  have hdescent : baseEnd_3219451 < baseStart_3219451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219468 : List Nat := [2, 2, 1, 2, 3, 1, 5, 2, 1, 3]
def baseStart_3219468 : Nat := 118140960795 + 3219468 * 2 ^ 59
def prefixEnd_3219468 : Nat := 4983230072969 + 3 ^ 40 * 3219468 * 2
def baseEnd_3219468 : Nat := 1102089690512876700229295

theorem tailTrace_3219468 : CollatzResearch.WordTrace tailWord_3219468 prefixEnd_3219468 1102089690512876700229295 := by
  unfold tailWord_3219468
  simp only [CollatzResearch.WordTrace]
  refine ⟨58711822350212376102201529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78282429800283168136268705 58711822350212376102201529)
  ·
    refine ⟨44033866762659282076651147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58711822350212376102201529 44033866762659282076651147)
    ·
      refine ⟨66050800143988923114976721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44033866762659282076651147 66050800143988923114976721)
      ·
        refine ⟨49538100107991692336232541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66050800143988923114976721 49538100107991692336232541)
        ·
          refine ⟨18576787540496884626087203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49538100107991692336232541 18576787540496884626087203)
          ·
            refine ⟨27865181310745326939130805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18576787540496884626087203 27865181310745326939130805)
            ·
              refine ⟨2612360747882374400543513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27865181310745326939130805 2612360747882374400543513)
              ·
                refine ⟨1959270560911780800407635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612360747882374400543513 1959270560911780800407635)
                ·
                  refine ⟨2938905841367671200611453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959270560911780800407635 2938905841367671200611453)
                  ·
                    refine ⟨1102089690512876700229295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938905841367671200611453 1102089690512876700229295)
                    ·
                      rfl

theorem cell22_3219468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_3219468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219468 prefixEnd_3219468 := by exact prefixLift 3219468
  have htrace : WordTrace (prefixWord ++ tailWord_3219468) baseStart_3219468 baseEnd_3219468 := by
    simpa [prefixWord, tailWord_3219468, baseEnd_3219468] using wordTrace_append hprefix tailTrace_3219468
  have hstable : (prefixWord ++ tailWord_3219468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219468).length < 2 ^ (prefixWord ++ tailWord_3219468).sum := by decide
  have hdescent : baseEnd_3219468 < baseStart_3219468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219507 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 3, 5]
def baseStart_3219507 : Nat := 118140960795 + 3219507 * 2 ^ 59
def prefixEnd_3219507 : Nat := 4983230072969 + 3 ^ 40 * 3219507 * 2
def baseEnd_3219507 : Nat := 1102103041009893598504175

theorem tailTrace_3219507 : CollatzResearch.WordTrace tailWord_3219507 prefixEnd_3219507 1102103041009893598504175 := by
  unfold tailWord_3219507
  simp only [CollatzResearch.WordTrace]
  refine ⟨117425067147283461865072775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78283378098188974576715183 117425067147283461865072775)
  ·
    refine ⟨176137600720925192797609163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117425067147283461865072775 176137600720925192797609163)
    ·
      refine ⟨264206401081387789196413745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176137600720925192797609163 264206401081387789196413745)
      ·
        refine ⟨198154800811040841897310309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264206401081387789196413745 198154800811040841897310309)
        ·
          refine ⟨37154025152070157855745683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198154800811040841897310309 37154025152070157855745683)
          ·
            refine ⟨55731037728105236783618525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37154025152070157855745683 55731037728105236783618525)
            ·
              refine ⟨20899139148039463793856947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55731037728105236783618525 20899139148039463793856947)
              ·
                refine ⟨31348708722059195690785421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20899139148039463793856947 31348708722059195690785421)
                ·
                  refine ⟨11755765770772198384044533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31348708722059195690785421 11755765770772198384044533)
                  ·
                    refine ⟨1102103041009893598504175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11755765770772198384044533 1102103041009893598504175)
                    ·
                      rfl

theorem cell22_3219507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_3219507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219507 prefixEnd_3219507 := by exact prefixLift 3219507
  have htrace : WordTrace (prefixWord ++ tailWord_3219507) baseStart_3219507 baseEnd_3219507 := by
    simpa [prefixWord, tailWord_3219507, baseEnd_3219507] using wordTrace_append hprefix tailTrace_3219507
  have hstable : (prefixWord ++ tailWord_3219507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219507).length < 2 ^ (prefixWord ++ tailWord_3219507).sum := by decide
  have hdescent : baseEnd_3219507 < baseStart_3219507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219526 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3219526 : Nat := 118140960795 + 3219526 * 2 ^ 59
def prefixEnd_3219526 : Nat := 4983230072969 + 3 ^ 40 * 3219526 * 2
def baseEnd_3219526 : Nat := 367369848366061294093039

theorem tailTrace_3219526 : CollatzResearch.WordTrace tailWord_3219526 prefixEnd_3219526 367369848366061294093039 := by
  unfold tailWord_3219526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669555004194207128437951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78283840089476418740009621 3669555004194207128437951)
  ·
    refine ⟨5504332506291310692656927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3669555004194207128437951 5504332506291310692656927)
    ·
      refine ⟨8256498759436966038985391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5504332506291310692656927 8256498759436966038985391)
      ·
        refine ⟨12384748139155449058478087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8256498759436966038985391 12384748139155449058478087)
        ·
          refine ⟨18577122208733173587717131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12384748139155449058478087 18577122208733173587717131)
          ·
            refine ⟨27865683313099760381575697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18577122208733173587717131 27865683313099760381575697)
            ·
              refine ⟨20899262484824820286181773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27865683313099760381575697 20899262484824820286181773)
              ·
                refine ⟨7837223431809307607318165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20899262484824820286181773 7837223431809307607318165)
                ·
                  refine ⟨367369848366061294093039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7837223431809307607318165 367369848366061294093039)
                  ·
                    rfl

theorem cell22_3219526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3219526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219526 prefixEnd_3219526 := by exact prefixLift 3219526
  have htrace : WordTrace (prefixWord ++ tailWord_3219526) baseStart_3219526 baseEnd_3219526 := by
    simpa [prefixWord, tailWord_3219526, baseEnd_3219526] using wordTrace_append hprefix tailTrace_3219526
  have hstable : (prefixWord ++ tailWord_3219526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219526).length < 2 ^ (prefixWord ++ tailWord_3219526).sum := by decide
  have hdescent : baseEnd_3219526 < baseStart_3219526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219541 : List Nat := [1, 3, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_3219541 : Nat := 118140960795 + 3219541 * 2 ^ 59
def prefixEnd_3219541 : Nat := 4983230072969 + 3 ^ 40 * 3219541 * 2
def baseEnd_3219541 : Nat := 1102114679904728843154071

theorem tailTrace_3219541 : CollatzResearch.WordTrace tailWord_3219541 prefixEnd_3219541 1102114679904728843154071 := by
  unfold tailWord_3219541
  simp only [CollatzResearch.WordTrace]
  refine ⟨117426307229160285671810477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78284204819440190447873651 117426307229160285671810477)
  ·
    refine ⟨44034865210935107126928929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117426307229160285671810477 44034865210935107126928929)
    ·
      refine ⟨33026148908201330345196697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44034865210935107126928929 33026148908201330345196697)
      ·
        refine ⟨24769611681150997758897523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33026148908201330345196697 24769611681150997758897523)
        ·
          refine ⟨37154417521726496638346285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24769611681150997758897523 37154417521726496638346285)
          ·
            refine ⟨13932906570647436239379857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37154417521726496638346285 13932906570647436239379857)
            ·
              refine ⟨10449679927985577179534893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13932906570647436239379857 10449679927985577179534893)
              ·
                refine ⟨3918629972994591442325585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10449679927985577179534893 3918629972994591442325585)
                ·
                  refine ⟨2938972479745943581744189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918629972994591442325585 2938972479745943581744189)
                  ·
                    refine ⟨1102114679904728843154071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938972479745943581744189 1102114679904728843154071)
                    ·
                      rfl

theorem cell22_3219541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_3219541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219541 prefixEnd_3219541 := by exact prefixLift 3219541
  have htrace : WordTrace (prefixWord ++ tailWord_3219541) baseStart_3219541 baseEnd_3219541 := by
    simpa [prefixWord, tailWord_3219541, baseEnd_3219541] using wordTrace_append hprefix tailTrace_3219541
  have hstable : (prefixWord ++ tailWord_3219541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219541).length < 2 ^ (prefixWord ++ tailWord_3219541).sum := by decide
  have hdescent : baseEnd_3219541 < baseStart_3219541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219569 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 5, 3]
def baseStart_3219569 : Nat := 118140960795 + 3219569 * 2 ^ 59
def prefixEnd_3219569 : Nat := 4983230072969 + 3 ^ 40 * 3219569 * 2
def baseEnd_3219569 : Nat := 1102124264876946103453985

theorem tailTrace_3219569 : CollatzResearch.WordTrace tailWord_3219569 prefixEnd_3219569 1102124264876946103453985 := by
  unfold tailWord_3219569
  simp only [CollatzResearch.WordTrace]
  refine ⟨117427328473058846453829761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78284885648705897635886507 117427328473058846453829761)
  ·
    refine ⟨88070496354794134840372321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117427328473058846453829761 88070496354794134840372321)
    ·
      refine ⟨66052872266095601130279241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88070496354794134840372321 66052872266095601130279241)
      ·
        refine ⟨49539654199571700847709431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66052872266095601130279241 49539654199571700847709431)
        ·
          refine ⟨74309481299357551271564147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49539654199571700847709431 74309481299357551271564147)
          ·
            refine ⟨111464221949036326907346221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74309481299357551271564147 111464221949036326907346221)
            ·
              refine ⟨41799083230888622590254833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111464221949036326907346221 41799083230888622590254833)
              ·
                refine ⟨31349312423166466942691125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41799083230888622590254833 31349312423166466942691125)
                ·
                  refine ⟨2938998039671856275877293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31349312423166466942691125 2938998039671856275877293)
                  ·
                    refine ⟨1102124264876946103453985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938998039671856275877293 1102124264876946103453985)
                    ·
                      rfl

theorem cell22_3219569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_3219569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219569 prefixEnd_3219569 := by exact prefixLift 3219569
  have htrace : WordTrace (prefixWord ++ tailWord_3219569) baseStart_3219569 baseEnd_3219569 := by
    simpa [prefixWord, tailWord_3219569, baseEnd_3219569] using wordTrace_append hprefix tailTrace_3219569
  have hstable : (prefixWord ++ tailWord_3219569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219569).length < 2 ^ (prefixWord ++ tailWord_3219569).sum := by decide
  have hdescent : baseEnd_3219569 < baseStart_3219569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219637 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3219637 : Nat := 118140960795 + 3219637 * 2 ^ 59
def prefixEnd_3219637 : Nat := 4983230072969 + 3 ^ 40 * 3219637 * 2
def baseEnd_3219637 : Nat := 1102147542666616592753777

theorem tailTrace_3219637 : CollatzResearch.WordTrace tailWord_3219637 prefixEnd_3219637 1102147542666616592753777 := by
  unfold tailWord_3219637
  simp only [CollatzResearch.WordTrace]
  refine ⟨117429808636812494067305165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78286539091208329378203443 117429808636812494067305165)
  ·
    refine ⟨44036178238804685275239437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117429808636812494067305165 44036178238804685275239437)
    ·
      refine ⟨16513566839551756978214789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44036178238804685275239437 16513566839551756978214789)
      ·
        refine ⟨3096293782415954433415273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16513566839551756978214789 3096293782415954433415273)
        ·
          refine ⟨2322220336811965825061455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3096293782415954433415273 2322220336811965825061455)
          ·
            refine ⟨3483330505217948737592183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322220336811965825061455 3483330505217948737592183)
            ·
              refine ⟨5224995757826923106388275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483330505217948737592183 5224995757826923106388275)
              ·
                refine ⟨7837493636740384659582413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224995757826923106388275 7837493636740384659582413)
                ·
                  refine ⟨2939060113777644247343405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7837493636740384659582413 2939060113777644247343405)
                  ·
                    refine ⟨1102147542666616592753777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2939060113777644247343405 1102147542666616592753777)
                    ·
                      rfl

theorem cell22_3219637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3219637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219637 prefixEnd_3219637 := by exact prefixLift 3219637
  have htrace : WordTrace (prefixWord ++ tailWord_3219637) baseStart_3219637 baseEnd_3219637 := by
    simpa [prefixWord, tailWord_3219637, baseEnd_3219637] using wordTrace_append hprefix tailTrace_3219637
  have hstable : (prefixWord ++ tailWord_3219637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219637).length < 2 ^ (prefixWord ++ tailWord_3219637).sum := by decide
  have hdescent : baseEnd_3219637 < baseStart_3219637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219650 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3219650 : Nat := 118140960795 + 3219650 * 2 ^ 59
def prefixEnd_3219650 : Nat := 4983230072969 + 3 ^ 40 * 3219650 * 2
def baseEnd_3219650 : Nat := 367383997610762964059579

theorem tailTrace_3219650 : CollatzResearch.WordTrace tailWord_3219650 prefixEnd_3219650 367383997610762964059579 := by
  unfold tailWord_3219650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357570696441349321882101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78286855190510264858352269 29357570696441349321882101)
  ·
    refine ⟨2752272252791376498926447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29357570696441349321882101 2752272252791376498926447)
    ·
      refine ⟨4128408379187064748389671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2752272252791376498926447 4128408379187064748389671)
      ·
        refine ⟨6192612568780597122584507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4128408379187064748389671 6192612568780597122584507)
        ·
          refine ⟨9288918853170895683876761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6192612568780597122584507 9288918853170895683876761)
          ·
            refine ⟨6966689139878171762907571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9288918853170895683876761 6966689139878171762907571)
            ·
              refine ⟨10450033709817257644361357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966689139878171762907571 10450033709817257644361357)
              ·
                refine ⟨3918762641181471616635509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10450033709817257644361357 3918762641181471616635509)
                ·
                  refine ⟨367383997610762964059579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3918762641181471616635509 367383997610762964059579)
                  ·
                    rfl

theorem cell22_3219650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3219650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219650 prefixEnd_3219650 := by exact prefixLift 3219650
  have htrace : WordTrace (prefixWord ++ tailWord_3219650) baseStart_3219650 baseEnd_3219650 := by
    simpa [prefixWord, tailWord_3219650, baseEnd_3219650] using wordTrace_append hprefix tailTrace_3219650
  have hstable : (prefixWord ++ tailWord_3219650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219650).length < 2 ^ (prefixWord ++ tailWord_3219650).sum := by decide
  have hdescent : baseEnd_3219650 < baseStart_3219650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219659 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 1, 5]
def baseStart_3219659 : Nat := 118140960795 + 3219659 * 2 ^ 59
def prefixEnd_3219659 : Nat := 4983230072969 + 3 ^ 40 * 3219659 * 2
def baseEnd_3219659 : Nat := 1102155073716215868703709

theorem tailTrace_3219659 : CollatzResearch.WordTrace tailWord_3219659 prefixEnd_3219659 1102155073716215868703709 := by
  unfold tailWord_3219659
  simp only [CollatzResearch.WordTrace]
  refine ⟨117430611042732791824606031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78287074028488527883070687 117430611042732791824606031)
  ·
    refine ⟨176145916564099187736909047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117430611042732791824606031 176145916564099187736909047)
    ·
      refine ⟨264218874846148781605363571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176145916564099187736909047 264218874846148781605363571)
      ·
        refine ⟨396328312269223172408045357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264218874846148781605363571 396328312269223172408045357)
        ·
          refine ⟨148623117100958689653017009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396328312269223172408045357 148623117100958689653017009)
          ·
            refine ⟨111467337825719017239762757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148623117100958689653017009 111467337825719017239762757)
            ·
              refine ⟨20900125842322315732455517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111467337825719017239762757 20900125842322315732455517)
              ·
                refine ⟨7837547190870868399670819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20900125842322315732455517 7837547190870868399670819)
                ·
                  refine ⟨11756320786306302599506229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7837547190870868399670819 11756320786306302599506229)
                  ·
                    refine ⟨1102155073716215868703709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11756320786306302599506229 1102155073716215868703709)
                    ·
                      rfl

theorem cell22_3219659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 5].length) (baseStart_3219659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219659 prefixEnd_3219659 := by exact prefixLift 3219659
  have htrace : WordTrace (prefixWord ++ tailWord_3219659) baseStart_3219659 baseEnd_3219659 := by
    simpa [prefixWord, tailWord_3219659, baseEnd_3219659] using wordTrace_append hprefix tailTrace_3219659
  have hstable : (prefixWord ++ tailWord_3219659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219659).length < 2 ^ (prefixWord ++ tailWord_3219659).sum := by decide
  have hdescent : baseEnd_3219659 < baseStart_3219659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219674 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_3219674 : Nat := 118140960795 + 3219674 * 2 ^ 59
def prefixEnd_3219674 : Nat := 4983230072969 + 3 ^ 40 * 3219674 * 2
def baseEnd_3219674 : Nat := 1102160208522760829578663

theorem tailTrace_3219674 : CollatzResearch.WordTrace tailWord_3219674 prefixEnd_3219674 1102160208522760829578663 := by
  unfold tailWord_3219674
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357789534419612346600519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78287438758452299590934717 29357789534419612346600519)
  ·
    refine ⟨44036684301629418519900779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29357789534419612346600519 44036684301629418519900779)
    ·
      refine ⟨66055026452444127779851169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44036684301629418519900779 66055026452444127779851169)
      ·
        refine ⟨49541269839333095834888377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66055026452444127779851169 49541269839333095834888377)
        ·
          refine ⟨37155952379499821876166283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49541269839333095834888377 37155952379499821876166283)
          ·
            refine ⟨55733928569249732814249425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37155952379499821876166283 55733928569249732814249425)
            ·
              refine ⟨41800446426937299610687069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55733928569249732814249425 41800446426937299610687069)
              ·
                refine ⟨15675167410101487354007651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41800446426937299610687069 15675167410101487354007651)
                ·
                  refine ⟨23512751115152231031011477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15675167410101487354007651 23512751115152231031011477)
                  ·
                    refine ⟨1102160208522760829578663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23512751115152231031011477 1102160208522760829578663)
                    ·
                      rfl

theorem cell22_3219674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_3219674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219674 prefixEnd_3219674 := by exact prefixLift 3219674
  have htrace : WordTrace (prefixWord ++ tailWord_3219674) baseStart_3219674 baseEnd_3219674 := by
    simpa [prefixWord, tailWord_3219674, baseEnd_3219674] using wordTrace_append hprefix tailTrace_3219674
  have hstable : (prefixWord ++ tailWord_3219674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219674).length < 2 ^ (prefixWord ++ tailWord_3219674).sum := by decide
  have hdescent : baseEnd_3219674 < baseStart_3219674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219695 : List Nat := [1, 1, 2, 1, 6, 3, 2, 2, 4]
def baseStart_3219695 : Nat := 118140960795 + 3219695 * 2 ^ 59
def prefixEnd_3219695 : Nat := 4983230072969 + 3 ^ 40 * 3219695 * 2
def baseEnd_3219695 : Nat := 367389132417307924934533

theorem tailTrace_3219695 : CollatzResearch.WordTrace tailWord_3219695 prefixEnd_3219695 367389132417307924934533 := by
  unfold tailWord_3219695
  simp only [CollatzResearch.WordTrace]
  refine ⟨117431924070602369972916539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78287949380401579981944359 117431924070602369972916539)
  ·
    refine ⟨176147886105903554959374809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117431924070602369972916539 176147886105903554959374809)
    ·
      refine ⟨132110914579427666219531107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176147886105903554959374809 132110914579427666219531107)
      ·
        refine ⟨198166371869141499329296661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132110914579427666219531107 198166371869141499329296661)
        ·
          refine ⟨9289048681366007781060781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 198166371869141499329296661 9289048681366007781060781)
          ·
            refine ⟨3483393255512252917897793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9289048681366007781060781 3483393255512252917897793)
            ·
              refine ⟨2612544941634189688423345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3483393255512252917897793 2612544941634189688423345)
              ·
                refine ⟨1959408706225642266317509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612544941634189688423345 1959408706225642266317509)
                ·
                  refine ⟨367389132417307924934533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1959408706225642266317509 367389132417307924934533)
                  ·
                    rfl

theorem cell22_3219695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 4].length) (baseStart_3219695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219695 prefixEnd_3219695 := by exact prefixLift 3219695
  have htrace : WordTrace (prefixWord ++ tailWord_3219695) baseStart_3219695 baseEnd_3219695 := by
    simpa [prefixWord, tailWord_3219695, baseEnd_3219695] using wordTrace_append hprefix tailTrace_3219695
  have hstable : (prefixWord ++ tailWord_3219695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219695).length < 2 ^ (prefixWord ++ tailWord_3219695).sum := by decide
  have hdescent : baseEnd_3219695 < baseStart_3219695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219706 : List Nat := [3, 1, 1, 1, 1, 7, 1, 7]
def baseStart_3219706 : Nat := 118140960795 + 3219706 * 2 ^ 59
def prefixEnd_3219706 : Nat := 4983230072969 + 3 ^ 40 * 3219706 * 2
def baseEnd_3219706 : Nat := 122463462530747045864285

theorem tailTrace_3219706 : CollatzResearch.WordTrace tailWord_3219706 prefixEnd_3219706 122463462530747045864285 := by
  unfold tailWord_3219706
  simp only [CollatzResearch.WordTrace]
  refine ⟨29358081318390629712891743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78288216849041679234377981 29358081318390629712891743)
  ·
    refine ⟨44037121977585944569337615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29358081318390629712891743 44037121977585944569337615)
    ·
      refine ⟨66055682966378916854006423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44037121977585944569337615 66055682966378916854006423)
      ·
        refine ⟨99083524449568375281009635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66055682966378916854006423 99083524449568375281009635)
        ·
          refine ⟨148625286674352562921514453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99083524449568375281009635 148625286674352562921514453)
          ·
            refine ⟨3483405156430138193472995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 148625286674352562921514453 3483405156430138193472995)
            ·
              refine ⟨5225107734645207290209493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483405156430138193472995 5225107734645207290209493)
              ·
                refine ⟨122463462530747045864285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5225107734645207290209493 122463462530747045864285)
                ·
                  rfl

theorem cell22_3219706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_3219706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219706 prefixEnd_3219706 := by exact prefixLift 3219706
  have htrace : WordTrace (prefixWord ++ tailWord_3219706) baseStart_3219706 baseEnd_3219706 := by
    simpa [prefixWord, tailWord_3219706, baseEnd_3219706] using wordTrace_append hprefix tailTrace_3219706
  have hstable : (prefixWord ++ tailWord_3219706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219706).length < 2 ^ (prefixWord ++ tailWord_3219706).sum := by decide
  have hdescent : baseEnd_3219706 < baseStart_3219706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219721 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 5, 3]
def baseStart_3219721 : Nat := 118140960795 + 3219721 * 2 ^ 59
def prefixEnd_3219721 : Nat := 4983230072969 + 3 ^ 40 * 3219721 * 2
def baseEnd_3219721 : Nat := 1102176297583268373653519

theorem tailTrace_3219721 : CollatzResearch.WordTrace tailWord_3219721 prefixEnd_3219721 1102176297583268373653519 := by
  unfold tailWord_3219721
  simp only [CollatzResearch.WordTrace]
  refine ⟨117432872368508176413363017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78288581579005450942242011 117432872368508176413363017)
  ·
    refine ⟨88074654276381132310022263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117432872368508176413363017 88074654276381132310022263)
    ·
      refine ⟨132111981414571698465033395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88074654276381132310022263 132111981414571698465033395)
      ·
        refine ⟨198167972121857547697550093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132111981414571698465033395 198167972121857547697550093)
        ·
          refine ⟨74312989545696580386581285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198167972121857547697550093 74312989545696580386581285)
          ·
            refine ⟨13933685539818108822483991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74312989545696580386581285 13933685539818108822483991)
            ·
              refine ⟨20900528309727163233725987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13933685539818108822483991 20900528309727163233725987)
              ·
                refine ⟨31350792464590744850588981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20900528309727163233725987 31350792464590744850588981)
                ·
                  refine ⟨2939136793555382329742717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31350792464590744850588981 2939136793555382329742717)
                  ·
                    refine ⟨1102176297583268373653519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2939136793555382329742717 1102176297583268373653519)
                    ·
                      rfl

theorem cell22_3219721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_3219721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219721 prefixEnd_3219721 := by exact prefixLift 3219721
  have htrace : WordTrace (prefixWord ++ tailWord_3219721) baseStart_3219721 baseEnd_3219721 := by
    simpa [prefixWord, tailWord_3219721, baseEnd_3219721] using wordTrace_append hprefix tailTrace_3219721
  have hstable : (prefixWord ++ tailWord_3219721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219721).length < 2 ^ (prefixWord ++ tailWord_3219721).sum := by decide
  have hdescent : baseEnd_3219721 < baseStart_3219721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219813 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 6]
def baseStart_3219813 : Nat := 118140960795 + 3219813 * 2 ^ 59
def prefixEnd_3219813 : Nat := 4983230072969 + 3 ^ 40 * 3219813 * 2
def baseEnd_3219813 : Nat := 367402597021136933451079

theorem tailTrace_3219813 : CollatzResearch.WordTrace tailWord_3219813 prefixEnd_3219813 367402597021136933451079 := by
  unfold tailWord_3219813
  simp only [CollatzResearch.WordTrace]
  refine ⟨117436227884174876125712093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78290818589449917417141395 117436227884174876125712093)
  ·
    refine ⟨44038585456565578547142035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117436227884174876125712093 44038585456565578547142035)
    ·
      refine ⟨66057878184848367820713053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44038585456565578547142035 66057878184848367820713053)
      ·
        refine ⟨24771704319318137932767395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66057878184848367820713053 24771704319318137932767395)
        ·
          refine ⟨37157556478977206899151093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24771704319318137932767395 37157556478977206899151093)
          ·
            refine ⟨3483520919904113146795415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37157556478977206899151093 3483520919904113146795415)
            ·
              refine ⟨5225281379856169720193123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483520919904113146795415 5225281379856169720193123)
              ·
                refine ⟨7837922069784254580289685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5225281379856169720193123 7837922069784254580289685)
                ·
                  refine ⟨367402597021136933451079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7837922069784254580289685 367402597021136933451079)
                  ·
                    rfl

theorem cell22_3219813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_3219813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219813 prefixEnd_3219813 := by exact prefixLift 3219813
  have htrace : WordTrace (prefixWord ++ tailWord_3219813) baseStart_3219813 baseEnd_3219813 := by
    simpa [prefixWord, tailWord_3219813, baseEnd_3219813] using wordTrace_append hprefix tailTrace_3219813
  have hstable : (prefixWord ++ tailWord_3219813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219813).length < 2 ^ (prefixWord ++ tailWord_3219813).sum := by decide
  have hdescent : baseEnd_3219813 < baseStart_3219813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219871 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 1, 8]
def baseStart_3219871 : Nat := 118140960795 + 3219871 * 2 ^ 59
def prefixEnd_3219871 : Nat := 4983230072969 + 3 ^ 40 * 3219871 * 2
def baseEnd_3219871 : Nat := 1102227645648717982403059

theorem tailTrace_3219871 : CollatzResearch.WordTrace tailWord_3219871 prefixEnd_3219871 1102227645648717982403059 := by
  unfold tailWord_3219871
  simp only [CollatzResearch.WordTrace]
  refine ⟨117438343317964752031323467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78292228878643168020882311 117438343317964752031323467)
  ·
    refine ⟨176157514976947128046985201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117438343317964752031323467 176157514976947128046985201)
    ·
      refine ⟨132118136232710346035238901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176157514976947128046985201 132118136232710346035238901)
      ·
        refine ⟨12386075271816594940803647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132118136232710346035238901 12386075271816594940803647)
        ·
          refine ⟨18579112907724892411205471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12386075271816594940803647 18579112907724892411205471)
          ·
            refine ⟨27868669361587338616808207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18579112907724892411205471 27868669361587338616808207)
            ·
              refine ⟨41803004042381007925212311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27868669361587338616808207 41803004042381007925212311)
              ·
                refine ⟨62704506063571511887818467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41803004042381007925212311 62704506063571511887818467)
                ·
                  refine ⟨94056759095357267831727701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62704506063571511887818467 94056759095357267831727701)
                  ·
                    refine ⟨1102227645648717982403059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94056759095357267831727701 1102227645648717982403059)
                    ·
                      rfl

theorem cell22_3219871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_3219871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219871 prefixEnd_3219871 := by exact prefixLift 3219871
  have htrace : WordTrace (prefixWord ++ tailWord_3219871) baseStart_3219871 baseEnd_3219871 := by
    simpa [prefixWord, tailWord_3219871, baseEnd_3219871] using wordTrace_append hprefix tailTrace_3219871
  have hstable : (prefixWord ++ tailWord_3219871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219871).length < 2 ^ (prefixWord ++ tailWord_3219871).sum := by decide
  have hdescent : baseEnd_3219871 < baseStart_3219871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219950 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3219950 : Nat := 118140960795 + 3219950 * 2 ^ 59
def prefixEnd_3219950 : Nat := 4983230072969 + 3 ^ 40 * 3219950 * 2
def baseEnd_3219950 : Nat := 1102254688963188109677817

theorem tailTrace_3219950 : CollatzResearch.WordTrace tailWord_3219950 prefixEnd_3219950 1102254688963188109677817 := by
  unfold tailWord_3219950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14680153085584818565431163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78294149789785699015632869 14680153085584818565431163)
  ·
    refine ⟨22020229628377227848146745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14680153085584818565431163 22020229628377227848146745)
    ·
      refine ⟨16515172221282920886110059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22020229628377227848146745 16515172221282920886110059)
      ·
        refine ⟨24772758331924381329165089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16515172221282920886110059 24772758331924381329165089)
        ·
          refine ⟨18579568748943285996873817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24772758331924381329165089 18579568748943285996873817)
          ·
            refine ⟨13934676561707464497655363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18579568748943285996873817 13934676561707464497655363)
            ·
              refine ⟨20902014842561196746483045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13934676561707464497655363 20902014842561196746483045)
              ·
                refine ⟨3919127782980224389965571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20902014842561196746483045 3919127782980224389965571)
                ·
                  refine ⟨5878691674470336584948357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919127782980224389965571 5878691674470336584948357)
                  ·
                    refine ⟨1102254688963188109677817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5878691674470336584948357 1102254688963188109677817)
                    ·
                      rfl

theorem cell22_3219950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3219950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219950 prefixEnd_3219950 := by exact prefixLift 3219950
  have htrace : WordTrace (prefixWord ++ tailWord_3219950) baseStart_3219950 baseEnd_3219950 := by
    simpa [prefixWord, tailWord_3219950, baseEnd_3219950] using wordTrace_append hprefix tailTrace_3219950
  have hstable : (prefixWord ++ tailWord_3219950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219950).length < 2 ^ (prefixWord ++ tailWord_3219950).sum := by decide
  have hdescent : baseEnd_3219950 < baseStart_3219950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219980 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_3219980 : Nat := 118140960795 + 3219980 * 2 ^ 59
def prefixEnd_3219980 : Nat := 4983230072969 + 3 ^ 40 * 3219980 * 2
def baseEnd_3219980 : Nat := 1102264958576278031427725

theorem tailTrace_3219980 : CollatzResearch.WordTrace tailWord_3219980 prefixEnd_3219980 1102264958576278031427725 := by
  unfold tailWord_3219980
  simp only [CollatzResearch.WordTrace]
  refine ⟨58721159437284931823520697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78294879249713242431360929 58721159437284931823520697)
  ·
    refine ⟨44040869577963698867640523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58721159437284931823520697 44040869577963698867640523)
    ·
      refine ⟨66061304366945548301460785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44040869577963698867640523 66061304366945548301460785)
      ·
        refine ⟨49545978275209161226095589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66061304366945548301460785 49545978275209161226095589)
        ·
          refine ⟨9289870926601717729892923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49545978275209161226095589 9289870926601717729892923)
          ·
            refine ⟨13934806389902576594839385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9289870926601717729892923 13934806389902576594839385)
            ·
              refine ⟨10451104792426932446129539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13934806389902576594839385 10451104792426932446129539)
              ·
                refine ⟨15676657188640398669194309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10451104792426932446129539 15676657188640398669194309)
                ·
                  refine ⟨2939373222870074750473933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15676657188640398669194309 2939373222870074750473933)
                  ·
                    refine ⟨1102264958576278031427725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2939373222870074750473933 1102264958576278031427725)
                    ·
                      rfl

theorem cell22_3219980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_3219980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219980 prefixEnd_3219980 := by exact prefixLift 3219980
  have htrace : WordTrace (prefixWord ++ tailWord_3219980) baseStart_3219980 baseEnd_3219980 := by
    simpa [prefixWord, tailWord_3219980, baseEnd_3219980] using wordTrace_append hprefix tailTrace_3219980
  have hstable : (prefixWord ++ tailWord_3219980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219980).length < 2 ^ (prefixWord ++ tailWord_3219980).sum := by decide
  have hdescent : baseEnd_3219980 < baseStart_3219980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3219997 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_3219997 : Nat := 118140960795 + 3219997 * 2 ^ 59
def prefixEnd_3219997 : Nat := 4983230072969 + 3 ^ 40 * 3219997 * 2
def baseEnd_3219997 : Nat := 1102270778023695653752673

theorem tailTrace_3219997 : CollatzResearch.WordTrace tailWord_3219997 prefixEnd_3219997 1102270778023695653752673 := by
  unfold tailWord_3219997
  simp only [CollatzResearch.WordTrace]
  refine ⟨117442938915508275550410245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78295292610338850366940163 117442938915508275550410245)
  ·
    refine ⟨22020551046657801665701921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117442938915508275550410245 22020551046657801665701921)
    ·
      refine ⟨16515413284993351249276441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22020551046657801665701921 16515413284993351249276441)
      ·
        refine ⟨12386559963745013436957331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16515413284993351249276441 12386559963745013436957331)
        ·
          refine ⟨18579839945617520155435997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12386559963745013436957331 18579839945617520155435997)
          ·
            refine ⟨6967439979606570058288499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18579839945617520155435997 6967439979606570058288499)
            ·
              refine ⟨10451159969409855087432749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6967439979606570058288499 10451159969409855087432749)
              ·
                refine ⟨3919184988528695657787281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10451159969409855087432749 3919184988528695657787281)
                ·
                  refine ⟨2939388741396521743340461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3919184988528695657787281 2939388741396521743340461)
                  ·
                    refine ⟨1102270778023695653752673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2939388741396521743340461 1102270778023695653752673)
                    ·
                      rfl

theorem cell22_3219997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_3219997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3219997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3219997 prefixEnd_3219997 := by exact prefixLift 3219997
  have htrace : WordTrace (prefixWord ++ tailWord_3219997) baseStart_3219997 baseEnd_3219997 := by
    simpa [prefixWord, tailWord_3219997, baseEnd_3219997] using wordTrace_append hprefix tailTrace_3219997
  have hstable : (prefixWord ++ tailWord_3219997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3219997).length < 2 ^ (prefixWord ++ tailWord_3219997).sum := by decide
  have hdescent : baseEnd_3219997 < baseStart_3219997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3219997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220053 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3220053 : Nat := 118140960795 + 3220053 * 2 ^ 59
def prefixEnd_3220053 : Nat := 4983230072969 + 3 ^ 40 * 3220053 * 2
def baseEnd_3220053 : Nat := 1102289947968130174352501

theorem tailTrace_3220053 : CollatzResearch.WordTrace tailWord_3220053 prefixEnd_3220053 1102289947968130174352501 := by
  unfold tailWord_3220053
  simp only [CollatzResearch.WordTrace]
  refine ⟨117444981403305397114448813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78296654268870264742965875 117444981403305397114448813)
  ·
    refine ⟨44041868026239523917918305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117444981403305397114448813 44041868026239523917918305)
    ·
      refine ⟨33031401019679642938438729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44041868026239523917918305 33031401019679642938438729)
      ·
        refine ⟨24773550764759732203829047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33031401019679642938438729 24773550764759732203829047)
        ·
          refine ⟨37160326147139598305743571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24773550764759732203829047 37160326147139598305743571)
          ·
            refine ⟨55740489220709397458615357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37160326147139598305743571 55740489220709397458615357)
            ·
              refine ⟨20902683457766024046980759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55740489220709397458615357 20902683457766024046980759)
              ·
                refine ⟨31354025186649036070471139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20902683457766024046980759 31354025186649036070471139)
                ·
                  refine ⟨47031037779973554105706709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31354025186649036070471139 47031037779973554105706709)
                  ·
                    refine ⟨1102289947968130174352501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47031037779973554105706709 1102289947968130174352501)
                    ·
                      rfl

theorem cell22_3220053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3220053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220053 prefixEnd_3220053 := by exact prefixLift 3220053
  have htrace : WordTrace (prefixWord ++ tailWord_3220053) baseStart_3220053 baseEnd_3220053 := by
    simpa [prefixWord, tailWord_3220053, baseEnd_3220053] using wordTrace_append hprefix tailTrace_3220053
  have hstable : (prefixWord ++ tailWord_3220053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220053).length < 2 ^ (prefixWord ++ tailWord_3220053).sum := by decide
  have hdescent : baseEnd_3220053 < baseStart_3220053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220100 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 6]
def baseStart_3220100 : Nat := 118140960795 + 3220100 * 2 ^ 59
def prefixEnd_3220100 : Nat := 4983230072969 + 3 ^ 40 * 3220100 * 2
def baseEnd_3220100 : Nat := 367435345676212572809119

theorem tailTrace_3220100 : CollatzResearch.WordTrace tailWord_3220100 prefixEnd_3220100 367435345676212572809119 := by
  unfold tailWord_3220100
  simp only [CollatzResearch.WordTrace]
  refine ⟨58723347817067562070704877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78297797089423416094273169 58723347817067562070704877)
  ·
    refine ⟨22021255431400335776514329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58723347817067562070704877 22021255431400335776514329)
    ·
      refine ⟨16515941573550251832385747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22021255431400335776514329 16515941573550251832385747)
      ·
        refine ⟨24773912360325377748578621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16515941573550251832385747 24773912360325377748578621)
        ·
          refine ⟨9290217135122016655716983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24773912360325377748578621 9290217135122016655716983)
          ·
            refine ⟨13935325702683024983575475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9290217135122016655716983 13935325702683024983575475)
            ·
              refine ⟨20902988554024537475363213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13935325702683024983575475 20902988554024537475363213)
              ·
                refine ⟨7838620707759201553261205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20902988554024537475363213 7838620707759201553261205)
                ·
                  refine ⟨367435345676212572809119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7838620707759201553261205 367435345676212572809119)
                  ·
                    rfl

theorem cell22_3220100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_3220100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220100 prefixEnd_3220100 := by exact prefixLift 3220100
  have htrace : WordTrace (prefixWord ++ tailWord_3220100) baseStart_3220100 baseEnd_3220100 := by
    simpa [prefixWord, tailWord_3220100, baseEnd_3220100] using wordTrace_append hprefix tailTrace_3220100
  have hstable : (prefixWord ++ tailWord_3220100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220100).length < 2 ^ (prefixWord ++ tailWord_3220100).sum := by decide
  have hdescent : baseEnd_3220100 < baseStart_3220100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220207 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 5]
def baseStart_3220207 : Nat := 118140960795 + 3220207 * 2 ^ 59
def prefixEnd_3220207 : Nat := 4983230072969 + 3 ^ 40 * 3220207 * 2
def baseEnd_3220207 : Nat := 367447555105108368667343

theorem tailTrace_3220207 : CollatzResearch.WordTrace tailWord_3220207 prefixEnd_3220207 367447555105108368667343 := by
  unfold tailWord_3220207
  simp only [CollatzResearch.WordTrace]
  refine ⟨117450598244747481415554875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78300398829831654277036583 117450598244747481415554875)
  ·
    refine ⟨176175897367121222123332313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117450598244747481415554875 176175897367121222123332313)
    ·
      refine ⟨132131923025340916592499235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176175897367121222123332313 132131923025340916592499235)
      ·
        refine ⟨198197884538011374888748853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132131923025340916592499235 198197884538011374888748853)
        ·
          refine ⟨18581051675438566395820205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198197884538011374888748853 18581051675438566395820205)
          ·
            refine ⟨6967894378289462398432577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18581051675438566395820205 6967894378289462398432577)
            ·
              refine ⟨5225920783717096798824433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6967894378289462398432577 5225920783717096798824433)
              ·
                refine ⟨3919440587787822599118325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5225920783717096798824433 3919440587787822599118325)
                ·
                  refine ⟨367447555105108368667343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3919440587787822599118325 367447555105108368667343)
                  ·
                    rfl

theorem cell22_3220207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 5].length) (baseStart_3220207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220207 prefixEnd_3220207 := by exact prefixLift 3220207
  have htrace : WordTrace (prefixWord ++ tailWord_3220207) baseStart_3220207 baseEnd_3220207 := by
    simpa [prefixWord, tailWord_3220207, baseEnd_3220207] using wordTrace_append hprefix tailTrace_3220207
  have hstable : (prefixWord ++ tailWord_3220207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220207).length < 2 ^ (prefixWord ++ tailWord_3220207).sum := by decide
  have hdescent : baseEnd_3220207 < baseStart_3220207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220213 : List Nat := [1, 3, 6, 1, 2, 1, 1, 7]
def baseStart_3220213 : Nat := 118140960795 + 3220213 * 2 ^ 59
def prefixEnd_3220213 : Nat := 4983230072969 + 3 ^ 40 * 3220213 * 2
def baseEnd_3220213 : Nat := 122482746581993676705779

theorem tailTrace_3220213 : CollatzResearch.WordTrace tailWord_3220213 prefixEnd_3220213 122482746581993676705779 := by
  unfold tailWord_3220213
  simp only [CollatzResearch.WordTrace]
  refine ⟨117450817082725744440273293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78300544721817162960182195 117450817082725744440273293)
  ·
    refine ⟨44044056406022154165102485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117450817082725744440273293 44044056406022154165102485)
    ·
      refine ⟨2064565144032288476489179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44044056406022154165102485 2064565144032288476489179)
      ·
        refine ⟨3096847716048432714733769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064565144032288476489179 3096847716048432714733769)
        ·
          refine ⟨2322635787036324536050327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3096847716048432714733769 2322635787036324536050327)
          ·
            refine ⟨3483953680554486804075491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322635787036324536050327 3483953680554486804075491)
            ·
              refine ⟨5225930520831730206113237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483953680554486804075491 5225930520831730206113237)
              ·
                refine ⟨122482746581993676705779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5225930520831730206113237 122482746581993676705779)
                ·
                  rfl

theorem cell22_3220213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 7].length) (baseStart_3220213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220213 prefixEnd_3220213 := by exact prefixLift 3220213
  have htrace : WordTrace (prefixWord ++ tailWord_3220213) baseStart_3220213 baseEnd_3220213 := by
    simpa [prefixWord, tailWord_3220213, baseEnd_3220213] using wordTrace_append hprefix tailTrace_3220213
  have hstable : (prefixWord ++ tailWord_3220213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220213).length < 2 ^ (prefixWord ++ tailWord_3220213).sum := by decide
  have hdescent : baseEnd_3220213 < baseStart_3220213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220222 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3220222 : Nat := 118140960795 + 3220222 * 2 ^ 59
def prefixEnd_3220222 : Nat := 4983230072969 + 3 ^ 40 * 3220222 * 2
def baseEnd_3220222 : Nat := 1102347800121870066876983

theorem tailTrace_3220222 : CollatzResearch.WordTrace tailWord_3220222 prefixEnd_3220222 1102347800121870066876983 := by
  unfold tailWord_3220222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14681393167461642372168865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78300763559795425984900613 14681393167461642372168865)
  ·
    refine ⟨11011044875596231779126649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14681393167461642372168865 11011044875596231779126649)
    ·
      refine ⟨8258283656697173834344987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11011044875596231779126649 8258283656697173834344987)
      ·
        refine ⟨12387425485045760751517481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8258283656697173834344987 12387425485045760751517481)
        ·
          refine ⟨9290569113784320563638111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12387425485045760751517481 9290569113784320563638111)
          ·
            refine ⟨13935853670676480845457167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9290569113784320563638111 13935853670676480845457167)
            ·
              refine ⟨20903780506014721268185751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13935853670676480845457167 20903780506014721268185751)
              ·
                refine ⟨31355670759022081902278627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20903780506014721268185751 31355670759022081902278627)
                ·
                  refine ⟨47033506138533122853417941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31355670759022081902278627 47033506138533122853417941)
                  ·
                    refine ⟨1102347800121870066876983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47033506138533122853417941 1102347800121870066876983)
                    ·
                      rfl

theorem cell22_3220222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3220222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220222 prefixEnd_3220222 := by exact prefixLift 3220222
  have htrace : WordTrace (prefixWord ++ tailWord_3220222) baseStart_3220222 baseEnd_3220222 := by
    simpa [prefixWord, tailWord_3220222, baseEnd_3220222] using wordTrace_append hprefix tailTrace_3220222
  have hstable : (prefixWord ++ tailWord_3220222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220222).length < 2 ^ (prefixWord ++ tailWord_3220222).sum := by decide
  have hdescent : baseEnd_3220222 < baseStart_3220222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220280 : List Nat := [2, 1, 2, 1, 3, 2, 2, 9]
def baseStart_3220280 : Nat := 118140960795 + 3220280 * 2 ^ 59
def prefixEnd_3220280 : Nat := 4983230072969 + 3 ^ 40 * 3220280 * 2
def baseEnd_3220280 : Nat := 122485294967464138769645

theorem tailTrace_3220280 : CollatzResearch.WordTrace tailWord_3220280 prefixEnd_3220280 122485294967464138769645 := by
  unfold tailWord_3220280
  simp only [CollatzResearch.WordTrace]
  refine ⟨58726630386741507441481147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78302173848988676588641529 58726630386741507441481147)
  ·
    refine ⟨88089945580112261162221721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58726630386741507441481147 88089945580112261162221721)
    ·
      refine ⟨66067459185084195871666291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88089945580112261162221721 66067459185084195871666291)
      ·
        refine ⟨99101188777626293807499437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66067459185084195871666291 99101188777626293807499437)
        ·
          refine ⟨37162945791609860177812289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99101188777626293807499437 37162945791609860177812289)
          ·
            refine ⟨27872209343707395133359217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37162945791609860177812289 27872209343707395133359217)
            ·
              refine ⟨20904157007780546350019413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27872209343707395133359217 20904157007780546350019413)
              ·
                refine ⟨122485294967464138769645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20904157007780546350019413 122485294967464138769645)
                ·
                  rfl

theorem cell22_3220280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 9].length) (baseStart_3220280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220280 prefixEnd_3220280 := by exact prefixLift 3220280
  have htrace : WordTrace (prefixWord ++ tailWord_3220280) baseStart_3220280 baseEnd_3220280 := by
    simpa [prefixWord, tailWord_3220280, baseEnd_3220280] using wordTrace_append hprefix tailTrace_3220280
  have hstable : (prefixWord ++ tailWord_3220280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220280).length < 2 ^ (prefixWord ++ tailWord_3220280).sum := by decide
  have hdescent : baseEnd_3220280 < baseStart_3220280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220295 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3220295 : Nat := 118140960795 + 3220295 * 2 ^ 59
def prefixEnd_3220295 : Nat := 4983230072969 + 3 ^ 40 * 3220295 * 2
def baseEnd_3220295 : Nat := 1102372789513722209801759

theorem tailTrace_3220295 : CollatzResearch.WordTrace tailWord_3220295 prefixEnd_3220295 1102372789513722209801759 := by
  unfold tailWord_3220295
  simp only [CollatzResearch.WordTrace]
  refine ⟨117453807868428672444758339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78302538578952448296505559 117453807868428672444758339)
  ·
    refine ⟨176180711802643008667137509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117453807868428672444758339 176180711802643008667137509)
    ·
      refine ⟨33033883462995564125088283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176180711802643008667137509 33033883462995564125088283)
      ·
        refine ⟨49550825194493346187632425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33033883462995564125088283 49550825194493346187632425)
        ·
          refine ⟨37163118895870009640724319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49550825194493346187632425 37163118895870009640724319)
          ·
            refine ⟨55744678343805014461086479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37163118895870009640724319 55744678343805014461086479)
            ·
              refine ⟨83617017515707521691629719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55744678343805014461086479 83617017515707521691629719)
              ·
                refine ⟨125425526273561282537444579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83617017515707521691629719 125425526273561282537444579)
                ·
                  refine ⟨188138289410341923806166869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125425526273561282537444579 188138289410341923806166869)
                  ·
                    refine ⟨1102372789513722209801759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 188138289410341923806166869 1102372789513722209801759)
                    ·
                      rfl

theorem cell22_3220295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3220295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220295 prefixEnd_3220295 := by exact prefixLift 3220295
  have htrace : WordTrace (prefixWord ++ tailWord_3220295) baseStart_3220295 baseEnd_3220295 := by
    simpa [prefixWord, tailWord_3220295, baseEnd_3220295] using wordTrace_append hprefix tailTrace_3220295
  have hstable : (prefixWord ++ tailWord_3220295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220295).length < 2 ^ (prefixWord ++ tailWord_3220295).sum := by decide
  have hdescent : baseEnd_3220295 < baseStart_3220295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220297 : List Nat := [1, 2, 1, 1, 2, 5, 4, 6]
def baseStart_3220297 : Nat := 118140960795 + 3220297 * 2 ^ 59
def prefixEnd_3220297 : Nat := 4983230072969 + 3 ^ 40 * 3220297 * 2
def baseEnd_3220297 : Nat := 122485941572732763472417

theorem tailTrace_3220297 : CollatzResearch.WordTrace tailWord_3220297 prefixEnd_3220297 122485941572732763472417 := by
  unfold tailWord_3220297
  simp only [CollatzResearch.WordTrace]
  refine ⟨117453880814421426786331145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78302587209614284524220763 117453880814421426786331145)
  ·
    refine ⟨88090410610816070089748359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117453880814421426786331145 88090410610816070089748359)
    ·
      refine ⟨132135615916224105134622539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88090410610816070089748359 132135615916224105134622539)
      ·
        refine ⟨198203423874336157701933809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132135615916224105134622539 198203423874336157701933809)
        ·
          refine ⟨148652567905752118276450357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198203423874336157701933809 148652567905752118276450357)
          ·
            refine ⟨13936178241164261088417221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148652567905752118276450357 13936178241164261088417221)
            ·
              refine ⟨2613033420218298954078229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13936178241164261088417221 2613033420218298954078229)
              ·
                refine ⟨122485941572732763472417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2613033420218298954078229 122485941572732763472417)
                ·
                  rfl

theorem cell22_3220297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 6].length) (baseStart_3220297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220297 prefixEnd_3220297 := by exact prefixLift 3220297
  have htrace : WordTrace (prefixWord ++ tailWord_3220297) baseStart_3220297 baseEnd_3220297 := by
    simpa [prefixWord, tailWord_3220297, baseEnd_3220297] using wordTrace_append hprefix tailTrace_3220297
  have hstable : (prefixWord ++ tailWord_3220297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220297).length < 2 ^ (prefixWord ++ tailWord_3220297).sum := by decide
  have hdescent : baseEnd_3220297 < baseStart_3220297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220312 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 5, 3]
def baseStart_3220312 : Nat := 118140960795 + 3220312 * 2 ^ 59
def prefixEnd_3220312 : Nat := 4983230072969 + 3 ^ 40 * 3220312 * 2
def baseEnd_3220312 : Nat := 1102378608961139832126707

theorem tailTrace_3220312 : CollatzResearch.WordTrace tailWord_3220312 prefixEnd_3220312 1102378608961139832126707 := by
  unfold tailWord_3220312
  simp only [CollatzResearch.WordTrace]
  refine ⟨58727213954683542174063595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78302951939578056232084793 58727213954683542174063595)
  ·
    refine ⟨88090820932025313261095393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58727213954683542174063595 88090820932025313261095393)
    ·
      refine ⟨66068115699018984945821545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88090820932025313261095393 66068115699018984945821545)
      ·
        refine ⟨49551086774264238709366159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66068115699018984945821545 49551086774264238709366159)
        ·
          refine ⟨74326630161396358064049239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49551086774264238709366159 74326630161396358064049239)
          ·
            refine ⟨111489945242094537096073859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74326630161396358064049239 111489945242094537096073859)
            ·
              refine ⟨167234917863141805644110789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111489945242094537096073859 167234917863141805644110789)
              ·
                refine ⟨31356547099339088558270773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167234917863141805644110789 31356547099339088558270773)
                ·
                  refine ⟨2939676290563039552337885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31356547099339088558270773 2939676290563039552337885)
                  ·
                    refine ⟨1102378608961139832126707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2939676290563039552337885 1102378608961139832126707)
                    ·
                      rfl

theorem cell22_3220312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_3220312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220312 prefixEnd_3220312 := by exact prefixLift 3220312
  have htrace : WordTrace (prefixWord ++ tailWord_3220312) baseStart_3220312 baseEnd_3220312 := by
    simpa [prefixWord, tailWord_3220312, baseEnd_3220312] using wordTrace_append hprefix tailTrace_3220312
  have hstable : (prefixWord ++ tailWord_3220312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220312).length < 2 ^ (prefixWord ++ tailWord_3220312).sum := by decide
  have hdescent : baseEnd_3220312 < baseStart_3220312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220436 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3220436 : Nat := 118140960795 + 3220436 * 2 ^ 59
def prefixEnd_3220436 : Nat := 4983230072969 + 3 ^ 40 * 3220436 * 2
def baseEnd_3220436 : Nat := 1102421056695244842026327

theorem tailTrace_3220436 : CollatzResearch.WordTrace tailWord_3220436 prefixEnd_3220436 1102421056695244842026327 := by
  unfold tailWord_3220436
  simp only [CollatzResearch.WordTrace]
  refine ⟨58729475280458926762820581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78305967040611902350427441 58729475280458926762820581)
  ·
    refine ⟨11011776615086048768028859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58729475280458926762820581 11011776615086048768028859)
    ·
      refine ⟨16517664922629073152043289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11011776615086048768028859 16517664922629073152043289)
      ·
        refine ⟨12388248691971804864032467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16517664922629073152043289 12388248691971804864032467)
        ·
          refine ⟨18582373037957707296048701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12388248691971804864032467 18582373037957707296048701)
          ·
            refine ⟨6968389889234140236018263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18582373037957707296048701 6968389889234140236018263)
            ·
              refine ⟨10452584833851210354027395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968389889234140236018263 10452584833851210354027395)
              ·
                refine ⟨15678877250776815531041093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10452584833851210354027395 15678877250776815531041093)
                ·
                  refine ⟨2939789484520652912070205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15678877250776815531041093 2939789484520652912070205)
                  ·
                    refine ⟨1102421056695244842026327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2939789484520652912070205 1102421056695244842026327)
                    ·
                      rfl

theorem cell22_3220436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3220436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220436 prefixEnd_3220436 := by exact prefixLift 3220436
  have htrace : WordTrace (prefixWord ++ tailWord_3220436) baseStart_3220436 baseEnd_3220436 := by
    simpa [prefixWord, tailWord_3220436, baseEnd_3220436] using wordTrace_append hprefix tailTrace_3220436
  have hstable : (prefixWord ++ tailWord_3220436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220436).length < 2 ^ (prefixWord ++ tailWord_3220436).sum := by decide
  have hdescent : baseEnd_3220436 < baseStart_3220436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220438 : List Nat := [5, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_3220438 : Nat := 118140960795 + 3220438 * 2 ^ 59
def prefixEnd_3220438 : Nat := 4983230072969 + 3 ^ 40 * 3220438 * 2
def baseEnd_3220438 : Nat := 367473913778705834492107

theorem tailTrace_3220438 : CollatzResearch.WordTrace tailWord_3220438 prefixEnd_3220438 367473913778705834492107 := by
  unfold tailWord_3220438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341188969181912991700873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78306015671273738578142645 7341188969181912991700873)
  ·
    refine ⟨5505891726886434743775655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7341188969181912991700873 5505891726886434743775655)
    ·
      refine ⟨8258837590329652115663483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5505891726886434743775655 8258837590329652115663483)
      ·
        refine ⟨12388256385494478173495225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8258837590329652115663483 12388256385494478173495225)
        ·
          refine ⟨9291192289120858630121419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12388256385494478173495225 9291192289120858630121419)
          ·
            refine ⟨13936788433681287945182129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9291192289120858630121419 13936788433681287945182129)
            ·
              refine ⟨10452591325260965958886597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13936788433681287945182129 10452591325260965958886597)
              ·
                refine ⟨1959860873486431117291237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10452591325260965958886597 1959860873486431117291237)
                ·
                  refine ⟨367473913778705834492107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1959860873486431117291237 367473913778705834492107)
                  ·
                    rfl

theorem cell22_3220438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_3220438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220438 prefixEnd_3220438 := by exact prefixLift 3220438
  have htrace : WordTrace (prefixWord ++ tailWord_3220438) baseStart_3220438 baseEnd_3220438 := by
    simpa [prefixWord, tailWord_3220438, baseEnd_3220438] using wordTrace_append hprefix tailTrace_3220438
  have hstable : (prefixWord ++ tailWord_3220438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220438).length < 2 ^ (prefixWord ++ tailWord_3220438).sum := by decide
  have hdescent : baseEnd_3220438 < baseStart_3220438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220453 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_3220453 : Nat := 118140960795 + 3220453 * 2 ^ 59
def prefixEnd_3220453 : Nat := 4983230072969 + 3 ^ 40 * 3220453 * 2
def baseEnd_3220453 : Nat := 1102426876142662464351275

theorem tailTrace_3220453 : CollatzResearch.WordTrace tailWord_3220453 prefixEnd_3220453 1102426876142662464351275 := by
  unfold tailWord_3220453
  simp only [CollatzResearch.WordTrace]
  refine ⟨117459570601856265429010013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78306380401237510286006675 117459570601856265429010013)
  ·
    refine ⟨44047338975696099535878755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117459570601856265429010013 44047338975696099535878755)
    ·
      refine ⟨66071008463544149303818133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44047338975696099535878755 66071008463544149303818133)
      ·
        refine ⟨3097078521728631998616475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66071008463544149303818133 3097078521728631998616475)
        ·
          refine ⟨4645617782592947997924713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097078521728631998616475 4645617782592947997924713)
          ·
            refine ⟨3484213336944710998443535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4645617782592947997924713 3484213336944710998443535)
            ·
              refine ⟨5226320005417066497665303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484213336944710998443535 5226320005417066497665303)
              ·
                refine ⟨7839480008125599746497955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226320005417066497665303 7839480008125599746497955)
                ·
                  refine ⟨11759220012188399619746933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7839480008125599746497955 11759220012188399619746933)
                  ·
                    refine ⟨1102426876142662464351275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11759220012188399619746933 1102426876142662464351275)
                    ·
                      rfl

theorem cell22_3220453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_3220453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220453 prefixEnd_3220453 := by exact prefixLift 3220453
  have htrace : WordTrace (prefixWord ++ tailWord_3220453) baseStart_3220453 baseEnd_3220453 := by
    simpa [prefixWord, tailWord_3220453, baseEnd_3220453] using wordTrace_append hprefix tailTrace_3220453
  have hstable : (prefixWord ++ tailWord_3220453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220453).length < 2 ^ (prefixWord ++ tailWord_3220453).sum := by decide
  have hdescent : baseEnd_3220453 < baseStart_3220453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220466 : List Nat := [3, 2, 1, 5, 1, 1, 1, 8]
def baseStart_3220466 : Nat := 118140960795 + 3220466 * 2 ^ 59
def prefixEnd_3220466 : Nat := 4983230072969 + 3 ^ 40 * 3220466 * 2
def baseEnd_3220466 : Nat := 122492369589814973752915

theorem tailTrace_3220466 : CollatzResearch.WordTrace tailWord_3220466 prefixEnd_3220466 122492369589814973752915 := by
  unfold tailWord_3220466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29365011187702292162308313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78306696500539445766155501 29365011187702292162308313)
  ·
    refine ⟨22023758390776719121731235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29365011187702292162308313 22023758390776719121731235)
    ·
      refine ⟨33035637586165078682596853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22023758390776719121731235 33035637586165078682596853)
      ·
        refine ⟨3097091023702976126493455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33035637586165078682596853 3097091023702976126493455)
        ·
          refine ⟨4645636535554464189740183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097091023702976126493455 4645636535554464189740183)
          ·
            refine ⟨6968454803331696284610275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645636535554464189740183 6968454803331696284610275)
            ·
              refine ⟨10452682204997544426915413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968454803331696284610275 10452682204997544426915413)
              ·
                refine ⟨122492369589814973752915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10452682204997544426915413 122492369589814973752915)
                ·
                  rfl

theorem cell22_3220466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_3220466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220466 prefixEnd_3220466 := by exact prefixLift 3220466
  have htrace : WordTrace (prefixWord ++ tailWord_3220466) baseStart_3220466 baseEnd_3220466 := by
    simpa [prefixWord, tailWord_3220466, baseEnd_3220466] using wordTrace_append hprefix tailTrace_3220466
  have hstable : (prefixWord ++ tailWord_3220466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220466).length < 2 ^ (prefixWord ++ tailWord_3220466).sum := by decide
  have hdescent : baseEnd_3220466 < baseStart_3220466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220494 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_3220494 : Nat := 118140960795 + 3220494 * 2 ^ 59
def prefixEnd_3220494 : Nat := 4983230072969 + 3 ^ 40 * 3220494 * 2
def baseEnd_3220494 : Nat := 367480303760184008025383

theorem tailTrace_3220494 : CollatzResearch.WordTrace tailWord_3220494 prefixEnd_3220494 367480303760184008025383 := by
  unfold tailWord_3220494
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682633249338466178906567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78307377329805152954168357 14682633249338466178906567)
  ·
    refine ⟨22023949874007699268359851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14682633249338466178906567 22023949874007699268359851)
    ·
      refine ⟨33035924811011548902539777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22023949874007699268359851 33035924811011548902539777)
      ·
        refine ⟨24776943608258661676904833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33035924811011548902539777 24776943608258661676904833)
        ·
          refine ⟨18582707706193996257678625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24776943608258661676904833 18582707706193996257678625)
          ·
            refine ⟨13937030779645497193258969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18582707706193996257678625 13937030779645497193258969)
            ·
              refine ⟨10452773084734122894944227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13937030779645497193258969 10452773084734122894944227)
              ·
                refine ⟨15679159627101184342416341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10452773084734122894944227 15679159627101184342416341)
                ·
                  refine ⟨367480303760184008025383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15679159627101184342416341 367480303760184008025383)
                  ·
                    rfl

theorem cell22_3220494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_3220494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220494 prefixEnd_3220494 := by exact prefixLift 3220494
  have htrace : WordTrace (prefixWord ++ tailWord_3220494) baseStart_3220494 baseEnd_3220494 := by
    simpa [prefixWord, tailWord_3220494, baseEnd_3220494] using wordTrace_append hprefix tailTrace_3220494
  have hstable : (prefixWord ++ tailWord_3220494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220494).length < 2 ^ (prefixWord ++ tailWord_3220494).sum := by decide
  have hdescent : baseEnd_3220494 < baseStart_3220494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220511 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 5]
def baseStart_3220511 : Nat := 118140960795 + 3220511 * 2 ^ 59
def prefixEnd_3220511 : Nat := 4983230072969 + 3 ^ 40 * 3220511 * 2
def baseEnd_3220511 : Nat := 367482243575989882133699

theorem tailTrace_3220511 : CollatzResearch.WordTrace tailWord_3220511 prefixEnd_3220511 367482243575989882133699 := by
  unfold tailWord_3220511
  simp only [CollatzResearch.WordTrace]
  refine ⟨117461686035646141334621387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78307790690430760889747591 117461686035646141334621387)
  ·
    refine ⟨176192529053469212001932081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117461686035646141334621387 176192529053469212001932081)
    ·
      refine ⟨132144396790101909001449061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176192529053469212001932081 132144396790101909001449061)
      ·
        refine ⟨24777074398144107937771699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132144396790101909001449061 24777074398144107937771699)
        ·
          refine ⟨37165611597216161906657549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24777074398144107937771699 37165611597216161906657549)
          ·
            refine ⟨13937104348956060714996581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37165611597216161906657549 13937104348956060714996581)
            ·
              refine ⟨2613207065429261384061859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13937104348956060714996581 2613207065429261384061859)
              ·
                refine ⟨3919810598143892076092789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613207065429261384061859 3919810598143892076092789)
                ·
                  refine ⟨367482243575989882133699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3919810598143892076092789 367482243575989882133699)
                  ·
                    rfl

theorem cell22_3220511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 5].length) (baseStart_3220511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220511 prefixEnd_3220511 := by exact prefixLift 3220511
  have htrace : WordTrace (prefixWord ++ tailWord_3220511) baseStart_3220511 baseEnd_3220511 := by
    simpa [prefixWord, tailWord_3220511, baseEnd_3220511] using wordTrace_append hprefix tailTrace_3220511
  have hstable : (prefixWord ++ tailWord_3220511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220511).length < 2 ^ (prefixWord ++ tailWord_3220511).sum := by decide
  have hdescent : baseEnd_3220511 < baseStart_3220511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220524 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_3220524 : Nat := 118140960795 + 3220524 * 2 ^ 59
def prefixEnd_3220524 : Nat := 4983230072969 + 3 ^ 40 * 3220524 * 2
def baseEnd_3220524 : Nat := 1102451180893641945826057

theorem tailTrace_3220524 : CollatzResearch.WordTrace tailWord_3220524 prefixEnd_3220524 1102451180893641945826057 := by
  unfold tailWord_3220524
  simp only [CollatzResearch.WordTrace]
  refine ⟨58731080092299522277422313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78308106789732696369896417 58731080092299522277422313)
  ·
    refine ⟨44048310069224641708066735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58731080092299522277422313 44048310069224641708066735)
    ·
      refine ⟨66072465103836962562100103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44048310069224641708066735 66072465103836962562100103)
      ·
        refine ⟨99108697655755443843150155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66072465103836962562100103 99108697655755443843150155)
        ·
          refine ⟨148663046483633165764725233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99108697655755443843150155 148663046483633165764725233)
          ·
            refine ⟨111497284862724874323543925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148663046483633165764725233 111497284862724874323543925)
            ·
              refine ⟨10452870455880456967832243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111497284862724874323543925 10452870455880456967832243)
              ·
                refine ⟨15679305683820685451748365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10452870455880456967832243 15679305683820685451748365)
                ·
                  refine ⟨5879739631432757044405637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15679305683820685451748365 5879739631432757044405637)
                  ·
                    refine ⟨1102451180893641945826057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5879739631432757044405637 1102451180893641945826057)
                    ·
                      rfl

theorem cell22_3220524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_3220524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220524 prefixEnd_3220524 := by exact prefixLift 3220524
  have htrace : WordTrace (prefixWord ++ tailWord_3220524) baseStart_3220524 baseEnd_3220524 := by
    simpa [prefixWord, tailWord_3220524, baseEnd_3220524] using wordTrace_append hprefix tailTrace_3220524
  have hstable : (prefixWord ++ tailWord_3220524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220524).length < 2 ^ (prefixWord ++ tailWord_3220524).sum := by decide
  have hdescent : baseEnd_3220524 < baseStart_3220524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220573 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 6]
def baseStart_3220573 : Nat := 118140960795 + 3220573 * 2 ^ 59
def prefixEnd_3220573 : Nat := 4983230072969 + 3 ^ 40 * 3220573 * 2
def baseEnd_3220573 : Nat := 367489318198340717116969

theorem tailTrace_3220573 : CollatzResearch.WordTrace tailWord_3220573 prefixEnd_3220573 367489318198340717116969 := by
  unfold tailWord_3220573
  simp only [CollatzResearch.WordTrace]
  refine ⟨117463947361421525923378373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78309298240947683948918915 117463947361421525923378373)
  ·
    refine ⟨22024490130266536110633445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117463947361421525923378373 22024490130266536110633445)
    ·
      refine ⟨4129591899424975520743771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22024490130266536110633445 4129591899424975520743771)
      ·
        refine ⟨6194387849137463281115657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129591899424975520743771 6194387849137463281115657)
        ·
          refine ⟨4645790886853097460836743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6194387849137463281115657 4645790886853097460836743)
          ·
            refine ⟨6968686330279646191255115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645790886853097460836743 6968686330279646191255115)
            ·
              refine ⟨10453029495419469286882673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968686330279646191255115 10453029495419469286882673)
              ·
                refine ⟨7839772121564601965162005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10453029495419469286882673 7839772121564601965162005)
                ·
                  refine ⟨367489318198340717116969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7839772121564601965162005 367489318198340717116969)
                  ·
                    rfl

theorem cell22_3220573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_3220573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220573 prefixEnd_3220573 := by exact prefixLift 3220573
  have htrace : WordTrace (prefixWord ++ tailWord_3220573) baseStart_3220573 baseEnd_3220573 := by
    simpa [prefixWord, tailWord_3220573, baseEnd_3220573] using wordTrace_append hprefix tailTrace_3220573
  have hstable : (prefixWord ++ tailWord_3220573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220573).length < 2 ^ (prefixWord ++ tailWord_3220573).sum := by decide
  have hdescent : baseEnd_3220573 < baseStart_3220573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220586 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3220586 : Nat := 118140960795 + 3220586 * 2 ^ 59
def prefixEnd_3220586 : Nat := 4983230072969 + 3 ^ 40 * 3220586 * 2
def baseEnd_3220586 : Nat := 1102472404760694450775867

theorem tailTrace_3220586 : CollatzResearch.WordTrace tailWord_3220586 prefixEnd_3220586 1102472404760694450775867 := by
  unfold tailWord_3220586
  simp only [CollatzResearch.WordTrace]
  refine ⟨29366105377593607285900403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78309614340249619429067741 29366105377593607285900403)
  ·
    refine ⟨44049158066390410928850605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29366105377593607285900403 44049158066390410928850605)
    ·
      refine ⟨16518434274896404098318977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44049158066390410928850605 16518434274896404098318977)
      ·
        refine ⟨12388825706172303073739233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16518434274896404098318977 12388825706172303073739233)
        ·
          refine ⟨9291619279629227305304425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12388825706172303073739233 9291619279629227305304425)
          ·
            refine ⟨6968714459721920478978319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9291619279629227305304425 6968714459721920478978319)
            ·
              refine ⟨10453071689582880718467479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968714459721920478978319 10453071689582880718467479)
              ·
                refine ⟨15679607534374321077701219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10453071689582880718467479 15679607534374321077701219)
                ·
                  refine ⟨23519411301561481616551829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15679607534374321077701219 23519411301561481616551829)
                  ·
                    refine ⟨1102472404760694450775867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23519411301561481616551829 1102472404760694450775867)
                    ·
                      rfl

theorem cell22_3220586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3220586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220586 prefixEnd_3220586 := by exact prefixLift 3220586
  have htrace : WordTrace (prefixWord ++ tailWord_3220586) baseStart_3220586 baseEnd_3220586 := by
    simpa [prefixWord, tailWord_3220586, baseEnd_3220586] using wordTrace_append hprefix tailTrace_3220586
  have hstable : (prefixWord ++ tailWord_3220586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220586).length < 2 ^ (prefixWord ++ tailWord_3220586).sum := by decide
  have hdescent : baseEnd_3220586 < baseStart_3220586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220693 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3220693 : Nat := 118140960795 + 3220693 * 2 ^ 59
def prefixEnd_3220693 : Nat := 4983230072969 + 3 ^ 40 * 3220693 * 2
def baseEnd_3220693 : Nat := 1102509033047381838350539

theorem tailTrace_3220693 : CollatzResearch.WordTrace tailWord_3220693 prefixEnd_3220693 1102509033047381838350539 := by
  unfold tailWord_3220693
  simp only [CollatzResearch.WordTrace]
  refine ⟨117468324120986786417746733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78312216080657857611831155 117468324120986786417746733)
  ·
    refine ⟨44050621545370044906655025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117468324120986786417746733 44050621545370044906655025)
    ·
      refine ⟨33037966159027533679991269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44050621545370044906655025 33037966159027533679991269)
      ·
        refine ⟨6194618654817662564998363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33037966159027533679991269 6194618654817662564998363)
        ·
          refine ⟨9291927982226493847497545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6194618654817662564998363 9291927982226493847497545)
          ·
            refine ⟨6968945986669870385623159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9291927982226493847497545 6968945986669870385623159)
            ·
              refine ⟨10453418980004805578434739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968945986669870385623159 10453418980004805578434739)
              ·
                refine ⟨15680128470007208367652109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10453418980004805578434739 15680128470007208367652109)
                ·
                  refine ⟨5880048176252703137869541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15680128470007208367652109 5880048176252703137869541)
                  ·
                    refine ⟨1102509033047381838350539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5880048176252703137869541 1102509033047381838350539)
                    ·
                      rfl

theorem cell22_3220693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3220693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220693 prefixEnd_3220693 := by exact prefixLift 3220693
  have htrace : WordTrace (prefixWord ++ tailWord_3220693) baseStart_3220693 baseEnd_3220693 := by
    simpa [prefixWord, tailWord_3220693, baseEnd_3220693] using wordTrace_append hprefix tailTrace_3220693
  have hstable : (prefixWord ++ tailWord_3220693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220693).length < 2 ^ (prefixWord ++ tailWord_3220693).sum := by decide
  have hdescent : baseEnd_3220693 < baseStart_3220693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220719 : List Nat := [1, 1, 2, 1, 17]
def baseStart_3220719 : Nat := 118140960795 + 3220719 * 2 ^ 59
def prefixEnd_3220719 : Nat := 4983230072969 + 3 ^ 40 * 3220719 * 2
def baseEnd_3220719 : Nat := 4537110836949491511113

theorem tailTrace_3220719 : CollatzResearch.WordTrace tailWord_3220719 prefixEnd_3220719 4537110836949491511113 := by
  unfold tailWord_3220719
  simp only [CollatzResearch.WordTrace]
  refine ⟨117469272418892592858193211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78312848279261728572128807 117469272418892592858193211)
  ·
    refine ⟨176203908628338889287289817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117469272418892592858193211 176203908628338889287289817)
    ·
      refine ⟨132152931471254166965467363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176203908628338889287289817 132152931471254166965467363)
      ·
        refine ⟨198229397206881250448201045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132152931471254166965467363 198229397206881250448201045)
        ·
          refine ⟨4537110836949491511113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 198229397206881250448201045 4537110836949491511113)
          ·
            rfl

theorem cell22_3220719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 17].length) (baseStart_3220719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220719 prefixEnd_3220719 := by exact prefixLift 3220719
  have htrace : WordTrace (prefixWord ++ tailWord_3220719) baseStart_3220719 baseEnd_3220719 := by
    simpa [prefixWord, tailWord_3220719, baseEnd_3220719] using wordTrace_append hprefix tailTrace_3220719
  have hstable : (prefixWord ++ tailWord_3220719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220719).length < 2 ^ (prefixWord ++ tailWord_3220719).sum := by decide
  have hdescent : baseEnd_3220719 < baseStart_3220719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220723 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 2, 3]
def baseStart_3220723 : Nat := 118140960795 + 3220723 * 2 ^ 59
def prefixEnd_3220723 : Nat := 4983230072969 + 3 ^ 40 * 3220723 * 2
def baseEnd_3220723 : Nat := 1102519302660471760100447

theorem tailTrace_3220723 : CollatzResearch.WordTrace tailWord_3220723 prefixEnd_3220723 1102519302660471760100447 := by
  unfold tailWord_3220723
  simp only [CollatzResearch.WordTrace]
  refine ⟨117469418310878101541338823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78312945540585401027559215 117469418310878101541338823)
  ·
    refine ⟨176204127466317152312008235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117469418310878101541338823 176204127466317152312008235)
    ·
      refine ⟨264306191199475728468012353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176204127466317152312008235 264306191199475728468012353)
      ·
        refine ⟨198229643399606796351009265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264306191199475728468012353 198229643399606796351009265)
        ·
          refine ⟨148672232549705097263256949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198229643399606796351009265 148672232549705097263256949)
          ·
            refine ⟨13938021801534852868430339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148672232549705097263256949 13938021801534852868430339)
            ·
              refine ⟨20907032702302279302645509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13938021801534852868430339 20907032702302279302645509)
              ·
                refine ⟨3920068631681677369246033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20907032702302279302645509 3920068631681677369246033)
                ·
                  refine ⟨2940051473761258026934525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3920068631681677369246033 2940051473761258026934525)
                  ·
                    refine ⟨1102519302660471760100447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940051473761258026934525 1102519302660471760100447)
                    ·
                      rfl

theorem cell22_3220723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 3].length) (baseStart_3220723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220723 prefixEnd_3220723 := by exact prefixLift 3220723
  have htrace : WordTrace (prefixWord ++ tailWord_3220723) baseStart_3220723 baseEnd_3220723 := by
    simpa [prefixWord, tailWord_3220723, baseEnd_3220723] using wordTrace_append hprefix tailTrace_3220723
  have hstable : (prefixWord ++ tailWord_3220723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220723).length < 2 ^ (prefixWord ++ tailWord_3220723).sum := by decide
  have hdescent : baseEnd_3220723 < baseStart_3220723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220740 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_3220740 : Nat := 118140960795 + 3220740 * 2 ^ 59
def prefixEnd_3220740 : Nat := 4983230072969 + 3 ^ 40 * 3220740 * 2
def baseEnd_3220740 : Nat := 1102525122107889382425395

theorem tailTrace_3220740 : CollatzResearch.WordTrace tailWord_3220740 prefixEnd_3220740 1102525122107889382425395 := by
  unfold tailWord_3220740
  simp only [CollatzResearch.WordTrace]
  refine ⟨58735019175908256722353837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78313358901211008963138449 58735019175908256722353837)
  ·
    refine ⟨22025632190965596270882689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58735019175908256722353837 22025632190965596270882689)
    ·
      refine ⟨16519224143224197203162017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22025632190965596270882689 16519224143224197203162017)
      ·
        refine ⟨12389418107418147902371513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16519224143224197203162017 12389418107418147902371513)
        ·
          refine ⟨9292063580563610926778635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12389418107418147902371513 9292063580563610926778635)
          ·
            refine ⟨13938095370845416390167953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9292063580563610926778635 13938095370845416390167953)
            ·
              refine ⟨10453571528134062292625965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13938095370845416390167953 10453571528134062292625965)
              ·
                refine ⟨3920089323050273359734737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10453571528134062292625965 3920089323050273359734737)
                ·
                  refine ⟨2940066992287705019801053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3920089323050273359734737 2940066992287705019801053)
                  ·
                    refine ⟨1102525122107889382425395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940066992287705019801053 1102525122107889382425395)
                    ·
                      rfl

theorem cell22_3220740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_3220740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220740 prefixEnd_3220740 := by exact prefixLift 3220740
  have htrace : WordTrace (prefixWord ++ tailWord_3220740) baseStart_3220740 baseEnd_3220740 := by
    simpa [prefixWord, tailWord_3220740, baseEnd_3220740] using wordTrace_append hprefix tailTrace_3220740
  have hstable : (prefixWord ++ tailWord_3220740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220740).length < 2 ^ (prefixWord ++ tailWord_3220740).sum := by decide
  have hdescent : baseEnd_3220740 < baseStart_3220740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220785 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 3, 3]
def baseStart_3220785 : Nat := 118140960795 + 3220785 * 2 ^ 59
def prefixEnd_3220785 : Nat := 4983230072969 + 3 ^ 40 * 3220785 * 2
def baseEnd_3220785 : Nat := 1102540526527524265050257

theorem tailTrace_3220785 : CollatzResearch.WordTrace tailWord_3220785 prefixEnd_3220785 1102540526527524265050257 := by
  unfold tailWord_3220785
  simp only [CollatzResearch.WordTrace]
  refine ⟨117471679636653486130095809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78314453091102324086730539 117471679636653486130095809)
  ·
    refine ⟨88103759727490114597571857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117471679636653486130095809 88103759727490114597571857)
    ·
      refine ⟨66077819795617585948178893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88103759727490114597571857 66077819795617585948178893)
      ·
        refine ⟨24779182423356594730567085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66077819795617585948178893 24779182423356594730567085)
        ·
          refine ⟨9292193408758723023962657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24779182423356594730567085 9292193408758723023962657)
          ·
            refine ⟨6969145056569042267971993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9292193408758723023962657 6969145056569042267971993)
            ·
              refine ⟨5226858792426781700978995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6969145056569042267971993 5226858792426781700978995)
              ·
                refine ⟨7840288188640172551468493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226858792426781700978995 7840288188640172551468493)
                ·
                  refine ⟨2940108070740064706800685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7840288188640172551468493 2940108070740064706800685)
                  ·
                    refine ⟨1102540526527524265050257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940108070740064706800685 1102540526527524265050257)
                    ·
                      rfl

theorem cell22_3220785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_3220785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220785 prefixEnd_3220785 := by exact prefixLift 3220785
  have htrace : WordTrace (prefixWord ++ tailWord_3220785) baseStart_3220785 baseEnd_3220785 := by
    simpa [prefixWord, tailWord_3220785, baseEnd_3220785] using wordTrace_append hprefix tailTrace_3220785
  have hstable : (prefixWord ++ tailWord_3220785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220785).length < 2 ^ (prefixWord ++ tailWord_3220785).sum := by decide
  have hdescent : baseEnd_3220785 < baseStart_3220785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220811 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 7, 4]
def baseStart_3220811 : Nat := 118140960795 + 3220811 * 2 ^ 59
def prefixEnd_3220811 : Nat := 4983230072969 + 3 ^ 40 * 3220811 * 2
def baseEnd_3220811 : Nat := 1102549426858868863900177

theorem tailTrace_3220811 : CollatzResearch.WordTrace tailWord_3220811 prefixEnd_3220811 1102549426858868863900177 := by
  unfold tailWord_3220811
  simp only [CollatzResearch.WordTrace]
  refine ⟨117472627934559292570542287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78315085289706195047028191 117472627934559292570542287)
  ·
    refine ⟨176208941901838938855813431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117472627934559292570542287 176208941901838938855813431)
    ·
      refine ⟨264313412852758408283720147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176208941901838938855813431 264313412852758408283720147)
      ·
        refine ⟨396470119279137612425580221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264313412852758408283720147 396470119279137612425580221)
        ·
          refine ⟨148676294729676604659592583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396470119279137612425580221 148676294729676604659592583)
          ·
            refine ⟨223014442094514906989388875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148676294729676604659592583 223014442094514906989388875)
            ·
              refine ⟨334521663141772360484083313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223014442094514906989388875 334521663141772360484083313)
              ·
                refine ⟨250891247356329270363062485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334521663141772360484083313 250891247356329270363062485)
                ·
                  refine ⟨5880263609913967274134277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 250891247356329270363062485 5880263609913967274134277)
                  ·
                    refine ⟨1102549426858868863900177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5880263609913967274134277 1102549426858868863900177)
                    ·
                      rfl

theorem cell22_3220811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 4].length) (baseStart_3220811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220811 prefixEnd_3220811 := by exact prefixLift 3220811
  have htrace : WordTrace (prefixWord ++ tailWord_3220811) baseStart_3220811 baseEnd_3220811 := by
    simpa [prefixWord, tailWord_3220811, baseEnd_3220811] using wordTrace_append hprefix tailTrace_3220811
  have hstable : (prefixWord ++ tailWord_3220811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220811).length < 2 ^ (prefixWord ++ tailWord_3220811).sum := by decide
  have hdescent : baseEnd_3220811 < baseStart_3220811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220826 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_3220826 : Nat := 118140960795 + 3220826 * 2 ^ 59
def prefixEnd_3220826 : Nat := 4983230072969 + 3 ^ 40 * 3220826 * 2
def baseEnd_3220826 : Nat := 367518187221804608258377

theorem tailTrace_3220826 : CollatzResearch.WordTrace tailWord_3220826 prefixEnd_3220826 367518187221804608258377 := by
  unfold tailWord_3220826
  simp only [CollatzResearch.WordTrace]
  refine ⟨29368293757376237533084583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78315450019669966754892221 29368293757376237533084583)
  ·
    refine ⟨44052440636064356299626875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29368293757376237533084583 44052440636064356299626875)
    ·
      refine ⟨66078660954096534449440313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44052440636064356299626875 66078660954096534449440313)
      ·
        refine ⟨49558995715572400837080235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66078660954096534449440313 49558995715572400837080235)
        ·
          refine ⟨74338493573358601255620353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49558995715572400837080235 74338493573358601255620353)
          ·
            refine ⟨55753870180018950941715265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74338493573358601255620353 55753870180018950941715265)
            ·
              refine ⟨41815402635014213206286449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55753870180018950941715265 41815402635014213206286449)
              ·
                refine ⟨31361551976260659904714837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41815402635014213206286449 31361551976260659904714837)
                ·
                  refine ⟨367518187221804608258377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31361551976260659904714837 367518187221804608258377)
                  ·
                    rfl

theorem cell22_3220826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_3220826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220826 prefixEnd_3220826 := by exact prefixLift 3220826
  have htrace : WordTrace (prefixWord ++ tailWord_3220826) baseStart_3220826 baseEnd_3220826 := by
    simpa [prefixWord, tailWord_3220826, baseEnd_3220826] using wordTrace_append hprefix tailTrace_3220826
  have hstable : (prefixWord ++ tailWord_3220826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220826).length < 2 ^ (prefixWord ++ tailWord_3220826).sum := by decide
  have hdescent : baseEnd_3220826 < baseStart_3220826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220841 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_3220841 : Nat := 118140960795 + 3220841 * 2 ^ 59
def prefixEnd_3220841 : Nat := 4983230072969 + 3 ^ 40 * 3220841 * 2
def baseEnd_3220841 : Nat := 1102559696471958785650085

theorem tailTrace_3220841 : CollatzResearch.WordTrace tailWord_3220841 prefixEnd_3220841 1102559696471958785650085 := by
  unfold tailWord_3220841
  simp only [CollatzResearch.WordTrace]
  refine ⟨117473722124450607694134377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78315814749633738462756251 117473722124450607694134377)
  ·
    refine ⟨88105291593337955770600783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117473722124450607694134377 88105291593337955770600783)
    ·
      refine ⟨132157937390006933655901175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88105291593337955770600783 132157937390006933655901175)
      ·
        refine ⟨198236906085010400483851763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132157937390006933655901175 198236906085010400483851763)
        ·
          refine ⟨297355359127515600725777645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198236906085010400483851763 297355359127515600725777645)
          ·
            refine ⟨111508259672818350272166617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297355359127515600725777645 111508259672818350272166617)
            ·
              refine ⟨83631194754613762704124963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111508259672818350272166617 83631194754613762704124963)
              ·
                refine ⟨125446792131920644056187445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83631194754613762704124963 125446792131920644056187445)
                ·
                  refine ⟨11760636762367560380267573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125446792131920644056187445 11760636762367560380267573)
                  ·
                    refine ⟨1102559696471958785650085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11760636762367560380267573 1102559696471958785650085)
                    ·
                      rfl

theorem cell22_3220841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_3220841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220841 prefixEnd_3220841 := by exact prefixLift 3220841
  have htrace : WordTrace (prefixWord ++ tailWord_3220841) baseStart_3220841 baseEnd_3220841 := by
    simpa [prefixWord, tailWord_3220841, baseEnd_3220841] using wordTrace_append hprefix tailTrace_3220841
  have hstable : (prefixWord ++ tailWord_3220841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220841).length < 2 ^ (prefixWord ++ tailWord_3220841).sum := by decide
  have hdescent : baseEnd_3220841 < baseStart_3220841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220888 : List Nat := [2, 1, 2, 5, 2, 10]
def baseStart_3220888 : Nat := 118140960795 + 3220888 * 2 ^ 59
def prefixEnd_3220888 : Nat := 4983230072969 + 3 ^ 40 * 3220888 * 2
def baseEnd_3220888 : Nat := 13612046734968720120061

theorem tailTrace_3220888 : CollatzResearch.WordTrace tailWord_3220888 prefixEnd_3220888 13612046734968720120061 := by
  unfold tailWord_3220888
  simp only [CollatzResearch.WordTrace]
  refine ⟨58737718177640167360547659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78316957570186889814063545 58737718177640167360547659)
  ·
    refine ⟨88106577266460251040821489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58737718177640167360547659 88106577266460251040821489)
    ·
      refine ⟨66079932949845188280616117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88106577266460251040821489 66079932949845188280616117)
      ·
        refine ⟨6194993714047986401307761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66079932949845188280616117 6194993714047986401307761)
        ·
          refine ⟨4646245285535989800980821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6194993714047986401307761 4646245285535989800980821)
          ·
            refine ⟨13612046734968720120061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4646245285535989800980821 13612046734968720120061)
            ·
              rfl

theorem cell22_3220888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 10].length) (baseStart_3220888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220888 prefixEnd_3220888 := by exact prefixLift 3220888
  have htrace : WordTrace (prefixWord ++ tailWord_3220888) baseStart_3220888 baseEnd_3220888 := by
    simpa [prefixWord, tailWord_3220888, baseEnd_3220888] using wordTrace_append hprefix tailTrace_3220888
  have hstable : (prefixWord ++ tailWord_3220888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220888).length < 2 ^ (prefixWord ++ tailWord_3220888).sum := by decide
  have hdescent : baseEnd_3220888 < baseStart_3220888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220894 : List Nat := [4, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3220894 : Nat := 118140960795 + 3220894 * 2 ^ 59
def prefixEnd_3220894 : Nat := 4983230072969 + 3 ^ 40 * 3220894 * 2
def baseEnd_3220894 : Nat := 367525946485028104691641

theorem tailTrace_3220894 : CollatzResearch.WordTrace tailWord_3220894 prefixEnd_3220894 367525946485028104691641 := by
  unfold tailWord_3220894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14684456899157324718226717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78317103462172398497209157 14684456899157324718226717)
  ·
    refine ⟨5506671337183996769335019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14684456899157324718226717 5506671337183996769335019)
    ·
      refine ⟨8260007005775995154002529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5506671337183996769335019 8260007005775995154002529)
      ·
        refine ⟨6195005254331996365501897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8260007005775995154002529 6195005254331996365501897)
        ·
          refine ⟨4646253940748997274126423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6195005254331996365501897 4646253940748997274126423)
          ·
            refine ⟨6969380911123495911189635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646253940748997274126423 6969380911123495911189635)
            ·
              refine ⟨10454071366685243866784453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6969380911123495911189635 10454071366685243866784453)
              ·
                refine ⟨1960138381253483225022085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10454071366685243866784453 1960138381253483225022085)
                ·
                  refine ⟨367525946485028104691641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1960138381253483225022085 367525946485028104691641)
                  ·
                    rfl

theorem cell22_3220894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3220894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220894 prefixEnd_3220894 := by exact prefixLift 3220894
  have htrace : WordTrace (prefixWord ++ tailWord_3220894) baseStart_3220894 baseEnd_3220894 := by
    simpa [prefixWord, tailWord_3220894, baseEnd_3220894] using wordTrace_append hprefix tailTrace_3220894
  have hstable : (prefixWord ++ tailWord_3220894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220894).length < 2 ^ (prefixWord ++ tailWord_3220894).sum := by decide
  have hdescent : baseEnd_3220894 < baseStart_3220894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220924 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 2, 4]
def baseStart_3220924 : Nat := 118140960795 + 3220924 * 2 ^ 59
def prefixEnd_3220924 : Nat := 4983230072969 + 3 ^ 40 * 3220924 * 2
def baseEnd_3220924 : Nat := 1102588109068174235824831

theorem tailTrace_3220924 : CollatzResearch.WordTrace tailWord_3220924 prefixEnd_3220924 1102588109068174235824831 := by
  unfold tailWord_3220924
  simp only [CollatzResearch.WordTrace]
  refine ⟨58738374691574956434702913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78317832922099941912937217 58738374691574956434702913)
  ·
    refine ⟨44053781018681217326027185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58738374691574956434702913 44053781018681217326027185)
    ·
      refine ⟨33040335764010912994520389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44053781018681217326027185 33040335764010912994520389)
      ·
        refine ⟨6195062955752046186472573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33040335764010912994520389 6195062955752046186472573)
        ·
          refine ⟨2323148608407017319927215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6195062955752046186472573 2323148608407017319927215)
          ·
            refine ⟨3484722912610525979890823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323148608407017319927215 3484722912610525979890823)
            ·
              refine ⟨5227084368915788969836235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484722912610525979890823 5227084368915788969836235)
              ·
                refine ⟨7840626553373683454754353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5227084368915788969836235 7840626553373683454754353)
                ·
                  refine ⟨5880469915030262591065765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7840626553373683454754353 5880469915030262591065765)
                  ·
                    refine ⟨1102588109068174235824831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5880469915030262591065765 1102588109068174235824831)
                    ·
                      rfl

theorem cell22_3220924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_3220924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220924 prefixEnd_3220924 := by exact prefixLift 3220924
  have htrace : WordTrace (prefixWord ++ tailWord_3220924) baseStart_3220924 baseEnd_3220924 := by
    simpa [prefixWord, tailWord_3220924, baseEnd_3220924] using wordTrace_append hprefix tailTrace_3220924
  have hstable : (prefixWord ++ tailWord_3220924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220924).length < 2 ^ (prefixWord ++ tailWord_3220924).sum := by decide
  have hdescent : baseEnd_3220924 < baseStart_3220924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3220930 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3220930 : Nat := 118140960795 + 3220930 * 2 ^ 59
def prefixEnd_3220930 : Nat := 4983230072969 + 3 ^ 40 * 3220930 * 2
def baseEnd_3220930 : Nat := 1102590162990792220174813

theorem tailTrace_3220930 : CollatzResearch.WordTrace tailWord_3220930 prefixEnd_3220930 1102590162990792220174813 := by
  unfold tailWord_3220930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29369242055282043973531061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78317978814085450596082829 29369242055282043973531061)
  ·
    refine ⟨2753366442682691622518537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29369242055282043973531061 2753366442682691622518537)
    ·
      refine ⟨2065024832012018716888903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2753366442682691622518537 2065024832012018716888903)
      ·
        refine ⟨3097537248018028075333355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2065024832012018716888903 3097537248018028075333355)
        ·
          refine ⟨4646305872027042113000033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097537248018028075333355 4646305872027042113000033)
          ·
            refine ⟨3484729404020281584750025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4646305872027042113000033 3484729404020281584750025)
            ·
              refine ⟨2613547053015211188562519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3484729404020281584750025 2613547053015211188562519)
              ·
                refine ⟨3920320579522816782843779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613547053015211188562519 3920320579522816782843779)
                ·
                  refine ⟨5880480869284225174265669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920320579522816782843779 5880480869284225174265669)
                  ·
                    refine ⟨1102590162990792220174813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5880480869284225174265669 1102590162990792220174813)
                    ·
                      rfl

theorem cell22_3220930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3220930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3220930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3220930 prefixEnd_3220930 := by exact prefixLift 3220930
  have htrace : WordTrace (prefixWord ++ tailWord_3220930) baseStart_3220930 baseEnd_3220930 := by
    simpa [prefixWord, tailWord_3220930, baseEnd_3220930] using wordTrace_append hprefix tailTrace_3220930
  have hstable : (prefixWord ++ tailWord_3220930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3220930).length < 2 ^ (prefixWord ++ tailWord_3220930).sum := by decide
  have hdescent : baseEnd_3220930 < baseStart_3220930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3220930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
