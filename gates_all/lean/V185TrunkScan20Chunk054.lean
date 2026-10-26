import V185TrunkScan20Chunk053

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_328408 : List Nat := [2, 1, 2, 2, 3, 2, 3, 5]
def baseStart_328408 : Nat := 118140960795 + 328408 * 2 ^ 59
def prefixEnd_328408 : Nat := 4983230072969 + 3 ^ 40 * 328408 * 2
def baseEnd_328408 : Nat := 49964786602031506930277

theorem tailTrace_328408 : CollatzResearch.WordTrace tailWord_328408 prefixEnd_328408 49964786602031506930277 := by
  unfold tailWord_328408
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989011897120689233072939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7985349196160918977430585 5989011897120689233072939)
  ·
    refine ⟨8983517845681033849609409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5989011897120689233072939 8983517845681033849609409)
    ·
      refine ⟨6737638384260775387207057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8983517845681033849609409 6737638384260775387207057)
      ·
        refine ⟨5053228788195581540405293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6737638384260775387207057 5053228788195581540405293)
        ·
          refine ⟨1894960795573343077651985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5053228788195581540405293 1894960795573343077651985)
          ·
            refine ⟨1421220596680007308238989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1894960795573343077651985 1421220596680007308238989)
            ·
              refine ⟨532957723755002740589621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1421220596680007308238989 532957723755002740589621)
              ·
                refine ⟨49964786602031506930277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 532957723755002740589621 49964786602031506930277)
                ·
                  rfl

theorem cell20_328408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_328408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328408 prefixEnd_328408 := by exact prefixLift 328408
  have htrace : WordTrace (prefixWord ++ tailWord_328408) baseStart_328408 baseEnd_328408 := by
    simpa [prefixWord, tailWord_328408, baseEnd_328408] using wordTrace_append hprefix tailTrace_328408
  have hstable : (prefixWord ++ tailWord_328408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328408).length < 2 ^ (prefixWord ++ tailWord_328408).sum := by decide
  have hdescent : baseEnd_328408 < baseStart_328408 := by decide
  rcases family_descends (prefixWord ++ tailWord_328408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328456 : List Nat := [2, 1, 3, 2, 2, 2, 2, 4, 2]
def baseStart_328456 : Nat := 118140960795 + 328456 * 2 ^ 59
def prefixEnd_328456 : Nat := 4983230072969 + 3 ^ 40 * 328456 * 2
def baseEnd_328456 : Nat := 149916268314019687190635

theorem tailTrace_328456 : CollatzResearch.WordTrace tailWord_328456 prefixEnd_328456 149916268314019687190635 := by
  unfold tailWord_328456
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989887249033741331946611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7986516332044988442595481 5989887249033741331946611)
  ·
    refine ⟨8984830873550611997919917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5989887249033741331946611 8984830873550611997919917)
    ·
      refine ⟨3369311577581479499219969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8984830873550611997919917 3369311577581479499219969)
      ·
        refine ⟨2526983683186109624414977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3369311577581479499219969 2526983683186109624414977)
        ·
          refine ⟨1895237762389582218311233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2526983683186109624414977 1895237762389582218311233)
          ·
            refine ⟨1421428321792186663733425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895237762389582218311233 1421428321792186663733425)
            ·
              refine ⟨1066071241344139997800069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421428321792186663733425 1066071241344139997800069)
              ·
                refine ⟨199888357752026249587513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1066071241344139997800069 199888357752026249587513)
                ·
                  refine ⟨149916268314019687190635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199888357752026249587513 149916268314019687190635)
                  ·
                    rfl

theorem cell20_328456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_328456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328456 prefixEnd_328456 := by exact prefixLift 328456
  have htrace : WordTrace (prefixWord ++ tailWord_328456) baseStart_328456 baseEnd_328456 := by
    simpa [prefixWord, tailWord_328456, baseEnd_328456] using wordTrace_append hprefix tailTrace_328456
  have hstable : (prefixWord ++ tailWord_328456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328456).length < 2 ^ (prefixWord ++ tailWord_328456).sum := by decide
  have hdescent : baseEnd_328456 < baseStart_328456 := by decide
  rcases family_descends (prefixWord ++ tailWord_328456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328467 : List Nat := [1, 1, 1, 2, 1, 3, 4, 7]
def baseStart_328467 : Nat := 118140960795 + 328467 * 2 ^ 59
def prefixEnd_328467 : Nat := 4983230072969 + 3 ^ 40 * 328467 * 2
def baseEnd_328467 : Nat := 49973763004584179274641

theorem tailTrace_328467 : CollatzResearch.WordTrace tailWord_328467 prefixEnd_328467 49973763004584179274641 := by
  unfold tailWord_328467
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980175701027631542543655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7986783800685087695029103 11980175701027631542543655)
  ·
    refine ⟨17970263551541447313815483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11980175701027631542543655 17970263551541447313815483)
    ·
      refine ⟨26955395327312170970723225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17970263551541447313815483 26955395327312170970723225)
      ·
        refine ⟨20216546495484128228042419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26955395327312170970723225 20216546495484128228042419)
        ·
          refine ⟨30324819743226192342063629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20216546495484128228042419 30324819743226192342063629)
          ·
            refine ⟨11371807403709822128273861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30324819743226192342063629 11371807403709822128273861)
            ·
              refine ⟨2132213888195591649051349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11371807403709822128273861 2132213888195591649051349)
              ·
                refine ⟨49973763004584179274641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2132213888195591649051349 49973763004584179274641)
                ·
                  rfl

theorem cell20_328467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_328467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328467 prefixEnd_328467 := by exact prefixLift 328467
  have htrace : WordTrace (prefixWord ++ tailWord_328467) baseStart_328467 baseEnd_328467 := by
    simpa [prefixWord, tailWord_328467, baseEnd_328467] using wordTrace_append hprefix tailTrace_328467
  have hstable : (prefixWord ++ tailWord_328467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328467).length < 2 ^ (prefixWord ++ tailWord_328467).sum := by decide
  have hdescent : baseEnd_328467 < baseStart_328467 := by decide
  rcases family_descends (prefixWord ++ tailWord_328467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328511 : List Nat := [1, 1, 2, 2, 5, 2, 3, 2, 2]
def baseStart_328511 : Nat := 118140960795 + 328511 * 2 ^ 59
def prefixEnd_328511 : Nat := 4983230072969 + 3 ^ 40 * 328511 * 2
def baseEnd_328511 : Nat := 149941371812683940357077

theorem tailTrace_328511 : CollatzResearch.WordTrace tailWord_328511 prefixEnd_328511 149941371812683940357077 := by
  unfold tailWord_328511
  simp only [CollatzResearch.WordTrace]
  refine ⟨11981780512868227057145387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7987853675245484704763591 11981780512868227057145387)
  ·
    refine ⟨17972670769302340585718081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11981780512868227057145387 17972670769302340585718081)
    ·
      refine ⟨13479503076976755439288561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17972670769302340585718081 13479503076976755439288561)
      ·
        refine ⟨10109627307732566579466421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13479503076976755439288561 10109627307732566579466421)
        ·
          refine ⟨947777560099928116824977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10109627307732566579466421 947777560099928116824977)
          ·
            refine ⟨710833170074946087618733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 947777560099928116824977 710833170074946087618733)
            ·
              refine ⟨266562438778104782857025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 710833170074946087618733 266562438778104782857025)
              ·
                refine ⟨199921829083578587142769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266562438778104782857025 199921829083578587142769)
                ·
                  refine ⟨149941371812683940357077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199921829083578587142769 149941371812683940357077)
                  ·
                    rfl

theorem cell20_328511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 2].length) (baseStart_328511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328511 prefixEnd_328511 := by exact prefixLift 328511
  have htrace : WordTrace (prefixWord ++ tailWord_328511) baseStart_328511 baseEnd_328511 := by
    simpa [prefixWord, tailWord_328511, baseEnd_328511] using wordTrace_append hprefix tailTrace_328511
  have hstable : (prefixWord ++ tailWord_328511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328511).length < 2 ^ (prefixWord ++ tailWord_328511).sum := by decide
  have hdescent : baseEnd_328511 < baseStart_328511 := by decide
  rcases family_descends (prefixWord ++ tailWord_328511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328536 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_328536 : Nat := 118140960795 + 328536 * 2 ^ 59
def prefixEnd_328536 : Nat := 4983230072969 + 3 ^ 40 * 328536 * 2
def baseEnd_328536 : Nat := 149952782493894964523641

theorem tailTrace_328536 : CollatzResearch.WordTrace tailWord_328536 prefixEnd_328536 149952782493894964523641 := by
  unfold tailWord_328536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5991346168888828163402731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7988461558518437551203641 5991346168888828163402731)
  ·
    refine ⟨8987019253333242245104097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5991346168888828163402731 8987019253333242245104097)
    ·
      refine ⟨6740264439999931683828073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8987019253333242245104097 6740264439999931683828073)
      ·
        refine ⟨5055198329999948762871055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6740264439999931683828073 5055198329999948762871055)
        ·
          refine ⟨7582797494999923144306583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5055198329999948762871055 7582797494999923144306583)
          ·
            refine ⟨11374196242499884716459875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7582797494999923144306583 11374196242499884716459875)
            ·
              refine ⟨17061294363749827074689813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11374196242499884716459875 17061294363749827074689813)
              ·
                refine ⟨799748173300773144126085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17061294363749827074689813 799748173300773144126085)
                ·
                  refine ⟨149952782493894964523641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 799748173300773144126085 149952782493894964523641)
                  ·
                    rfl

theorem cell20_328536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_328536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328536 prefixEnd_328536 := by exact prefixLift 328536
  have htrace : WordTrace (prefixWord ++ tailWord_328536) baseStart_328536 baseEnd_328536 := by
    simpa [prefixWord, tailWord_328536, baseEnd_328536] using wordTrace_append hprefix tailTrace_328536
  have hstable : (prefixWord ++ tailWord_328536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328536).length < 2 ^ (prefixWord ++ tailWord_328536).sum := by decide
  have hdescent : baseEnd_328536 < baseStart_328536 := by decide
  rcases family_descends (prefixWord ++ tailWord_328536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328543 : List Nat := [1, 1, 2, 3, 1, 3, 1, 8]
def baseStart_328543 : Nat := 118140960795 + 328543 * 2 ^ 59
def prefixEnd_328543 : Nat := 4983230072969 + 3 ^ 40 * 328543 * 2
def baseEnd_328543 : Nat := 49985325828211350430093

theorem tailTrace_328543 : CollatzResearch.WordTrace tailWord_328543 prefixEnd_328543 49985325828211350430093 := by
  unfold tailWord_328543
  simp only [CollatzResearch.WordTrace]
  refine ⟨11982947648752296522310283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7988631765834864348206855 11982947648752296522310283)
  ·
    refine ⟨17974421473128444783465425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11982947648752296522310283 17974421473128444783465425)
    ·
      refine ⟨13480816104846333587599069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17974421473128444783465425 13480816104846333587599069)
      ·
        refine ⟨5055306039317375095349651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13480816104846333587599069 5055306039317375095349651)
        ·
          refine ⟨7582959058976062643024477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5055306039317375095349651 7582959058976062643024477)
          ·
            refine ⟨2843609647116023491134179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7582959058976062643024477 2843609647116023491134179)
            ·
              refine ⟨4265414470674035236701269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843609647116023491134179 4265414470674035236701269)
              ·
                refine ⟨49985325828211350430093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4265414470674035236701269 49985325828211350430093)
                ·
                  rfl

theorem cell20_328543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_328543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328543 prefixEnd_328543 := by exact prefixLift 328543
  have htrace : WordTrace (prefixWord ++ tailWord_328543) baseStart_328543 baseEnd_328543 := by
    simpa [prefixWord, tailWord_328543, baseEnd_328543] using wordTrace_append hprefix tailTrace_328543
  have hstable : (prefixWord ++ tailWord_328543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328543).length < 2 ^ (prefixWord ++ tailWord_328543).sum := by decide
  have hdescent : baseEnd_328543 < baseStart_328543 := by decide
  rcases family_descends (prefixWord ++ tailWord_328543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328566 : List Nat := [5, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_328566 : Nat := 118140960795 + 328566 * 2 ^ 59
def prefixEnd_328566 : Nat := 4983230072969 + 3 ^ 40 * 328566 * 2
def baseEnd_328566 : Nat := 149966475311348193523519

theorem tailTrace_328566 : CollatzResearch.WordTrace tailWord_328566 prefixEnd_328566 149966475311348193523519 := by
  unfold tailWord_328566
  simp only [CollatzResearch.WordTrace]
  refine ⟨748986657979310715649847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7989191018445980966931701 748986657979310715649847)
  ·
    refine ⟨1123479986968966073474771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748986657979310715649847 1123479986968966073474771)
    ·
      refine ⟨1685219980453449110212157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123479986968966073474771 1685219980453449110212157)
      ·
        refine ⟨631957492670043416329559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1685219980453449110212157 631957492670043416329559)
        ·
          refine ⟨947936239005065124494339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631957492670043416329559 947936239005065124494339)
          ·
            refine ⟨1421904358507597686741509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947936239005065124494339 1421904358507597686741509)
            ·
              refine ⟨266607067220174566264033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1421904358507597686741509 266607067220174566264033)
              ·
                refine ⟨199955300415130924698025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266607067220174566264033 199955300415130924698025)
                ·
                  refine ⟨149966475311348193523519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199955300415130924698025 149966475311348193523519)
                  ·
                    rfl

theorem cell20_328566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_328566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328566 prefixEnd_328566 := by exact prefixLift 328566
  have htrace : WordTrace (prefixWord ++ tailWord_328566) baseStart_328566 baseEnd_328566 := by
    simpa [prefixWord, tailWord_328566, baseEnd_328566] using wordTrace_append hprefix tailTrace_328566
  have hstable : (prefixWord ++ tailWord_328566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328566).length < 2 ^ (prefixWord ++ tailWord_328566).sum := by decide
  have hdescent : baseEnd_328566 < baseStart_328566 := by decide
  rcases family_descends (prefixWord ++ tailWord_328566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328584 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_328584 : Nat := 118140960795 + 328584 * 2 ^ 59
def prefixEnd_328584 : Nat := 4983230072969 + 3 ^ 40 * 328584 * 2
def baseEnd_328584 : Nat := 149974691001820130923445

theorem tailTrace_328584 : CollatzResearch.WordTrace tailWord_328584 prefixEnd_328584 149974691001820130923445 := by
  unfold tailWord_328584
  simp only [CollatzResearch.WordTrace]
  refine ⟨5992221520801880262276403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7989628694402507016368537 5992221520801880262276403)
  ·
    refine ⟨8988332281202820393414605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5992221520801880262276403 8988332281202820393414605)
    ·
      refine ⟨3370624605451057647530477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8988332281202820393414605 3370624605451057647530477)
      ·
        refine ⟨1263984227044146617823929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3370624605451057647530477 1263984227044146617823929)
        ·
          refine ⟨947988170283109963367947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1263984227044146617823929 947988170283109963367947)
          ·
            refine ⟨1421982255424664945051921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947988170283109963367947 1421982255424664945051921)
            ·
              refine ⟨1066486691568498708788941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421982255424664945051921 1066486691568498708788941)
              ·
                refine ⟨399932509338187015795853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1066486691568498708788941 399932509338187015795853)
                ·
                  refine ⟨149974691001820130923445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 399932509338187015795853 149974691001820130923445)
                  ·
                    rfl

theorem cell20_328584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_328584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328584 prefixEnd_328584 := by exact prefixLift 328584
  have htrace : WordTrace (prefixWord ++ tailWord_328584) baseStart_328584 baseEnd_328584 := by
    simpa [prefixWord, tailWord_328584, baseEnd_328584] using wordTrace_append hprefix tailTrace_328584
  have hstable : (prefixWord ++ tailWord_328584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328584).length < 2 ^ (prefixWord ++ tailWord_328584).sum := by decide
  have hdescent : baseEnd_328584 < baseStart_328584 := by decide
  rcases family_descends (prefixWord ++ tailWord_328584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328594 : List Nat := [3, 2, 3, 2, 2, 1, 3, 4]
def baseStart_328594 : Nat := 118140960795 + 328594 * 2 ^ 59
def prefixEnd_328594 : Nat := 4983230072969 + 3 ^ 40 * 328594 * 2
def baseEnd_328594 : Nat := 49993085091434846863357

theorem tailTrace_328594 : CollatzResearch.WordTrace tailWord_328594 prefixEnd_328594 49993085091434846863357 := by
  unfold tailWord_328594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2996201942891883058104209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7989871847711688154944557 2996201942891883058104209)
  ·
    refine ⟨2247151457168912293578157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2996201942891883058104209 2247151457168912293578157)
    ·
      refine ⟨842681796438342110091809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2247151457168912293578157 842681796438342110091809)
      ·
        refine ⟨632011347328756582568857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 842681796438342110091809 632011347328756582568857)
        ·
          refine ⟨474008510496567436926643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632011347328756582568857 474008510496567436926643)
          ·
            refine ⟨711012765744851155389965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474008510496567436926643 711012765744851155389965)
            ·
              refine ⟨266629787154319183271237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711012765744851155389965 266629787154319183271237)
              ·
                refine ⟨49993085091434846863357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266629787154319183271237 49993085091434846863357)
                ·
                  rfl

theorem cell20_328594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_328594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328594 prefixEnd_328594 := by exact prefixLift 328594
  have htrace : WordTrace (prefixWord ++ tailWord_328594) baseStart_328594 baseEnd_328594 := by
    simpa [prefixWord, tailWord_328594, baseEnd_328594] using wordTrace_append hprefix tailTrace_328594
  have hstable : (prefixWord ++ tailWord_328594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328594).length < 2 ^ (prefixWord ++ tailWord_328594).sum := by decide
  have hdescent : baseEnd_328594 < baseStart_328594 := by decide
  rcases family_descends (prefixWord ++ tailWord_328594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328605 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_328605 : Nat := 118140960795 + 328605 * 2 ^ 59
def prefixEnd_328605 : Nat := 4983230072969 + 3 ^ 40 * 328605 * 2
def baseEnd_328605 : Nat := 149984275974037391223359

theorem tailTrace_328605 : CollatzResearch.WordTrace tailWord_328605 prefixEnd_328605 149984275974037391223359 := by
  unfold tailWord_328605
  simp only [CollatzResearch.WordTrace]
  refine ⟨11985208974527681111067269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7990139316351787407378179 11985208974527681111067269)
  ·
    refine ⟨2247226682723940208325113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11985208974527681111067269 2247226682723940208325113)
    ·
      refine ⟨1685420012042955156243835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2247226682723940208325113 1685420012042955156243835)
      ·
        refine ⟨2528130018064432734365753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685420012042955156243835 2528130018064432734365753)
        ·
          refine ⟨1896097513548324550774315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2528130018064432734365753 1896097513548324550774315)
          ·
            refine ⟨2844146270322486826161473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896097513548324550774315 2844146270322486826161473)
            ·
              refine ⟨2133109702741865119621105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2844146270322486826161473 2133109702741865119621105)
              ·
                refine ⟨1599832277056398839715829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133109702741865119621105 1599832277056398839715829)
                ·
                  refine ⟨149984275974037391223359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1599832277056398839715829 149984275974037391223359)
                  ·
                    rfl

theorem cell20_328605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_328605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328605 prefixEnd_328605 := by exact prefixLift 328605
  have htrace : WordTrace (prefixWord ++ tailWord_328605) baseStart_328605 baseEnd_328605 := by
    simpa [prefixWord, tailWord_328605, baseEnd_328605] using wordTrace_append hprefix tailTrace_328605
  have hstable : (prefixWord ++ tailWord_328605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328605).length < 2 ^ (prefixWord ++ tailWord_328605).sum := by decide
  have hdescent : baseEnd_328605 < baseStart_328605 := by decide
  rcases family_descends (prefixWord ++ tailWord_328605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328612 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_328612 : Nat := 118140960795 + 328612 * 2 ^ 59
def prefixEnd_328612 : Nat := 4983230072969 + 3 ^ 40 * 328612 * 2
def baseEnd_328612 : Nat := 149987470964776477989997

theorem tailTrace_328612 : CollatzResearch.WordTrace tailWord_328612 prefixEnd_328612 149987470964776477989997 := by
  unfold tailWord_328612
  simp only [CollatzResearch.WordTrace]
  refine ⟨5992732142751160653286045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7990309523668214204381393 5992732142751160653286045)
  ·
    refine ⟨2247274553531685244982267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5992732142751160653286045 2247274553531685244982267)
    ·
      refine ⟨3370911830297527867473401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2247274553531685244982267 3370911830297527867473401)
      ·
        refine ⟨2528183872723145900605051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3370911830297527867473401 2528183872723145900605051)
        ·
          refine ⟨3792275809084718850907577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528183872723145900605051 3792275809084718850907577)
          ·
            refine ⟨2844206856813539138180683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3792275809084718850907577 2844206856813539138180683)
            ·
              refine ⟨4266310285220308707271025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844206856813539138180683 4266310285220308707271025)
              ·
                refine ⟨3199732713915231530453269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4266310285220308707271025 3199732713915231530453269)
                ·
                  refine ⟨149987470964776477989997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3199732713915231530453269 149987470964776477989997)
                  ·
                    rfl

theorem cell20_328612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_328612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328612 prefixEnd_328612 := by exact prefixLift 328612
  have htrace : WordTrace (prefixWord ++ tailWord_328612) baseStart_328612 baseEnd_328612 := by
    simpa [prefixWord, tailWord_328612, baseEnd_328612] using wordTrace_append hprefix tailTrace_328612
  have hstable : (prefixWord ++ tailWord_328612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328612).length < 2 ^ (prefixWord ++ tailWord_328612).sum := by decide
  have hdescent : baseEnd_328612 < baseStart_328612 := by decide
  rcases family_descends (prefixWord ++ tailWord_328612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328629 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_328629 : Nat := 118140960795 + 328629 * 2 ^ 59
def prefixEnd_328629 : Nat := 4983230072969 + 3 ^ 40 * 328629 * 2
def baseEnd_328629 : Nat := 149995230227999974423261

theorem tailTrace_328629 : CollatzResearch.WordTrace tailWord_328629 prefixEnd_328629 149995230227999974423261 := by
  unfold tailWord_328629
  simp only [CollatzResearch.WordTrace]
  refine ⟨11986084326440733209940941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7990722884293822139960627 11986084326440733209940941)
  ·
    refine ⟨4494781622415274953727853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11986084326440733209940941 4494781622415274953727853)
    ·
      refine ⟨1685543108405728107647945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4494781622415274953727853 1685543108405728107647945)
      ·
        refine ⟨1264157331304296080735959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1685543108405728107647945 1264157331304296080735959)
        ·
          refine ⟨1896235996956444121103939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264157331304296080735959 1896235996956444121103939)
          ·
            refine ⟨2844353995434666181655909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896235996956444121103939 2844353995434666181655909)
            ·
              refine ⟨533316374143999909060483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2844353995434666181655909 533316374143999909060483)
              ·
                refine ⟨799974561215999863590725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533316374143999909060483 799974561215999863590725)
                ·
                  refine ⟨149995230227999974423261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 799974561215999863590725 149995230227999974423261)
                  ·
                    rfl

theorem cell20_328629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_328629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328629 prefixEnd_328629 := by exact prefixLift 328629
  have htrace : WordTrace (prefixWord ++ tailWord_328629) baseStart_328629 baseEnd_328629 := by
    simpa [prefixWord, tailWord_328629, baseEnd_328629] using wordTrace_append hprefix tailTrace_328629
  have hstable : (prefixWord ++ tailWord_328629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328629).length < 2 ^ (prefixWord ++ tailWord_328629).sum := by decide
  have hdescent : baseEnd_328629 < baseStart_328629 := by decide
  rcases family_descends (prefixWord ++ tailWord_328629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328657 : List Nat := [1, 2, 2, 1, 2, 1, 5, 6]
def baseStart_328657 : Nat := 118140960795 + 328657 * 2 ^ 59
def prefixEnd_328657 : Nat := 4983230072969 + 3 ^ 40 * 328657 * 2
def baseEnd_328657 : Nat := 50002670063652107163271

theorem tailTrace_328657 : CollatzResearch.WordTrace tailWord_328657 prefixEnd_328657 50002670063652107163271 := by
  unfold tailWord_328657
  simp only [CollatzResearch.WordTrace]
  refine ⟨11987105570339293991960225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7991403713559529327973483 11987105570339293991960225)
  ·
    refine ⟨8990329177754470493970169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11987105570339293991960225 8990329177754470493970169)
    ·
      refine ⟨6742746883315852870477627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8990329177754470493970169 6742746883315852870477627)
      ·
        refine ⟨10114120324973779305716441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6742746883315852870477627 10114120324973779305716441)
        ·
          refine ⟨7585590243730334479287331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10114120324973779305716441 7585590243730334479287331)
          ·
            refine ⟨11378385365595501718930997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7585590243730334479287331 11378385365595501718930997)
            ·
              refine ⟨1066723628024578286149781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11378385365595501718930997 1066723628024578286149781)
              ·
                refine ⟨50002670063652107163271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1066723628024578286149781 50002670063652107163271)
                ·
                  rfl

theorem cell20_328657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_328657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328657 prefixEnd_328657 := by exact prefixLift 328657
  have htrace : WordTrace (prefixWord ++ tailWord_328657) baseStart_328657 baseEnd_328657 := by
    simpa [prefixWord, tailWord_328657, baseEnd_328657] using wordTrace_append hprefix tailTrace_328657
  have hstable : (prefixWord ++ tailWord_328657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328657).length < 2 ^ (prefixWord ++ tailWord_328657).sum := by decide
  have hdescent : baseEnd_328657 < baseStart_328657 := by decide
  rcases family_descends (prefixWord ++ tailWord_328657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328694 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_328694 : Nat := 118140960795 + 328694 * 2 ^ 59
def prefixEnd_328694 : Nat := 4983230072969 + 3 ^ 40 * 328694 * 2
def baseEnd_328694 : Nat := 150024897999148637256329

theorem tailTrace_328694 : CollatzResearch.WordTrace tailWord_328694 prefixEnd_328694 150024897999148637256329 := by
  unfold tailWord_328694
  simp only [CollatzResearch.WordTrace]
  refine ⟨749278441950328081941071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7992303380803499540704757 749278441950328081941071)
  ·
    refine ⟨1123917662925492122911607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 749278441950328081941071 1123917662925492122911607)
    ·
      refine ⟨1685876494388238184367411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123917662925492122911607 1685876494388238184367411)
      ·
        refine ⟨2528814741582357276551117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685876494388238184367411 2528814741582357276551117)
        ·
          refine ⟨948305528093383978706669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2528814741582357276551117 948305528093383978706669)
          ·
            refine ⟨355614573035018992015001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 948305528093383978706669 355614573035018992015001)
            ·
              refine ⟨266710929776264244011251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355614573035018992015001 266710929776264244011251)
              ·
                refine ⟨400066394664396366016877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266710929776264244011251 400066394664396366016877)
                ·
                  refine ⟨150024897999148637256329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400066394664396366016877 150024897999148637256329)
                  ·
                    rfl

theorem cell20_328694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_328694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328694 prefixEnd_328694 := by exact prefixLift 328694
  have htrace : WordTrace (prefixWord ++ tailWord_328694) baseStart_328694 baseEnd_328694 := by
    simpa [prefixWord, tailWord_328694, baseEnd_328694] using wordTrace_append hprefix tailTrace_328694
  have hstable : (prefixWord ++ tailWord_328694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328694).length < 2 ^ (prefixWord ++ tailWord_328694).sum := by decide
  have hdescent : baseEnd_328694 < baseStart_328694 := by decide
  rcases family_descends (prefixWord ++ tailWord_328694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328733 : List Nat := [1, 4, 2, 2, 11]
def baseStart_328733 : Nat := 118140960795 + 328733 * 2 ^ 59
def prefixEnd_328733 : Nat := 4983230072969 + 3 ^ 40 * 328733 * 2
def baseEnd_328733 : Nat := 1852378995825158456249

theorem tailTrace_328733 : CollatzResearch.WordTrace tailWord_328733 prefixEnd_328733 1852378995825158456249 := by
  unfold tailWord_328733
  simp only [CollatzResearch.WordTrace]
  refine ⟨11989877518063958971726853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7993251678709305981151235 11989877518063958971726853)
  ·
    refine ⟨2248102034636992307198785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11989877518063958971726853 2248102034636992307198785)
    ·
      refine ⟨1686076525977744230399089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2248102034636992307198785 1686076525977744230399089)
      ·
        refine ⟨1264557394483308172799317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1686076525977744230399089 1264557394483308172799317)
        ·
          refine ⟨1852378995825158456249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1264557394483308172799317 1852378995825158456249)
          ·
            rfl

theorem cell20_328733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 11].length) (baseStart_328733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328733 prefixEnd_328733 := by exact prefixLift 328733
  have htrace : WordTrace (prefixWord ++ tailWord_328733) baseStart_328733 baseEnd_328733 := by
    simpa [prefixWord, tailWord_328733, baseEnd_328733] using wordTrace_append hprefix tailTrace_328733
  have hstable : (prefixWord ++ tailWord_328733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328733).length < 2 ^ (prefixWord ++ tailWord_328733).sum := by decide
  have hdescent : baseEnd_328733 < baseStart_328733 := by decide
  rcases family_descends (prefixWord ++ tailWord_328733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328739 : List Nat := [1, 1, 1, 4, 3, 4, 2, 2, 2]
def baseStart_328739 : Nat := 118140960795 + 328739 * 2 ^ 59
def prefixEnd_328739 : Nat := 4983230072969 + 3 ^ 40 * 328739 * 2
def baseEnd_328739 : Nat := 150045437225328480756145

theorem tailTrace_328739 : CollatzResearch.WordTrace tailWord_328739 prefixEnd_328739 150045437225328480756145 := by
  unfold tailWord_328739
  simp only [CollatzResearch.WordTrace]
  refine ⟨11990096356042221996445271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7993397570694814664296847 11990096356042221996445271)
  ·
    refine ⟨17985144534063332994667907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11990096356042221996445271 17985144534063332994667907)
    ·
      refine ⟨26977716801094999492001861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17985144534063332994667907 26977716801094999492001861)
      ·
        refine ⟨5058321900205312404750349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26977716801094999492001861 5058321900205312404750349)
        ·
          refine ⟨1896870712576992151781381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5058321900205312404750349 1896870712576992151781381)
          ·
            refine ⟨355663258608186028459009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1896870712576992151781381 355663258608186028459009)
            ·
              refine ⟨266747443956139521344257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355663258608186028459009 266747443956139521344257)
              ·
                refine ⟨200060582967104641008193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266747443956139521344257 200060582967104641008193)
                ·
                  refine ⟨150045437225328480756145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200060582967104641008193 150045437225328480756145)
                  ·
                    rfl

theorem cell20_328739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 2].length) (baseStart_328739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328739 prefixEnd_328739 := by exact prefixLift 328739
  have htrace : WordTrace (prefixWord ++ tailWord_328739) baseStart_328739 baseEnd_328739 := by
    simpa [prefixWord, tailWord_328739, baseEnd_328739] using wordTrace_append hprefix tailTrace_328739
  have hstable : (prefixWord ++ tailWord_328739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328739).length < 2 ^ (prefixWord ++ tailWord_328739).sum := by decide
  have hdescent : baseEnd_328739 < baseStart_328739 := by decide
  rcases family_descends (prefixWord ++ tailWord_328739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328746 : List Nat := [3, 1, 4, 1, 4, 1, 1, 5]
def baseStart_328746 : Nat := 118140960795 + 328746 * 2 ^ 59
def prefixEnd_328746 : Nat := 4983230072969 + 3 ^ 40 * 328746 * 2
def baseEnd_328746 : Nat := 50016210738689189174261

theorem tailTrace_328746 : CollatzResearch.WordTrace tailWord_328746 prefixEnd_328746 50016210738689189174261 := by
  unfold tailWord_328746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997587916754215547987523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7993567778011241461300061 2997587916754215547987523)
  ·
    refine ⟨4496381875131323321981285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2997587916754215547987523 4496381875131323321981285)
    ·
      refine ⟨843071601587123122871491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4496381875131323321981285 843071601587123122871491)
      ·
        refine ⟨1264607402380684684307237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843071601587123122871491 1264607402380684684307237)
        ·
          refine ⟨237113887946378378307607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1264607402380684684307237 237113887946378378307607)
          ·
            refine ⟨355670831919567567461411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237113887946378378307607 355670831919567567461411)
            ·
              refine ⟨533506247879351351192117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355670831919567567461411 533506247879351351192117)
              ·
                refine ⟨50016210738689189174261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 533506247879351351192117 50016210738689189174261)
                ·
                  rfl

theorem cell20_328746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_328746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328746 prefixEnd_328746 := by exact prefixLift 328746
  have htrace : WordTrace (prefixWord ++ tailWord_328746) baseStart_328746 baseEnd_328746 := by
    simpa [prefixWord, tailWord_328746, baseEnd_328746] using wordTrace_append hprefix tailTrace_328746
  have hstable : (prefixWord ++ tailWord_328746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328746).length < 2 ^ (prefixWord ++ tailWord_328746).sum := by decide
  have hdescent : baseEnd_328746 < baseStart_328746 := by decide
  rcases family_descends (prefixWord ++ tailWord_328746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328764 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_328764 : Nat := 118140960795 + 328764 * 2 ^ 59
def prefixEnd_328764 : Nat := 4983230072969 + 3 ^ 40 * 328764 * 2
def baseEnd_328764 : Nat := 150056847906539504922709

theorem tailTrace_328764 : CollatzResearch.WordTrace tailWord_328764 prefixEnd_328764 150056847906539504922709 := by
  unfold tailWord_328764
  simp only [CollatzResearch.WordTrace]
  refine ⟨5995504090475825633052673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7994005453967767510736897 5995504090475825633052673)
  ·
    refine ⟨4496628067856869224789505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5995504090475825633052673 4496628067856869224789505)
    ·
      refine ⟨3372471050892651918592129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4496628067856869224789505 3372471050892651918592129)
      ·
        refine ⟨2529353288169488938944097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3372471050892651918592129 2529353288169488938944097)
        ·
          refine ⟨1897014966127116704208073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2529353288169488938944097 1897014966127116704208073)
          ·
            refine ⟨1422761224595337528156055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897014966127116704208073 1422761224595337528156055)
            ·
              refine ⟨2134141836893006292234083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422761224595337528156055 2134141836893006292234083)
              ·
                refine ⟨3201212755339509438351125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134141836893006292234083 3201212755339509438351125)
                ·
                  refine ⟨150056847906539504922709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3201212755339509438351125 150056847906539504922709)
                  ·
                    rfl

theorem cell20_328764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_328764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328764 prefixEnd_328764 := by exact prefixLift 328764
  have htrace : WordTrace (prefixWord ++ tailWord_328764) baseStart_328764 baseEnd_328764 := by
    simpa [prefixWord, tailWord_328764, baseEnd_328764] using wordTrace_append hprefix tailTrace_328764
  have hstable : (prefixWord ++ tailWord_328764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328764).length < 2 ^ (prefixWord ++ tailWord_328764).sum := by decide
  have hdescent : baseEnd_328764 < baseStart_328764 := by decide
  rcases family_descends (prefixWord ++ tailWord_328764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328808 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 3]
def baseStart_328808 : Nat := 118140960795 + 328808 * 2 ^ 59
def prefixEnd_328808 : Nat := 4983230072969 + 3 ^ 40 * 328808 * 2
def baseEnd_328808 : Nat := 150076930705470907455863

theorem tailTrace_328808 : CollatzResearch.WordTrace tailWord_328808 prefixEnd_328808 150076930705470907455863 := by
  unfold tailWord_328808
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996306496396123390353539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7995075328528164520471385 5996306496396123390353539)
  ·
    refine ⟨8994459744594185085530309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5996306496396123390353539 8994459744594185085530309)
    ·
      refine ⟨1686461202111409703536933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8994459744594185085530309 1686461202111409703536933)
      ·
        refine ⟨316211475395889319413175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1686461202111409703536933 316211475395889319413175)
        ·
          refine ⟨474317213093833979119763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316211475395889319413175 474317213093833979119763)
          ·
            refine ⟨711475819640750968679645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474317213093833979119763 711475819640750968679645)
            ·
              refine ⟨266803432365281613254867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711475819640750968679645 266803432365281613254867)
              ·
                refine ⟨400205148547922419882301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266803432365281613254867 400205148547922419882301)
                ·
                  refine ⟨150076930705470907455863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400205148547922419882301 150076930705470907455863)
                  ·
                    rfl

theorem cell20_328808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_328808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328808 prefixEnd_328808 := by exact prefixLift 328808
  have htrace : WordTrace (prefixWord ++ tailWord_328808) baseStart_328808 baseEnd_328808 := by
    simpa [prefixWord, tailWord_328808, baseEnd_328808] using wordTrace_append hprefix tailTrace_328808
  have hstable : (prefixWord ++ tailWord_328808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328808).length < 2 ^ (prefixWord ++ tailWord_328808).sum := by decide
  have hdescent : baseEnd_328808 < baseStart_328808 := by decide
  rcases family_descends (prefixWord ++ tailWord_328808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328812 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 3]
def baseStart_328812 : Nat := 118140960795 + 328812 * 2 ^ 59
def prefixEnd_328812 : Nat := 4983230072969 + 3 ^ 40 * 328812 * 2
def baseEnd_328812 : Nat := 150078756414464671322513

theorem tailTrace_328812 : CollatzResearch.WordTrace tailWord_328812 prefixEnd_328812 150078756414464671322513 := by
  unfold tailWord_328812
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996379442388877731926345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7995172589851836975901793 5996379442388877731926345)
  ·
    refine ⟨4497284581791658298944759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5996379442388877731926345 4497284581791658298944759)
    ·
      refine ⟨6745926872687487448417139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4497284581791658298944759 6745926872687487448417139)
      ·
        refine ⟨10118890309031231172625709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6745926872687487448417139 10118890309031231172625709)
        ·
          refine ⟨3794583865886711689734641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10118890309031231172625709 3794583865886711689734641)
          ·
            refine ⟨2845937899415033767300981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3794583865886711689734641 2845937899415033767300981)
            ·
              refine ⟨266806678070159415684467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2845937899415033767300981 266806678070159415684467)
              ·
                refine ⟨400210017105239123526701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266806678070159415684467 400210017105239123526701)
                ·
                  refine ⟨150078756414464671322513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400210017105239123526701 150078756414464671322513)
                  ·
                    rfl

theorem cell20_328812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_328812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328812 prefixEnd_328812 := by exact prefixLift 328812
  have htrace : WordTrace (prefixWord ++ tailWord_328812) baseStart_328812 baseEnd_328812 := by
    simpa [prefixWord, tailWord_328812, baseEnd_328812] using wordTrace_append hprefix tailTrace_328812
  have hstable : (prefixWord ++ tailWord_328812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328812).length < 2 ^ (prefixWord ++ tailWord_328812).sum := by decide
  have hdescent : baseEnd_328812 < baseStart_328812 := by decide
  rcases family_descends (prefixWord ++ tailWord_328812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328833 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_328833 : Nat := 118140960795 + 328833 * 2 ^ 59
def prefixEnd_328833 : Nat := 4983230072969 + 3 ^ 40 * 328833 * 2
def baseEnd_328833 : Nat := 150088341386681931622427

theorem tailTrace_328833 : CollatzResearch.WordTrace tailWord_328833 prefixEnd_328833 150088341386681931622427 := by
  unfold tailWord_328833
  simp only [CollatzResearch.WordTrace]
  refine ⟨11993524817701676050367153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7995683211801117366911435 11993524817701676050367153)
  ·
    refine ⟨8995143613276257037775365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11993524817701676050367153 8995143613276257037775365)
    ·
      refine ⟨1686589427489298194582881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8995143613276257037775365 1686589427489298194582881)
      ·
        refine ⟨1264942070616973645937161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1686589427489298194582881 1264942070616973645937161)
        ·
          refine ⟨948706552962730234452871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264942070616973645937161 948706552962730234452871)
          ·
            refine ⟨1423059829444095351679307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948706552962730234452871 1423059829444095351679307)
            ·
              refine ⟨2134589744166143027518961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423059829444095351679307 2134589744166143027518961)
              ·
                refine ⟨1600942308124607270639221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2134589744166143027518961 1600942308124607270639221)
                ·
                  refine ⟨150088341386681931622427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1600942308124607270639221 150088341386681931622427)
                  ·
                    rfl

theorem cell20_328833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_328833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328833 prefixEnd_328833 := by exact prefixLift 328833
  have htrace : WordTrace (prefixWord ++ tailWord_328833) baseStart_328833 baseEnd_328833 := by
    simpa [prefixWord, tailWord_328833, baseEnd_328833] using wordTrace_append hprefix tailTrace_328833
  have hstable : (prefixWord ++ tailWord_328833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328833).length < 2 ^ (prefixWord ++ tailWord_328833).sum := by decide
  have hdescent : baseEnd_328833 < baseStart_328833 := by decide
  rcases family_descends (prefixWord ++ tailWord_328833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328836 : List Nat := [2, 3, 2, 1, 2, 2, 3, 3, 2]
def baseStart_328836 : Nat := 118140960795 + 328836 * 2 ^ 59
def prefixEnd_328836 : Nat := 4983230072969 + 3 ^ 40 * 328836 * 2
def baseEnd_328836 : Nat := 150089710668427254522415

theorem tailTrace_328836 : CollatzResearch.WordTrace tailWord_328836 prefixEnd_328836 150089710668427254522415 := by
  unfold tailWord_328836
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996817118345403781363181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7995756157793871708484241 5996817118345403781363181)
  ·
    refine ⟨2248806419379526418011193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5996817118345403781363181 2248806419379526418011193)
    ·
      refine ⟨1686604814534644813508395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2248806419379526418011193 1686604814534644813508395)
      ·
        refine ⟨2529907221801967220262593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686604814534644813508395 2529907221801967220262593)
        ·
          refine ⟨1897430416351475415196945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2529907221801967220262593 1897430416351475415196945)
          ·
            refine ⟨1423072812263606561397709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897430416351475415196945 1423072812263606561397709)
            ·
              refine ⟨533652304598852460524141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1423072812263606561397709 533652304598852460524141)
              ·
                refine ⟨200119614224569672696553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 533652304598852460524141 200119614224569672696553)
                ·
                  refine ⟨150089710668427254522415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200119614224569672696553 150089710668427254522415)
                  ·
                    rfl

theorem cell20_328836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_328836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328836 prefixEnd_328836 := by exact prefixLift 328836
  have htrace : WordTrace (prefixWord ++ tailWord_328836) baseStart_328836 baseEnd_328836 := by
    simpa [prefixWord, tailWord_328836, baseEnd_328836] using wordTrace_append hprefix tailTrace_328836
  have hstable : (prefixWord ++ tailWord_328836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328836).length < 2 ^ (prefixWord ++ tailWord_328836).sum := by decide
  have hdescent : baseEnd_328836 < baseStart_328836 := by decide
  rcases family_descends (prefixWord ++ tailWord_328836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328898 : List Nat := [3, 5, 1, 1, 3, 7]
def baseStart_328898 : Nat := 118140960795 + 328898 * 2 ^ 59
def prefixEnd_328898 : Nat := 4983230072969 + 3 ^ 40 * 328898 * 2
def baseEnd_328898 : Nat := 5559926265104836831685

theorem tailTrace_328898 : CollatzResearch.WordTrace tailWord_328898 prefixEnd_328898 5559926265104836831685 := by
  unfold tailWord_328898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998973890616548037870837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7997263708310794767655565 2998973890616548037870837)
  ·
    refine ⟨281153802245301378550391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2998973890616548037870837 281153802245301378550391)
    ·
      refine ⟨421730703367952067825587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281153802245301378550391 421730703367952067825587)
      ·
        refine ⟨632596055051928101738381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421730703367952067825587 632596055051928101738381)
        ·
          refine ⟨237223520644473038151893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 632596055051928101738381 237223520644473038151893)
          ·
            refine ⟨5559926265104836831685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 237223520644473038151893 5559926265104836831685)
            ·
              rfl

theorem cell20_328898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 7].length) (baseStart_328898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328898 prefixEnd_328898 := by exact prefixLift 328898
  have htrace : WordTrace (prefixWord ++ tailWord_328898) baseStart_328898 baseEnd_328898 := by
    simpa [prefixWord, tailWord_328898, baseEnd_328898] using wordTrace_append hprefix tailTrace_328898
  have hstable : (prefixWord ++ tailWord_328898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328898).length < 2 ^ (prefixWord ++ tailWord_328898).sum := by decide
  have hdescent : baseEnd_328898 < baseStart_328898 := by decide
  rcases family_descends (prefixWord ++ tailWord_328898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328899 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_328899 : Nat := 118140960795 + 328899 * 2 ^ 59
def prefixEnd_328899 : Nat := 4983230072969 + 3 ^ 40 * 328899 * 2
def baseEnd_328899 : Nat := 150118465585079035422157

theorem tailTrace_328899 : CollatzResearch.WordTrace tailWord_328899 prefixEnd_328899 150118465585079035422157 := by
  unfold tailWord_328899
  simp only [CollatzResearch.WordTrace]
  refine ⟨11995932035462569322269751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7997288023641712881513167 11995932035462569322269751)
  ·
    refine ⟨17993898053193853983404627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11995932035462569322269751 17993898053193853983404627)
    ·
      refine ⟨26990847079790780975106941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17993898053193853983404627 26990847079790780975106941)
      ·
        refine ⟨10121567654921542865665103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26990847079790780975106941 10121567654921542865665103)
        ·
          refine ⟨15182351482382314298497655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10121567654921542865665103 15182351482382314298497655)
          ·
            refine ⟨22773527223573471447746483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15182351482382314298497655 22773527223573471447746483)
            ·
              refine ⟨34160290835360207171619725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22773527223573471447746483 34160290835360207171619725)
              ·
                refine ⟨12810109063260077689357397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34160290835360207171619725 12810109063260077689357397)
                ·
                  refine ⟨150118465585079035422157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12810109063260077689357397 150118465585079035422157)
                  ·
                    rfl

theorem cell20_328899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_328899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328899 prefixEnd_328899 := by exact prefixLift 328899
  have htrace : WordTrace (prefixWord ++ tailWord_328899) baseStart_328899 baseEnd_328899 := by
    simpa [prefixWord, tailWord_328899, baseEnd_328899] using wordTrace_append hprefix tailTrace_328899
  have hstable : (prefixWord ++ tailWord_328899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328899).length < 2 ^ (prefixWord ++ tailWord_328899).sum := by decide
  have hdescent : baseEnd_328899 < baseStart_328899 := by decide
  rcases family_descends (prefixWord ++ tailWord_328899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328933 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 4]
def baseStart_328933 : Nat := 118140960795 + 328933 * 2 ^ 59
def prefixEnd_328933 : Nat := 4983230072969 + 3 ^ 40 * 328933 * 2
def baseEnd_328933 : Nat := 150133984111526028288685

theorem tailTrace_328933 : CollatzResearch.WordTrace tailWord_328933 prefixEnd_328933 150133984111526028288685 := by
  unfold tailWord_328933
  simp only [CollatzResearch.WordTrace]
  refine ⟨11997172117339393129007453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7998114744892928752671635 11997172117339393129007453)
  ·
    refine ⟨4498939544002272423377795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11997172117339393129007453 4498939544002272423377795)
    ·
      refine ⟨6748409316003408635066693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4498939544002272423377795 6748409316003408635066693)
      ·
        refine ⟨1265326746750639119075005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6748409316003408635066693 1265326746750639119075005)
        ·
          refine ⟨474497530031489669653127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1265326746750639119075005 474497530031489669653127)
          ·
            refine ⟨711746295047234504479691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474497530031489669653127 711746295047234504479691)
            ·
              refine ⟨1067619442570851756719537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711746295047234504479691 1067619442570851756719537)
              ·
                refine ⟨800714581928138817539653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067619442570851756719537 800714581928138817539653)
                ·
                  refine ⟨150133984111526028288685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 800714581928138817539653 150133984111526028288685)
                  ·
                    rfl

theorem cell20_328933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_328933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328933 prefixEnd_328933 := by exact prefixLift 328933
  have htrace : WordTrace (prefixWord ++ tailWord_328933) baseStart_328933 baseEnd_328933 := by
    simpa [prefixWord, tailWord_328933, baseEnd_328933] using wordTrace_append hprefix tailTrace_328933
  have hstable : (prefixWord ++ tailWord_328933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328933).length < 2 ^ (prefixWord ++ tailWord_328933).sum := by decide
  have hdescent : baseEnd_328933 < baseStart_328933 := by decide
  rcases family_descends (prefixWord ++ tailWord_328933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328940 : List Nat := [2, 2, 1, 1, 2, 5, 3, 4]
def baseStart_328940 : Nat := 118140960795 + 328940 * 2 ^ 59
def prefixEnd_328940 : Nat := 4983230072969 + 3 ^ 40 * 328940 * 2
def baseEnd_328940 : Nat := 50045726367421705018441

theorem tailTrace_328940 : CollatzResearch.WordTrace tailWord_328940 prefixEnd_328940 50045726367421705018441 := by
  unfold tailWord_328940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5998713714157016662256137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7998284952209355549674849 5998713714157016662256137)
  ·
    refine ⟨4499035285617762496692103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5998713714157016662256137 4499035285617762496692103)
    ·
      refine ⟨6748552928426643745038155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4499035285617762496692103 6748552928426643745038155)
      ·
        refine ⟨10122829392639965617557233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6748552928426643745038155 10122829392639965617557233)
        ·
          refine ⟨7592122044479974213167925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10122829392639965617557233 7592122044479974213167925)
          ·
            refine ⟨711761441669997582484493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7592122044479974213167925 711761441669997582484493)
            ·
              refine ⟨266910540626249093431685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711761441669997582484493 266910540626249093431685)
              ·
                refine ⟨50045726367421705018441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266910540626249093431685 50045726367421705018441)
                ·
                  rfl

theorem cell20_328940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_328940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328940 prefixEnd_328940 := by exact prefixLift 328940
  have htrace : WordTrace (prefixWord ++ tailWord_328940) baseStart_328940 baseEnd_328940 := by
    simpa [prefixWord, tailWord_328940, baseEnd_328940] using wordTrace_append hprefix tailTrace_328940
  have hstable : (prefixWord ++ tailWord_328940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328940).length < 2 ^ (prefixWord ++ tailWord_328940).sum := by decide
  have hdescent : baseEnd_328940 < baseStart_328940 := by decide
  rcases family_descends (prefixWord ++ tailWord_328940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328961 : List Nat := [1, 2, 4, 1, 1, 4, 7]
def baseStart_328961 : Nat := 118140960795 + 328961 * 2 ^ 59
def prefixEnd_328961 : Nat := 4983230072969 + 3 ^ 40 * 328961 * 2
def baseEnd_328961 : Nat := 16682973786053597261693

theorem tailTrace_328961 : CollatzResearch.WordTrace tailWord_328961 prefixEnd_328961 16682973786053597261693 := by
  unfold tailWord_328961
  simp only [CollatzResearch.WordTrace]
  refine ⟨11998193361237953911026737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7998795574158635940684491 11998193361237953911026737)
  ·
    refine ⟨8998645020928465433270053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11998193361237953911026737 8998645020928465433270053)
    ·
      refine ⟨1687245941424087268738135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8998645020928465433270053 1687245941424087268738135)
      ·
        refine ⟨2530868912136130903107203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687245941424087268738135 2530868912136130903107203)
        ·
          refine ⟨3796303368204196354660805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2530868912136130903107203 3796303368204196354660805)
          ·
            refine ⟨711806881538286816498901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3796303368204196354660805 711806881538286816498901)
            ·
              refine ⟨16682973786053597261693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 711806881538286816498901 16682973786053597261693)
              ·
                rfl

theorem cell20_328961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 7].length) (baseStart_328961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328961 prefixEnd_328961 := by exact prefixLift 328961
  have htrace : WordTrace (prefixWord ++ tailWord_328961) baseStart_328961 baseEnd_328961 := by
    simpa [prefixWord, tailWord_328961, baseEnd_328961] using wordTrace_append hprefix tailTrace_328961
  have hstable : (prefixWord ++ tailWord_328961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328961).length < 2 ^ (prefixWord ++ tailWord_328961).sum := by decide
  have hdescent : baseEnd_328961 < baseStart_328961 := by decide
  rcases family_descends (prefixWord ++ tailWord_328961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328964 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_328964 : Nat := 118140960795 + 328964 * 2 ^ 59
def prefixEnd_328964 : Nat := 4983230072969 + 3 ^ 40 * 328964 * 2
def baseEnd_328964 : Nat := 150148133356227698255225

theorem tailTrace_328964 : CollatzResearch.WordTrace tailWord_328964 prefixEnd_328964 150148133356227698255225 := by
  unfold tailWord_328964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5999151390113542711692973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7998868520151390282257297 5999151390113542711692973)
  ·
    refine ⟨2249681771292578516884865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5999151390113542711692973 2249681771292578516884865)
    ·
      refine ⟨1687261328469433887663649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2249681771292578516884865 1687261328469433887663649)
      ·
        refine ⟨1265445996352075415747737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1687261328469433887663649 1265445996352075415747737)
        ·
          refine ⟨949084497264056561810803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1265445996352075415747737 949084497264056561810803)
          ·
            refine ⟨1423626745896084842716205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949084497264056561810803 1423626745896084842716205)
            ·
              refine ⟨533860029711031816018577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1423626745896084842716205 533860029711031816018577)
              ·
                refine ⟨400395022283273862013933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533860029711031816018577 400395022283273862013933)
                ·
                  refine ⟨150148133356227698255225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400395022283273862013933 150148133356227698255225)
                  ·
                    rfl

theorem cell20_328964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_328964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328964 prefixEnd_328964 := by exact prefixLift 328964
  have htrace : WordTrace (prefixWord ++ tailWord_328964) baseStart_328964 baseEnd_328964 := by
    simpa [prefixWord, tailWord_328964, baseEnd_328964] using wordTrace_append hprefix tailTrace_328964
  have hstable : (prefixWord ++ tailWord_328964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328964).length < 2 ^ (prefixWord ++ tailWord_328964).sum := by decide
  have hdescent : baseEnd_328964 < baseStart_328964 := by decide
  rcases family_descends (prefixWord ++ tailWord_328964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328971 : List Nat := [1, 1, 1, 1, 5, 3, 2, 4, 2]
def baseStart_328971 : Nat := 118140960795 + 328971 * 2 ^ 59
def prefixEnd_328971 : Nat := 4983230072969 + 3 ^ 40 * 328971 * 2
def baseEnd_328971 : Nat := 150151328346966785021863

theorem tailTrace_328971 : CollatzResearch.WordTrace tailWord_328971 prefixEnd_328971 150151328346966785021863 := by
  unfold tailWord_328971
  simp only [CollatzResearch.WordTrace]
  refine ⟨11998558091201725618890767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7999038727467817079260511 11998558091201725618890767)
  ·
    refine ⟨17997837136802588428336151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11998558091201725618890767 17997837136802588428336151)
    ·
      refine ⟨26996755705203882642504227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17997837136802588428336151 26996755705203882642504227)
      ·
        refine ⟨40495133557805823963756341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26996755705203882642504227 40495133557805823963756341)
        ·
          refine ⟨3796418771044295996602157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40495133557805823963756341 3796418771044295996602157)
          ·
            refine ⟨1423657039141610998725809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3796418771044295996602157 1423657039141610998725809)
            ·
              refine ⟨1067742779356208249044357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423657039141610998725809 1067742779356208249044357)
              ·
                refine ⟨200201771129289046695817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1067742779356208249044357 200201771129289046695817)
                ·
                  refine ⟨150151328346966785021863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200201771129289046695817 150151328346966785021863)
                  ·
                    rfl

theorem cell20_328971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 2].length) (baseStart_328971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_328971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_328971 prefixEnd_328971 := by exact prefixLift 328971
  have htrace : WordTrace (prefixWord ++ tailWord_328971) baseStart_328971 baseEnd_328971 := by
    simpa [prefixWord, tailWord_328971, baseEnd_328971] using wordTrace_append hprefix tailTrace_328971
  have hstable : (prefixWord ++ tailWord_328971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328971).length < 2 ^ (prefixWord ++ tailWord_328971).sum := by decide
  have hdescent : baseEnd_328971 < baseStart_328971 := by decide
  rcases family_descends (prefixWord ++ tailWord_328971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329005 : List Nat := [1, 5, 3, 1, 1, 1, 3, 3, 2]
def baseStart_329005 : Nat := 118140960795 + 329005 * 2 ^ 59
def prefixEnd_329005 : Nat := 4983230072969 + 3 ^ 40 * 329005 * 2
def baseEnd_329005 : Nat := 150166846873413777888391

theorem tailTrace_329005 : CollatzResearch.WordTrace tailWord_329005 prefixEnd_329005 150166846873413777888391 := by
  unfold tailWord_329005
  simp only [CollatzResearch.WordTrace]
  refine ⟨11999798173078549425628469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7999865448719032950418979 11999798173078549425628469)
  ·
    refine ⟨1124981078726114008652669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11999798173078549425628469 1124981078726114008652669)
    ·
      refine ⟨421867904522292753244751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1124981078726114008652669 421867904522292753244751)
      ·
        refine ⟨632801856783439129867127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421867904522292753244751 632801856783439129867127)
        ·
          refine ⟨949202785175158694800691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632801856783439129867127 949202785175158694800691)
          ·
            refine ⟨1423804177762738042201037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949202785175158694800691 1423804177762738042201037)
            ·
              refine ⟨533926566661026765825389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1423804177762738042201037 533926566661026765825389)
              ·
                refine ⟨200222462497885037184521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 533926566661026765825389 200222462497885037184521)
                ·
                  refine ⟨150166846873413777888391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200222462497885037184521 150166846873413777888391)
                  ·
                    rfl

theorem cell20_329005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_329005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329005 prefixEnd_329005 := by exact prefixLift 329005
  have htrace : WordTrace (prefixWord ++ tailWord_329005) baseStart_329005 baseEnd_329005 := by
    simpa [prefixWord, tailWord_329005, baseEnd_329005] using wordTrace_append hprefix tailTrace_329005
  have hstable : (prefixWord ++ tailWord_329005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329005).length < 2 ^ (prefixWord ++ tailWord_329005).sum := by decide
  have hdescent : baseEnd_329005 < baseStart_329005 := by decide
  rcases family_descends (prefixWord ++ tailWord_329005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329085 : List Nat := [1, 4, 1, 1, 2, 2, 3, 4, 2]
def baseStart_329085 : Nat := 118140960795 + 329085 * 2 ^ 59
def prefixEnd_329085 : Nat := 4983230072969 + 3 ^ 40 * 329085 * 2
def baseEnd_329085 : Nat := 150203361053289055221397

theorem tailTrace_329085 : CollatzResearch.WordTrace tailWord_329085 prefixEnd_329085 150203361053289055221397 := by
  unfold tailWord_329085
  simp only [CollatzResearch.WordTrace]
  refine ⟨12002716012788723088540709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8001810675192482059027139 12002716012788723088540709)
  ·
    refine ⟨2250509252397885579101383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12002716012788723088540709 2250509252397885579101383)
    ·
      refine ⟨3375763878596828368652075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2250509252397885579101383 3375763878596828368652075)
      ·
        refine ⟨5063645817895242552978113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3375763878596828368652075 5063645817895242552978113)
        ·
          refine ⟨3797734363421431914733585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5063645817895242552978113 3797734363421431914733585)
          ·
            refine ⟨2848300772566073936050189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3797734363421431914733585 2848300772566073936050189)
            ·
              refine ⟨1068112789712277726018821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2848300772566073936050189 1068112789712277726018821)
              ·
                refine ⟨200271148071052073628529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1068112789712277726018821 200271148071052073628529)
                ·
                  refine ⟨150203361053289055221397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200271148071052073628529 150203361053289055221397)
                  ·
                    rfl

theorem cell20_329085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_329085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329085 prefixEnd_329085 := by exact prefixLift 329085
  have htrace : WordTrace (prefixWord ++ tailWord_329085) baseStart_329085 baseEnd_329085 := by
    simpa [prefixWord, tailWord_329085, baseEnd_329085] using wordTrace_append hprefix tailTrace_329085
  have hstable : (prefixWord ++ tailWord_329085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329085).length < 2 ^ (prefixWord ++ tailWord_329085).sum := by decide
  have hdescent : baseEnd_329085 < baseStart_329085 := by decide
  rcases family_descends (prefixWord ++ tailWord_329085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329092 : List Nat := [2, 3, 2, 1, 1, 5, 1, 5]
def baseStart_329092 : Nat := 118140960795 + 329092 * 2 ^ 59
def prefixEnd_329092 : Nat := 4983230072969 + 3 ^ 40 * 329092 * 2
def baseEnd_329092 : Nat := 50068852014676047329345

theorem tailTrace_329092 : CollatzResearch.WordTrace tailWord_329092 prefixEnd_329092 50068852014676047329345 := by
  unfold tailWord_329092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001485661881681642022765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8001980882508908856030353 6001485661881681642022765)
  ·
    refine ⟨2250557123205630615758537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6001485661881681642022765 2250557123205630615758537)
    ·
      refine ⟨1687917842404222961818903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2250557123205630615758537 1687917842404222961818903)
      ·
        refine ⟨2531876763606334442728355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687917842404222961818903 2531876763606334442728355)
        ·
          refine ⟨3797815145409501664092533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2531876763606334442728355 3797815145409501664092533)
          ·
            refine ⟨356045169882140781008675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3797815145409501664092533 356045169882140781008675)
            ·
              refine ⟨534067754823211171513013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356045169882140781008675 534067754823211171513013)
              ·
                refine ⟨50068852014676047329345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 534067754823211171513013 50068852014676047329345)
                ·
                  rfl

theorem cell20_329092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_329092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329092 prefixEnd_329092 := by exact prefixLift 329092
  have htrace : WordTrace (prefixWord ++ tailWord_329092) baseStart_329092 baseEnd_329092 := by
    simpa [prefixWord, tailWord_329092, baseEnd_329092] using wordTrace_append hprefix tailTrace_329092
  have hstable : (prefixWord ++ tailWord_329092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329092).length < 2 ^ (prefixWord ++ tailWord_329092).sum := by decide
  have hdescent : baseEnd_329092 < baseStart_329092 := by decide
  rcases family_descends (prefixWord ++ tailWord_329092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329120 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_329120 : Nat := 118140960795 + 329120 * 2 ^ 59
def prefixEnd_329120 : Nat := 4983230072969 + 3 ^ 40 * 329120 * 2
def baseEnd_329120 : Nat := 150219336006984489054587

theorem tailTrace_329120 : CollatzResearch.WordTrace tailWord_329120 prefixEnd_329120 150219336006984489054587 := by
  unfold tailWord_329120
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001996283830962033032407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8002661711774616044043209 6001996283830962033032407)
  ·
    refine ⟨9002994425746443049548611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6001996283830962033032407 9002994425746443049548611)
    ·
      refine ⟨13504491638619664574322917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9002994425746443049548611 13504491638619664574322917)
      ·
        refine ⟨2532092182241187107685547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13504491638619664574322917 2532092182241187107685547)
        ·
          refine ⟨3798138273361780661528321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2532092182241187107685547 3798138273361780661528321)
          ·
            refine ⟨2848603705021335496146241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3798138273361780661528321 2848603705021335496146241)
            ·
              refine ⟨2136452778766001622109681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848603705021335496146241 2136452778766001622109681)
              ·
                refine ⟨1602339584074501216582261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2136452778766001622109681 1602339584074501216582261)
                ·
                  refine ⟨150219336006984489054587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1602339584074501216582261 150219336006984489054587)
                  ·
                    rfl

theorem cell20_329120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_329120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329120 prefixEnd_329120 := by exact prefixLift 329120
  have htrace : WordTrace (prefixWord ++ tailWord_329120) baseStart_329120 baseEnd_329120 := by
    simpa [prefixWord, tailWord_329120, baseEnd_329120] using wordTrace_append hprefix tailTrace_329120
  have hstable : (prefixWord ++ tailWord_329120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329120).length < 2 ^ (prefixWord ++ tailWord_329120).sum := by decide
  have hdescent : baseEnd_329120 < baseStart_329120 := by decide
  rcases family_descends (prefixWord ++ tailWord_329120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329123 : List Nat := [1, 1, 1, 4, 1, 3, 4, 3, 2]
def baseStart_329123 : Nat := 118140960795 + 329123 * 2 ^ 59
def prefixEnd_329123 : Nat := 4983230072969 + 3 ^ 40 * 329123 * 2
def baseEnd_329123 : Nat := 150220705288729811954575

theorem tailTrace_329123 : CollatzResearch.WordTrace tailWord_329123 prefixEnd_329123 150220705288729811954575 := by
  unfold tailWord_329123
  simp only [CollatzResearch.WordTrace]
  refine ⟨12004101986651055578424023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8002734657767370385616015 12004101986651055578424023)
  ·
    refine ⟨18006152979976583367636035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12004101986651055578424023 18006152979976583367636035)
    ·
      refine ⟨27009229469964875051454053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18006152979976583367636035 27009229469964875051454053)
      ·
        refine ⟨5064230525618414072147635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27009229469964875051454053 5064230525618414072147635)
        ·
          refine ⟨7596345788427621108221453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064230525618414072147635 7596345788427621108221453)
          ·
            refine ⟨2848629670660357915583045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7596345788427621108221453 2848629670660357915583045)
            ·
              refine ⟨534118063248817109171821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2848629670660357915583045 534118063248817109171821)
              ·
                refine ⟨200294273718306415939433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 534118063248817109171821 200294273718306415939433)
                ·
                  refine ⟨150220705288729811954575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200294273718306415939433 150220705288729811954575)
                  ·
                    rfl

theorem cell20_329123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 3, 2].length) (baseStart_329123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329123 prefixEnd_329123 := by exact prefixLift 329123
  have htrace : WordTrace (prefixWord ++ tailWord_329123) baseStart_329123 baseEnd_329123 := by
    simpa [prefixWord, tailWord_329123, baseEnd_329123] using wordTrace_append hprefix tailTrace_329123
  have hstable : (prefixWord ++ tailWord_329123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329123).length < 2 ^ (prefixWord ++ tailWord_329123).sum := by decide
  have hdescent : baseEnd_329123 < baseStart_329123 := by decide
  rcases family_descends (prefixWord ++ tailWord_329123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329133 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 3]
def baseStart_329133 : Nat := 118140960795 + 329133 * 2 ^ 59
def prefixEnd_329133 : Nat := 4983230072969 + 3 ^ 40 * 329133 * 2
def baseEnd_329133 : Nat := 150225269561214221621201

theorem tailTrace_329133 : CollatzResearch.WordTrace tailWord_329133 prefixEnd_329133 150225269561214221621201 := by
  unfold tailWord_329133
  simp only [CollatzResearch.WordTrace]
  refine ⟨12004466716614827286288053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8002977811076551524192035 12004466716614827286288053)
  ·
    refine ⟨1125418754682640058089505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12004466716614827286288053 1125418754682640058089505)
    ·
      refine ⟨844064066011980043567129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1125418754682640058089505 844064066011980043567129)
      ·
        refine ⟨633048049508985032675347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 844064066011980043567129 633048049508985032675347)
        ·
          refine ⟨949572074263477549013021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633048049508985032675347 949572074263477549013021)
          ·
            refine ⟨356089527848804080879883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 949572074263477549013021 356089527848804080879883)
            ·
              refine ⟨534134291773206121319825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356089527848804080879883 534134291773206121319825)
              ·
                refine ⟨400600718829904590989869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534134291773206121319825 400600718829904590989869)
                ·
                  refine ⟨150225269561214221621201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400600718829904590989869 150225269561214221621201)
                  ·
                    rfl

theorem cell20_329133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_329133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329133 prefixEnd_329133 := by exact prefixLift 329133
  have htrace : WordTrace (prefixWord ++ tailWord_329133) baseStart_329133 baseEnd_329133 := by
    simpa [prefixWord, tailWord_329133, baseEnd_329133] using wordTrace_append hprefix tailTrace_329133
  have hstable : (prefixWord ++ tailWord_329133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329133).length < 2 ^ (prefixWord ++ tailWord_329133).sum := by decide
  have hdescent : baseEnd_329133 < baseStart_329133 := by decide
  rcases family_descends (prefixWord ++ tailWord_329133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329178 : List Nat := [3, 1, 1, 2, 3, 4, 1, 3, 2]
def baseStart_329178 : Nat := 118140960795 + 329178 * 2 ^ 59
def prefixEnd_329178 : Nat := 4983230072969 + 3 ^ 40 * 329178 * 2
def baseEnd_329178 : Nat := 150245808787394065121017

theorem tailTrace_329178 : CollatzResearch.WordTrace tailWord_329178 prefixEnd_329178 150245808787394065121017 := by
  unfold tailWord_329178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3001527000362949992919047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8004072000967866647784125 3001527000362949992919047)
  ·
    refine ⟨4502290500544424989378571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3001527000362949992919047 4502290500544424989378571)
    ·
      refine ⟨6753435750816637484067857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4502290500544424989378571 6753435750816637484067857)
      ·
        refine ⟨5065076813112478113050893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6753435750816637484067857 5065076813112478113050893)
        ·
          refine ⟨1899403804917179292394085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5065076813112478113050893 1899403804917179292394085)
          ·
            refine ⟨356138213421971117323891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1899403804917179292394085 356138213421971117323891)
            ·
              refine ⟨534207320132956675985837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356138213421971117323891 534207320132956675985837)
              ·
                refine ⟨200327745049858753494689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 534207320132956675985837 200327745049858753494689)
                ·
                  refine ⟨150245808787394065121017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200327745049858753494689 150245808787394065121017)
                  ·
                    rfl

theorem cell20_329178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_329178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329178 prefixEnd_329178 := by exact prefixLift 329178
  have htrace : WordTrace (prefixWord ++ tailWord_329178) baseStart_329178 baseEnd_329178 := by
    simpa [prefixWord, tailWord_329178, baseEnd_329178] using wordTrace_append hprefix tailTrace_329178
  have hstable : (prefixWord ++ tailWord_329178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329178).length < 2 ^ (prefixWord ++ tailWord_329178).sum := by decide
  have hdescent : baseEnd_329178 < baseStart_329178 := by decide
  rcases family_descends (prefixWord ++ tailWord_329178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329189 : List Nat := [1, 3, 1, 5, 1, 1, 8]
def baseStart_329189 : Nat := 118140960795 + 329189 * 2 ^ 59
def prefixEnd_329189 : Nat := 4983230072969 + 3 ^ 40 * 329189 * 2
def baseEnd_329189 : Nat := 16694536609680768417145

theorem tailTrace_329189 : CollatzResearch.WordTrace tailWord_329189 prefixEnd_329189 16694536609680768417145 := by
  unfold tailWord_329189
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006509204411948850326621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8004339469607965900217747 12006509204411948850326621)
  ·
    refine ⟨4502440951654480818872483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12006509204411948850326621 4502440951654480818872483)
    ·
      refine ⟨6753661427481721228308725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4502440951654480818872483 6753661427481721228308725)
      ·
        refine ⟨633155758826411365153943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6753661427481721228308725 633155758826411365153943)
        ·
          refine ⟨949733638239617047730915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633155758826411365153943 949733638239617047730915)
          ·
            refine ⟨1424600457359425571596373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949733638239617047730915 1424600457359425571596373)
            ·
              refine ⟨16694536609680768417145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1424600457359425571596373 16694536609680768417145)
              ·
                rfl

theorem cell20_329189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 8].length) (baseStart_329189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329189 prefixEnd_329189 := by exact prefixLift 329189
  have htrace : WordTrace (prefixWord ++ tailWord_329189) baseStart_329189 baseEnd_329189 := by
    simpa [prefixWord, tailWord_329189, baseEnd_329189] using wordTrace_append hprefix tailTrace_329189
  have hstable : (prefixWord ++ tailWord_329189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329189).length < 2 ^ (prefixWord ++ tailWord_329189).sum := by decide
  have hdescent : baseEnd_329189 < baseStart_329189 := by decide
  rcases family_descends (prefixWord ++ tailWord_329189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329203 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_329203 : Nat := 118140960795 + 329203 * 2 ^ 59
def prefixEnd_329203 : Nat := 4983230072969 + 3 ^ 40 * 329203 * 2
def baseEnd_329203 : Nat := 150257219468605089287581

theorem tailTrace_329203 : CollatzResearch.WordTrace tailWord_329203 prefixEnd_329203 150257219468605089287581 := by
  unfold tailWord_329203
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007019826361229241336263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8004679884240819494224175 12007019826361229241336263)
  ·
    refine ⟨18010529739541843862004395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12007019826361229241336263 18010529739541843862004395)
    ·
      refine ⟨27015794609312765793006593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18010529739541843862004395 27015794609312765793006593)
      ·
        refine ⟨20261845956984574344754945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27015794609312765793006593 20261845956984574344754945)
        ·
          refine ⟨15196384467738430758566209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20261845956984574344754945 15196384467738430758566209)
          ·
            refine ⟨11397288350803823068924657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15196384467738430758566209 11397288350803823068924657)
            ·
              refine ⟨8547966263102867301693493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11397288350803823068924657 8547966263102867301693493)
              ·
                refine ⟨801371837165893809533765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8547966263102867301693493 801371837165893809533765)
                ·
                  refine ⟨150257219468605089287581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801371837165893809533765 150257219468605089287581)
                  ·
                    rfl

theorem cell20_329203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_329203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329203 prefixEnd_329203 := by exact prefixLift 329203
  have htrace : WordTrace (prefixWord ++ tailWord_329203) baseStart_329203 baseEnd_329203 := by
    simpa [prefixWord, tailWord_329203, baseEnd_329203] using wordTrace_append hprefix tailTrace_329203
  have hstable : (prefixWord ++ tailWord_329203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329203).length < 2 ^ (prefixWord ++ tailWord_329203).sum := by decide
  have hdescent : baseEnd_329203 < baseStart_329203 := by decide
  rcases family_descends (prefixWord ++ tailWord_329203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329206 : List Nat := [5, 1, 1, 1, 2, 3, 2, 5]
def baseStart_329206 : Nat := 118140960795 + 329206 * 2 ^ 59
def prefixEnd_329206 : Nat := 4983230072969 + 3 ^ 40 * 329206 * 2
def baseEnd_329206 : Nat := 50086196250116804062523

theorem tailTrace_329206 : CollatzResearch.WordTrace tailWord_329206 prefixEnd_329206 50086196250116804062523 := by
  unfold tailWord_329206
  simp only [CollatzResearch.WordTrace]
  refine ⟨750445577834397547105967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8004752830233573835796981 750445577834397547105967)
  ·
    refine ⟨1125668366751596320658951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 750445577834397547105967 1125668366751596320658951)
    ·
      refine ⟨1688502550127394480988427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125668366751596320658951 1688502550127394480988427)
      ·
        refine ⟨2532753825191091721482641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688502550127394480988427 2532753825191091721482641)
        ·
          refine ⟨1899565368893318791111981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2532753825191091721482641 1899565368893318791111981)
          ·
            refine ⟨712337013334994546666993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1899565368893318791111981 712337013334994546666993)
            ·
              refine ⟨534252760001245910000245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712337013334994546666993 534252760001245910000245)
              ·
                refine ⟨50086196250116804062523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 534252760001245910000245 50086196250116804062523)
                ·
                  rfl

theorem cell20_329206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_329206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329206 prefixEnd_329206 := by exact prefixLift 329206
  have htrace : WordTrace (prefixWord ++ tailWord_329206) baseStart_329206 baseEnd_329206 := by
    simpa [prefixWord, tailWord_329206, baseEnd_329206] using wordTrace_append hprefix tailTrace_329206
  have hstable : (prefixWord ++ tailWord_329206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329206).length < 2 ^ (prefixWord ++ tailWord_329206).sum := by decide
  have hdescent : baseEnd_329206 < baseStart_329206 := by decide
  rcases family_descends (prefixWord ++ tailWord_329206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329213 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 3]
def baseStart_329213 : Nat := 118140960795 + 329213 * 2 ^ 59
def prefixEnd_329213 : Nat := 4983230072969 + 3 ^ 40 * 329213 * 2
def baseEnd_329213 : Nat := 150261783741089498954207

theorem tailTrace_329213 : CollatzResearch.WordTrace tailWord_329213 prefixEnd_329213 150261783741089498954207 := by
  unfold tailWord_329213
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007384556325000949200293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8004923037550000632800195 12007384556325000949200293)
  ·
    refine ⟨2251384604310937677975055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12007384556325000949200293 2251384604310937677975055)
    ·
      refine ⟨3377076906466406516962583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2251384604310937677975055 3377076906466406516962583)
      ·
        refine ⟨5065615359699609775443875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377076906466406516962583 5065615359699609775443875)
        ·
          refine ⟨7598423039549414663165813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5065615359699609775443875 7598423039549414663165813)
          ·
            refine ⟨712352159957757624671795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7598423039549414663165813 712352159957757624671795)
            ·
              refine ⟨1068528239936636437007693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712352159957757624671795 1068528239936636437007693)
              ·
                refine ⟨400698089976238663877885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068528239936636437007693 400698089976238663877885)
                ·
                  refine ⟨150261783741089498954207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400698089976238663877885 150261783741089498954207)
                  ·
                    rfl

theorem cell20_329213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_329213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329213 prefixEnd_329213 := by exact prefixLift 329213
  have htrace : WordTrace (prefixWord ++ tailWord_329213) baseStart_329213 baseEnd_329213 := by
    simpa [prefixWord, tailWord_329213, baseEnd_329213] using wordTrace_append hprefix tailTrace_329213
  have hstable : (prefixWord ++ tailWord_329213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329213).length < 2 ^ (prefixWord ++ tailWord_329213).sum := by decide
  have hdescent : baseEnd_329213 < baseStart_329213 := by decide
  rcases family_descends (prefixWord ++ tailWord_329213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329246 : List Nat := [4, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_329246 : Nat := 118140960795 + 329246 * 2 ^ 59
def prefixEnd_329246 : Nat := 4983230072969 + 3 ^ 40 * 329246 * 2
def baseEnd_329246 : Nat := 150276845840288050854073

theorem tailTrace_329246 : CollatzResearch.WordTrace tailWord_329246 prefixEnd_329246 150276845840288050854073 := by
  unfold tailWord_329246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501073520650680948143949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8005725443470298390101061 1501073520650680948143949)
  ·
    refine ⟨562902570244005355553981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1501073520650680948143949 562902570244005355553981)
    ·
      refine ⟨211088463841502008332743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 562902570244005355553981 211088463841502008332743)
      ·
        refine ⟨316632695762253012499115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211088463841502008332743 316632695762253012499115)
        ·
          refine ⟨474949043643379518748673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316632695762253012499115 474949043643379518748673)
          ·
            refine ⟨356211782732534639061505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474949043643379518748673 356211782732534639061505)
            ·
              refine ⟨267158837049400979296129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356211782732534639061505 267158837049400979296129)
              ·
                refine ⟨200369127787050734472097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267158837049400979296129 200369127787050734472097)
                ·
                  refine ⟨150276845840288050854073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200369127787050734472097 150276845840288050854073)
                  ·
                    rfl

theorem cell20_329246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_329246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329246 prefixEnd_329246 := by exact prefixLift 329246
  have htrace : WordTrace (prefixWord ++ tailWord_329246) baseStart_329246 baseEnd_329246 := by
    simpa [prefixWord, tailWord_329246, baseEnd_329246] using wordTrace_append hprefix tailTrace_329246
  have hstable : (prefixWord ++ tailWord_329246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329246).length < 2 ^ (prefixWord ++ tailWord_329246).sum := by decide
  have hdescent : baseEnd_329246 < baseStart_329246 := by decide
  rcases family_descends (prefixWord ++ tailWord_329246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329258 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_329258 : Nat := 118140960795 + 329258 * 2 ^ 59
def prefixEnd_329258 : Nat := 4983230072969 + 3 ^ 40 * 329258 * 2
def baseEnd_329258 : Nat := 150282322967269342454023

theorem tailTrace_329258 : CollatzResearch.WordTrace tailWord_329258 prefixEnd_329258 150282322967269342454023 := by
  unfold tailWord_329258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002256460290493408647107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8006017227441315756392285 3002256460290493408647107)
  ·
    refine ⟨4503384690435740112970661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3002256460290493408647107 4503384690435740112970661)
    ·
      refine ⟨844384629456701271181999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4503384690435740112970661 844384629456701271181999)
      ·
        refine ⟨1266576944185051906772999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844384629456701271181999 1266576944185051906772999)
        ·
          refine ⟨1899865416277577860159499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266576944185051906772999 1899865416277577860159499)
          ·
            refine ⟨2849798124416366790239249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899865416277577860159499 2849798124416366790239249)
            ·
              refine ⟨2137348593312275092679437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2849798124416366790239249 2137348593312275092679437)
              ·
                refine ⟨801505722492103159754789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137348593312275092679437 801505722492103159754789)
                ·
                  refine ⟨150282322967269342454023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801505722492103159754789 150282322967269342454023)
                  ·
                    rfl

theorem cell20_329258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_329258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329258 prefixEnd_329258 := by exact prefixLift 329258
  have htrace : WordTrace (prefixWord ++ tailWord_329258) baseStart_329258 baseEnd_329258 := by
    simpa [prefixWord, tailWord_329258, baseEnd_329258] using wordTrace_append hprefix tailTrace_329258
  have hstable : (prefixWord ++ tailWord_329258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329258).length < 2 ^ (prefixWord ++ tailWord_329258).sum := by decide
  have hdescent : baseEnd_329258 < baseStart_329258 := by decide
  rcases family_descends (prefixWord ++ tailWord_329258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329279 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_329279 : Nat := 118140960795 + 329279 * 2 ^ 59
def prefixEnd_329279 : Nat := 4983230072969 + 3 ^ 40 * 329279 * 2
def baseEnd_329279 : Nat := 150291907939486602753937

theorem tailTrace_329279 : CollatzResearch.WordTrace tailWord_329279 prefixEnd_329279 150291907939486602753937 := by
  unfold tailWord_329279
  simp only [CollatzResearch.WordTrace]
  refine ⟨12009791774085894221102891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8006527849390596147401927 12009791774085894221102891)
  ·
    refine ⟨18014687661128841331654337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12009791774085894221102891 18014687661128841331654337)
    ·
      refine ⟨13511015745846630998740753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18014687661128841331654337 13511015745846630998740753)
      ·
        refine ⟨10133261809384973249055565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13511015745846630998740753 10133261809384973249055565)
        ·
          refine ⟨3799973178519364968395837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10133261809384973249055565 3799973178519364968395837)
          ·
            refine ⟨1424989941944761863148439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3799973178519364968395837 1424989941944761863148439)
            ·
              refine ⟨2137484912917142794722659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424989941944761863148439 2137484912917142794722659)
              ·
                refine ⟨3206227369375714192083989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2137484912917142794722659 3206227369375714192083989)
                ·
                  refine ⟨150291907939486602753937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3206227369375714192083989 150291907939486602753937)
                  ·
                    rfl

theorem cell20_329279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_329279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329279 prefixEnd_329279 := by exact prefixLift 329279
  have htrace : WordTrace (prefixWord ++ tailWord_329279) baseStart_329279 baseEnd_329279 := by
    simpa [prefixWord, tailWord_329279, baseEnd_329279] using wordTrace_append hprefix tailTrace_329279
  have hstable : (prefixWord ++ tailWord_329279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329279).length < 2 ^ (prefixWord ++ tailWord_329279).sum := by decide
  have hdescent : baseEnd_329279 < baseStart_329279 := by decide
  rcases family_descends (prefixWord ++ tailWord_329279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329324 : List Nat := [2, 2, 1, 1, 3, 1, 1, 9]
def baseStart_329324 : Nat := 118140960795 + 329324 * 2 ^ 59
def prefixEnd_329324 : Nat := 4983230072969 + 3 ^ 40 * 329324 * 2
def baseEnd_329324 : Nat := 50104149055222148751251

theorem tailTrace_329324 : CollatzResearch.WordTrace tailWord_329324 prefixEnd_329324 50104149055222148751251 := by
  unfold tailWord_329324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005716529461433453245513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8007622039281911270994017 6005716529461433453245513)
  ·
    refine ⟨4504287397096075089934135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6005716529461433453245513 4504287397096075089934135)
    ·
      refine ⟨6756431095644112634901203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4504287397096075089934135 6756431095644112634901203)
      ·
        refine ⟨10134646643466168952351805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6756431095644112634901203 10134646643466168952351805)
        ·
          refine ⟨3800492491299813357131927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10134646643466168952351805 3800492491299813357131927)
          ·
            refine ⟨5700738736949720035697891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800492491299813357131927 5700738736949720035697891)
            ·
              refine ⟨8551108105424580053546837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700738736949720035697891 8551108105424580053546837)
              ·
                refine ⟨50104149055222148751251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8551108105424580053546837 50104149055222148751251)
                ·
                  rfl

theorem cell20_329324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_329324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329324 prefixEnd_329324 := by exact prefixLift 329324
  have htrace : WordTrace (prefixWord ++ tailWord_329324) baseStart_329324 baseEnd_329324 := by
    simpa [prefixWord, tailWord_329324, baseEnd_329324] using wordTrace_append hprefix tailTrace_329324
  have hstable : (prefixWord ++ tailWord_329324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329324).length < 2 ^ (prefixWord ++ tailWord_329324).sum := by decide
  have hdescent : baseEnd_329324 < baseStart_329324 := by decide
  rcases family_descends (prefixWord ++ tailWord_329324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329341 : List Nat := [1, 4, 1, 1, 4, 2, 1, 6]
def baseStart_329341 : Nat := 118140960795 + 329341 * 2 ^ 59
def prefixEnd_329341 : Nat := 4983230072969 + 3 ^ 40 * 329341 * 2
def baseEnd_329341 : Nat := 50106735476296647562339

theorem tailTrace_329341 : CollatzResearch.WordTrace tailWord_329341 prefixEnd_329341 50106735476296647562339 := by
  unfold tailWord_329341
  simp only [CollatzResearch.WordTrace]
  refine ⟨12012053099861278809859877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8008035399907519206573251 12012053099861278809859877)
  ·
    refine ⟨2252259956223989776848727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12012053099861278809859877 2252259956223989776848727)
    ·
      refine ⟨3378389934335984665273091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2252259956223989776848727 3378389934335984665273091)
      ·
        refine ⟨5067584901503976997909637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3378389934335984665273091 5067584901503976997909637)
        ·
          refine ⟨950172169031995687108057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5067584901503976997909637 950172169031995687108057)
          ·
            refine ⟨712629126773996765331043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950172169031995687108057 712629126773996765331043)
            ·
              refine ⟨1068943690160995147996565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712629126773996765331043 1068943690160995147996565)
              ·
                refine ⟨50106735476296647562339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1068943690160995147996565 50106735476296647562339)
                ·
                  rfl

theorem cell20_329341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_329341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329341 prefixEnd_329341 := by exact prefixLift 329341
  have htrace : WordTrace (prefixWord ++ tailWord_329341) baseStart_329341 baseEnd_329341 := by
    simpa [prefixWord, tailWord_329341, baseEnd_329341] using wordTrace_append hprefix tailTrace_329341
  have hstable : (prefixWord ++ tailWord_329341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329341).length < 2 ^ (prefixWord ++ tailWord_329341).sum := by decide
  have hdescent : baseEnd_329341 < baseStart_329341 := by decide
  rcases family_descends (prefixWord ++ tailWord_329341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329351 : List Nat := [1, 1, 4, 2, 1, 3, 3, 3, 2]
def baseStart_329351 : Nat := 118140960795 + 329351 * 2 ^ 59
def prefixEnd_329351 : Nat := 4983230072969 + 3 ^ 40 * 329351 * 2
def baseEnd_329351 : Nat := 150324770701374352353643

theorem tailTrace_329351 : CollatzResearch.WordTrace tailWord_329351 prefixEnd_329351 150324770701374352353643 := by
  unfold tailWord_329351
  simp only [CollatzResearch.WordTrace]
  refine ⟨12012417829825050517723907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8008278553216700345149271 12012417829825050517723907)
  ·
    refine ⟨18018626744737575776585861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12012417829825050517723907 18018626744737575776585861)
    ·
      refine ⟨3378492514638295458109849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18018626744737575776585861 3378492514638295458109849)
      ·
        refine ⟨2533869385978721593582387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3378492514638295458109849 2533869385978721593582387)
        ·
          refine ⟨3800804078968082390373581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533869385978721593582387 3800804078968082390373581)
          ·
            refine ⟨1425301529613030896390093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3800804078968082390373581 1425301529613030896390093)
            ·
              refine ⟨534488073604886586146285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1425301529613030896390093 534488073604886586146285)
              ·
                refine ⟨200433027601832469804857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 534488073604886586146285 200433027601832469804857)
                ·
                  refine ⟨150324770701374352353643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200433027601832469804857 150324770701374352353643)
                  ·
                    rfl

theorem cell20_329351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 2].length) (baseStart_329351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329351 prefixEnd_329351 := by exact prefixLift 329351
  have htrace : WordTrace (prefixWord ++ tailWord_329351) baseStart_329351 baseEnd_329351 := by
    simpa [prefixWord, tailWord_329351, baseEnd_329351] using wordTrace_append hprefix tailTrace_329351
  have hstable : (prefixWord ++ tailWord_329351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329351).length < 2 ^ (prefixWord ++ tailWord_329351).sum := by decide
  have hdescent : baseEnd_329351 < baseStart_329351 := by decide
  rcases family_descends (prefixWord ++ tailWord_329351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329368 : List Nat := [2, 1, 2, 4, 1, 3, 3, 2, 2]
def baseStart_329368 : Nat := 118140960795 + 329368 * 2 ^ 59
def prefixEnd_329368 : Nat := 4983230072969 + 3 ^ 40 * 329368 * 2
def baseEnd_329368 : Nat := 150332529964597848786907

theorem tailTrace_329368 : CollatzResearch.WordTrace tailWord_329368 prefixEnd_329368 150332529964597848786907 := by
  unfold tailWord_329368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006518935381731210546379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8008691913842308280728505 6006518935381731210546379)
  ·
    refine ⟨9009778403072596815819569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6006518935381731210546379 9009778403072596815819569)
    ·
      refine ⟨6757333802304447611864677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9009778403072596815819569 6757333802304447611864677)
      ·
        refine ⟨1267000087932083927224627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6757333802304447611864677 1267000087932083927224627)
        ·
          refine ⟨1900500131898125890836941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267000087932083927224627 1900500131898125890836941)
          ·
            refine ⟨712687549461797209063853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1900500131898125890836941 712687549461797209063853)
            ·
              refine ⟨267257831048173953398945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 712687549461797209063853 267257831048173953398945)
              ·
                refine ⟨200443373286130465049209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267257831048173953398945 200443373286130465049209)
                ·
                  refine ⟨150332529964597848786907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200443373286130465049209 150332529964597848786907)
                  ·
                    rfl

theorem cell20_329368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_329368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329368 prefixEnd_329368 := by exact prefixLift 329368
  have htrace : WordTrace (prefixWord ++ tailWord_329368) baseStart_329368 baseEnd_329368 := by
    simpa [prefixWord, tailWord_329368, baseEnd_329368] using wordTrace_append hprefix tailTrace_329368
  have hstable : (prefixWord ++ tailWord_329368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329368).length < 2 ^ (prefixWord ++ tailWord_329368).sum := by decide
  have hdescent : baseEnd_329368 < baseStart_329368 := by decide
  rcases family_descends (prefixWord ++ tailWord_329368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329378 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_329378 : Nat := 118140960795 + 329378 * 2 ^ 59
def prefixEnd_329378 : Nat := 4983230072969 + 3 ^ 40 * 329378 * 2
def baseEnd_329378 : Nat := 150337094237082258453533

theorem tailTrace_329378 : CollatzResearch.WordTrace tailWord_329378 prefixEnd_329378 150337094237082258453533 := by
  unfold tailWord_329378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3003350650181808532239197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8008935067151489419304525 3003350650181808532239197)
  ·
    refine ⟨1126256493818178199589699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3003350650181808532239197 1126256493818178199589699)
    ·
      refine ⟨1689384740727267299384549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1126256493818178199589699 1689384740727267299384549)
      ·
        refine ⟨316759638886362618634603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1689384740727267299384549 316759638886362618634603)
        ·
          refine ⟨475139458329543927951905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316759638886362618634603 475139458329543927951905)
          ·
            refine ⟨356354593747157945963929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475139458329543927951905 356354593747157945963929)
            ·
              refine ⟨267265945310368459472947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356354593747157945963929 267265945310368459472947)
              ·
                refine ⟨400898917965552689209421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267265945310368459472947 400898917965552689209421)
                ·
                  refine ⟨150337094237082258453533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400898917965552689209421 150337094237082258453533)
                  ·
                    rfl

theorem cell20_329378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_329378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329378 prefixEnd_329378 := by exact prefixLift 329378
  have htrace : WordTrace (prefixWord ++ tailWord_329378) baseStart_329378 baseEnd_329378 := by
    simpa [prefixWord, tailWord_329378, baseEnd_329378] using wordTrace_append hprefix tailTrace_329378
  have hstable : (prefixWord ++ tailWord_329378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329378).length < 2 ^ (prefixWord ++ tailWord_329378).sum := by decide
  have hdescent : baseEnd_329378 < baseStart_329378 := by decide
  rcases family_descends (prefixWord ++ tailWord_329378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329420 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_329420 : Nat := 118140960795 + 329420 * 2 ^ 59
def prefixEnd_329420 : Nat := 4983230072969 + 3 ^ 40 * 329420 * 2
def baseEnd_329420 : Nat := 150356264181516779053361

theorem tailTrace_329420 : CollatzResearch.WordTrace tailWord_329420 prefixEnd_329420 150356264181516779053361 := by
  unfold tailWord_329420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6007467233287537650992857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8009956311050050201323809 6007467233287537650992857)
  ·
    refine ⟨4505600424965653238244643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6007467233287537650992857 4505600424965653238244643)
    ·
      refine ⟨6758400637448479857366965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4505600424965653238244643 6758400637448479857366965)
      ·
        refine ⟨633600059760794986628153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6758400637448479857366965 633600059760794986628153)
        ·
          refine ⟨475200044820596239971115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633600059760794986628153 475200044820596239971115)
          ·
            refine ⟨712800067230894359956673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475200044820596239971115 712800067230894359956673)
            ·
              refine ⟨534600050423170769967505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712800067230894359956673 534600050423170769967505)
              ·
                refine ⟨400950037817378077475629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534600050423170769967505 400950037817378077475629)
                ·
                  refine ⟨150356264181516779053361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400950037817378077475629 150356264181516779053361)
                  ·
                    rfl

theorem cell20_329420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_329420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329420 prefixEnd_329420 := by exact prefixLift 329420
  have htrace : WordTrace (prefixWord ++ tailWord_329420) baseStart_329420 baseEnd_329420 := by
    simpa [prefixWord, tailWord_329420, baseEnd_329420] using wordTrace_append hprefix tailTrace_329420
  have hstable : (prefixWord ++ tailWord_329420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329420).length < 2 ^ (prefixWord ++ tailWord_329420).sum := by decide
  have hdescent : baseEnd_329420 < baseStart_329420 := by decide
  rcases family_descends (prefixWord ++ tailWord_329420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329430 : List Nat := [5, 2, 1, 3, 1, 2, 1, 5]
def baseStart_329430 : Nat := 118140960795 + 329430 * 2 ^ 59
def prefixEnd_329430 : Nat := 4983230072969 + 3 ^ 40 * 329430 * 2
def baseEnd_329430 : Nat := 50120276151333729573329

theorem tailTrace_329430 : CollatzResearch.WordTrace tailWord_329430 prefixEnd_329430 50120276151333729573329 := by
  unfold tailWord_329430
  simp only [CollatzResearch.WordTrace]
  refine ⟨750956199783677938115609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8010199464359231339899829 750956199783677938115609)
  ·
    refine ⟨563217149837758453586707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 750956199783677938115609 563217149837758453586707)
    ·
      refine ⟨844825724756637680380061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563217149837758453586707 844825724756637680380061)
      ·
        refine ⟨316809646783739130142523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 844825724756637680380061 316809646783739130142523)
        ·
          refine ⟨475214470175608695213785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316809646783739130142523 475214470175608695213785)
          ·
            refine ⟨356410852631706521410339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475214470175608695213785 356410852631706521410339)
            ·
              refine ⟨534616278947559782115509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356410852631706521410339 534616278947559782115509)
              ·
                refine ⟨50120276151333729573329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 534616278947559782115509 50120276151333729573329)
                ·
                  rfl

theorem cell20_329430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_329430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329430 prefixEnd_329430 := by exact prefixLift 329430
  have htrace : WordTrace (prefixWord ++ tailWord_329430) baseStart_329430 baseEnd_329430 := by
    simpa [prefixWord, tailWord_329430, baseEnd_329430] using wordTrace_append hprefix tailTrace_329430
  have hstable : (prefixWord ++ tailWord_329430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329430).length < 2 ^ (prefixWord ++ tailWord_329430).sum := by decide
  have hdescent : baseEnd_329430 < baseStart_329430 := by decide
  rcases family_descends (prefixWord ++ tailWord_329430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329431 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_329431 : Nat := 118140960795 + 329431 * 2 ^ 59
def prefixEnd_329431 : Nat := 4983230072969 + 3 ^ 40 * 329431 * 2
def baseEnd_329431 : Nat := 150361284881249629686649

theorem tailTrace_329431 : CollatzResearch.WordTrace tailWord_329431 prefixEnd_329431 150361284881249629686649 := by
  unfold tailWord_329431
  simp only [CollatzResearch.WordTrace]
  refine ⟨12015335669535224180636147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8010223779690149453757431 12015335669535224180636147)
  ·
    refine ⟨18023003504302836270954221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12015335669535224180636147 18023003504302836270954221)
    ·
      refine ⟨6758626314113563601607833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18023003504302836270954221 6758626314113563601607833)
      ·
        refine ⟨5068969735585172701205875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6758626314113563601607833 5068969735585172701205875)
        ·
          refine ⟨7603454603377759051808813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5068969735585172701205875 7603454603377759051808813)
          ·
            refine ⟨2851295476266659644428305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7603454603377759051808813 2851295476266659644428305)
            ·
              refine ⟨2138471607199994733321229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2851295476266659644428305 2138471607199994733321229)
              ·
                refine ⟨801926852699998024995461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2138471607199994733321229 801926852699998024995461)
                ·
                  refine ⟨150361284881249629686649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801926852699998024995461 150361284881249629686649)
                  ·
                    rfl

theorem cell20_329431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_329431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329431 prefixEnd_329431 := by exact prefixLift 329431
  have htrace : WordTrace (prefixWord ++ tailWord_329431) baseStart_329431 baseEnd_329431 := by
    simpa [prefixWord, tailWord_329431, baseEnd_329431] using wordTrace_append hprefix tailTrace_329431
  have hstable : (prefixWord ++ tailWord_329431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329431).length < 2 ^ (prefixWord ++ tailWord_329431).sum := by decide
  have hdescent : baseEnd_329431 < baseStart_329431 := by decide
  rcases family_descends (prefixWord ++ tailWord_329431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329448 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_329448 : Nat := 118140960795 + 329448 * 2 ^ 59
def prefixEnd_329448 : Nat := 4983230072969 + 3 ^ 40 * 329448 * 2
def baseEnd_329448 : Nat := 150369044144473126119913

theorem tailTrace_329448 : CollatzResearch.WordTrace tailWord_329448 prefixEnd_329448 150369044144473126119913 := by
  unfold tailWord_329448
  simp only [CollatzResearch.WordTrace]
  refine ⟨6007977855236818042002499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8010637140315757389336665 6007977855236818042002499)
  ·
    refine ⟨9011966782855227063003749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6007977855236818042002499 9011966782855227063003749)
    ·
      refine ⟨1689743771785355074313203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9011966782855227063003749 1689743771785355074313203)
      ·
        refine ⟨2534615657678032611469805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689743771785355074313203 2534615657678032611469805)
        ·
          refine ⟨950480871629262229301177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2534615657678032611469805 950480871629262229301177)
          ·
            refine ⟨712860653721946671975883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950480871629262229301177 712860653721946671975883)
            ·
              refine ⟨1069290980582920007963825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712860653721946671975883 1069290980582920007963825)
              ·
                refine ⟨801968235437190005972869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1069290980582920007963825 801968235437190005972869)
                ·
                  refine ⟨150369044144473126119913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 801968235437190005972869 150369044144473126119913)
                  ·
                    rfl

theorem cell20_329448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_329448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329448 prefixEnd_329448 := by exact prefixLift 329448
  have htrace : WordTrace (prefixWord ++ tailWord_329448) baseStart_329448 baseEnd_329448 := by
    simpa [prefixWord, tailWord_329448, baseEnd_329448] using wordTrace_append hprefix tailTrace_329448
  have hstable : (prefixWord ++ tailWord_329448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329448).length < 2 ^ (prefixWord ++ tailWord_329448).sum := by decide
  have hdescent : baseEnd_329448 < baseStart_329448 := by decide
  rcases family_descends (prefixWord ++ tailWord_329448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329455 : List Nat := [1, 1, 2, 1, 5, 1, 5, 4]
def baseStart_329455 : Nat := 118140960795 + 329455 * 2 ^ 59
def prefixEnd_329455 : Nat := 4983230072969 + 3 ^ 40 * 329455 * 2
def baseEnd_329455 : Nat := 50124079711737404295517

theorem tailTrace_329455 : CollatzResearch.WordTrace tailWord_329455 prefixEnd_329455 50124079711737404295517 := by
  unfold tailWord_329455
  simp only [CollatzResearch.WordTrace]
  refine ⟨12016211021448276279509819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8010807347632184186339879 12016211021448276279509819)
  ·
    refine ⟨18024316532172414419264729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12016211021448276279509819 18024316532172414419264729)
    ·
      refine ⟨13518237399129310814448547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18024316532172414419264729 13518237399129310814448547)
      ·
        refine ⟨20277356098693966221672821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13518237399129310814448547 20277356098693966221672821)
        ·
          refine ⟨1901002134252559333281827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20277356098693966221672821 1901002134252559333281827)
          ·
            refine ⟨2851503201378838999922741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901002134252559333281827 2851503201378838999922741)
            ·
              refine ⟨267328425129266156242757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2851503201378838999922741 267328425129266156242757)
              ·
                refine ⟨50124079711737404295517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267328425129266156242757 50124079711737404295517)
                ·
                  rfl

theorem cell20_329455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 4].length) (baseStart_329455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329455 prefixEnd_329455 := by exact prefixLift 329455
  have htrace : WordTrace (prefixWord ++ tailWord_329455) baseStart_329455 baseEnd_329455 := by
    simpa [prefixWord, tailWord_329455, baseEnd_329455] using wordTrace_append hprefix tailTrace_329455
  have hstable : (prefixWord ++ tailWord_329455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329455).length < 2 ^ (prefixWord ++ tailWord_329455).sum := by decide
  have hdescent : baseEnd_329455 < baseStart_329455 := by decide
  rcases family_descends (prefixWord ++ tailWord_329455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329479 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 5]
def baseStart_329479 : Nat := 118140960795 + 329479 * 2 ^ 59
def prefixEnd_329479 : Nat := 4983230072969 + 3 ^ 40 * 329479 * 2
def baseEnd_329479 : Nat := 150383193389174796086453

theorem tailTrace_329479 : CollatzResearch.WordTrace tailWord_329479 prefixEnd_329479 150383193389174796086453 := by
  unfold tailWord_329479
  simp only [CollatzResearch.WordTrace]
  refine ⟨12017086373361328378383491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8011390915574218918922327 12017086373361328378383491)
  ·
    refine ⟨18025629560041992567575237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12017086373361328378383491 18025629560041992567575237)
    ·
      refine ⟨3379805542507873606420357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18025629560041992567575237 3379805542507873606420357)
      ·
        refine ⟨633713539220226301203817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3379805542507873606420357 633713539220226301203817)
        ·
          refine ⟨475285154415169725902863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633713539220226301203817 475285154415169725902863)
          ·
            refine ⟨712927731622754588854295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475285154415169725902863 712927731622754588854295)
            ·
              refine ⟨1069391597434131883281443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712927731622754588854295 1069391597434131883281443)
              ·
                refine ⟨1604087396151197824922165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069391597434131883281443 1604087396151197824922165)
                ·
                  refine ⟨150383193389174796086453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1604087396151197824922165 150383193389174796086453)
                  ·
                    rfl

theorem cell20_329479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_329479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329479 prefixEnd_329479 := by exact prefixLift 329479
  have htrace : WordTrace (prefixWord ++ tailWord_329479) baseStart_329479 baseEnd_329479 := by
    simpa [prefixWord, tailWord_329479, baseEnd_329479] using wordTrace_append hprefix tailTrace_329479
  have hstable : (prefixWord ++ tailWord_329479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329479).length < 2 ^ (prefixWord ++ tailWord_329479).sum := by decide
  have hdescent : baseEnd_329479 < baseStart_329479 := by decide
  rcases family_descends (prefixWord ++ tailWord_329479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329507 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_329507 : Nat := 118140960795 + 329507 * 2 ^ 59
def prefixEnd_329507 : Nat := 4983230072969 + 3 ^ 40 * 329507 * 2
def baseEnd_329507 : Nat := 150395973352131143153005

theorem tailTrace_329507 : CollatzResearch.WordTrace tailWord_329507 prefixEnd_329507 150395973352131143153005 := by
  unfold tailWord_329507
  simp only [CollatzResearch.WordTrace]
  refine ⟨12018107617259889160402775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8012071744839926106935183 12018107617259889160402775)
  ·
    refine ⟨18027161425889833740604163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12018107617259889160402775 18027161425889833740604163)
    ·
      refine ⟨27040742138834750610906245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18027161425889833740604163 27040742138834750610906245)
      ·
        refine ⟨5070139151031515739544921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27040742138834750610906245 5070139151031515739544921)
        ·
          refine ⟨3802604363273636804658691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5070139151031515739544921 3802604363273636804658691)
          ·
            refine ⟨5703906544910455206988037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3802604363273636804658691 5703906544910455206988037)
            ·
              refine ⟨1069482477170710351310257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5703906544910455206988037 1069482477170710351310257)
              ·
                refine ⟨802111857878032763482693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1069482477170710351310257 802111857878032763482693)
                ·
                  refine ⟨150395973352131143153005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802111857878032763482693 150395973352131143153005)
                  ·
                    rfl

theorem cell20_329507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_329507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329507 prefixEnd_329507 := by exact prefixLift 329507
  have htrace : WordTrace (prefixWord ++ tailWord_329507) baseStart_329507 baseEnd_329507 := by
    simpa [prefixWord, tailWord_329507, baseEnd_329507] using wordTrace_append hprefix tailTrace_329507
  have hstable : (prefixWord ++ tailWord_329507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329507).length < 2 ^ (prefixWord ++ tailWord_329507).sum := by decide
  have hdescent : baseEnd_329507 < baseStart_329507 := by decide
  rcases family_descends (prefixWord ++ tailWord_329507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329541 : List Nat := [1, 3, 1, 1, 1, 2, 7, 2, 2]
def baseStart_329541 : Nat := 118140960795 + 329541 * 2 ^ 59
def prefixEnd_329541 : Nat := 4983230072969 + 3 ^ 40 * 329541 * 2
def baseEnd_329541 : Nat := 150411491878578136019533

theorem tailTrace_329541 : CollatzResearch.WordTrace tailWord_329541 prefixEnd_329541 150411491878578136019533 := by
  unfold tailWord_329541
  simp only [CollatzResearch.WordTrace]
  refine ⟨12019347699136712967140477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8012898466091141978093651 12019347699136712967140477)
  ·
    refine ⟨4507255387176267362677679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12019347699136712967140477 4507255387176267362677679)
    ·
      refine ⟨6760883080764401044016519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4507255387176267362677679 6760883080764401044016519)
      ·
        refine ⟨10141324621146601566024779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760883080764401044016519 10141324621146601566024779)
        ·
          refine ⟨15211986931719902349037169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10141324621146601566024779 15211986931719902349037169)
          ·
            refine ⟨11408990198789926761777877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15211986931719902349037169 11408990198789926761777877)
            ·
              refine ⟨267398207784138908479169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11408990198789926761777877 267398207784138908479169)
              ·
                refine ⟨200548655838104181359377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267398207784138908479169 200548655838104181359377)
                ·
                  refine ⟨150411491878578136019533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200548655838104181359377 150411491878578136019533)
                  ·
                    rfl

theorem cell20_329541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_329541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329541 prefixEnd_329541 := by exact prefixLift 329541
  have htrace : WordTrace (prefixWord ++ tailWord_329541) baseStart_329541 baseEnd_329541 := by
    simpa [prefixWord, tailWord_329541, baseEnd_329541] using wordTrace_append hprefix tailTrace_329541
  have hstable : (prefixWord ++ tailWord_329541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329541).length < 2 ^ (prefixWord ++ tailWord_329541).sum := by decide
  have hdescent : baseEnd_329541 < baseStart_329541 := by decide
  rcases family_descends (prefixWord ++ tailWord_329541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329600 : List Nat := [2, 1, 1, 2, 1, 2, 5, 4, 2]
def baseStart_329600 : Nat := 118140960795 + 329600 * 2 ^ 59
def prefixEnd_329600 : Nat := 4983230072969 + 3 ^ 40 * 329600 * 2
def baseEnd_329600 : Nat := 150438421086236153052625

theorem tailTrace_329600 : CollatzResearch.WordTrace tailWord_329600 prefixEnd_329600 150438421086236153052625 := by
  unfold tailWord_329600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6010749802961483021769127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8014333070615310695692169 6010749802961483021769127)
  ·
    refine ⟨9016124704442224532653691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6010749802961483021769127 9016124704442224532653691)
    ·
      refine ⟨13524187056663336798980537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9016124704442224532653691 13524187056663336798980537)
      ·
        refine ⟨10143140292497502599235403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13524187056663336798980537 10143140292497502599235403)
        ·
          refine ⟨15214710438746253898853105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10143140292497502599235403 15214710438746253898853105)
          ·
            refine ⟨11411032829059690424139829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15214710438746253898853105 11411032829059690424139829)
            ·
              refine ⟨1069784327724345977263109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11411032829059690424139829 1069784327724345977263109)
              ·
                refine ⟨200584561448314870736833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1069784327724345977263109 200584561448314870736833)
                ·
                  refine ⟨150438421086236153052625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200584561448314870736833 150438421086236153052625)
                  ·
                    rfl

theorem cell20_329600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_329600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329600 prefixEnd_329600 := by exact prefixLift 329600
  have htrace : WordTrace (prefixWord ++ tailWord_329600) baseStart_329600 baseEnd_329600 := by
    simpa [prefixWord, tailWord_329600, baseEnd_329600] using wordTrace_append hprefix tailTrace_329600
  have hstable : (prefixWord ++ tailWord_329600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329600).length < 2 ^ (prefixWord ++ tailWord_329600).sum := by decide
  have hdescent : baseEnd_329600 < baseStart_329600 := by decide
  rcases family_descends (prefixWord ++ tailWord_329600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329621 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_329621 : Nat := 118140960795 + 329621 * 2 ^ 59
def prefixEnd_329621 : Nat := 4983230072969 + 3 ^ 40 * 329621 * 2
def baseEnd_329621 : Nat := 150448006058453413352539

theorem tailTrace_329621 : CollatzResearch.WordTrace tailWord_329621 prefixEnd_329621 150448006058453413352539 := by
  unfold tailWord_329621
  simp only [CollatzResearch.WordTrace]
  refine ⟨12022265538846886630052717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8014843692564591086701811 12022265538846886630052717)
  ·
    refine ⟨4508349577067582486269769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12022265538846886630052717 4508349577067582486269769)
    ·
      refine ⟨3381262182800686864702327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4508349577067582486269769 3381262182800686864702327)
      ·
        refine ⟨5071893274201030297053491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3381262182800686864702327 5071893274201030297053491)
        ·
          refine ⟨7607839911301545445580237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5071893274201030297053491 7607839911301545445580237)
          ·
            refine ⟨2852939966738079542092589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7607839911301545445580237 2852939966738079542092589)
            ·
              refine ⟨1069852487526779828284721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2852939966738079542092589 1069852487526779828284721)
              ·
                refine ⟨802389365645084871213541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1069852487526779828284721 802389365645084871213541)
                ·
                  refine ⟨150448006058453413352539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802389365645084871213541 150448006058453413352539)
                  ·
                    rfl

theorem cell20_329621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_329621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329621 prefixEnd_329621 := by exact prefixLift 329621
  have htrace : WordTrace (prefixWord ++ tailWord_329621) baseStart_329621 baseEnd_329621 := by
    simpa [prefixWord, tailWord_329621, baseEnd_329621] using wordTrace_append hprefix tailTrace_329621
  have hstable : (prefixWord ++ tailWord_329621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329621).length < 2 ^ (prefixWord ++ tailWord_329621).sum := by decide
  have hdescent : baseEnd_329621 < baseStart_329621 := by decide
  rcases family_descends (prefixWord ++ tailWord_329621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329634 : List Nat := [3, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_329634 : Nat := 118140960795 + 329634 * 2 ^ 59
def prefixEnd_329634 : Nat := 4983230072969 + 3 ^ 40 * 329634 * 2
def baseEnd_329634 : Nat := 150453939612683145919153

theorem tailTrace_329634 : CollatzResearch.WordTrace tailWord_329634 prefixEnd_329634 150453939612683145919153 := by
  unfold tailWord_329634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005684921949947462568989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8015159791866526566850637 3005684921949947462568989)
  ·
    refine ⟨1127131845731230298463371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3005684921949947462568989 1127131845731230298463371)
    ·
      refine ⟨1690697768596845447695057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127131845731230298463371 1690697768596845447695057)
      ·
        refine ⟨1268023326447634085771293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1690697768596845447695057 1268023326447634085771293)
        ·
          refine ⟨475508747417862782164235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1268023326447634085771293 475508747417862782164235)
          ·
            refine ⟨713263121126794173246353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475508747417862782164235 713263121126794173246353)
            ·
              refine ⟨534947340845095629934765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713263121126794173246353 534947340845095629934765)
              ·
                refine ⟨200605252816910861225537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 534947340845095629934765 200605252816910861225537)
                ·
                  refine ⟨150453939612683145919153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200605252816910861225537 150453939612683145919153)
                  ·
                    rfl

theorem cell20_329634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_329634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329634 prefixEnd_329634 := by exact prefixLift 329634
  have htrace : WordTrace (prefixWord ++ tailWord_329634) baseStart_329634 baseEnd_329634 := by
    simpa [prefixWord, tailWord_329634, baseEnd_329634] using wordTrace_append hprefix tailTrace_329634
  have hstable : (prefixWord ++ tailWord_329634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329634).length < 2 ^ (prefixWord ++ tailWord_329634).sum := by decide
  have hdescent : baseEnd_329634 < baseStart_329634 := by decide
  rcases family_descends (prefixWord ++ tailWord_329634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329635 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_329635 : Nat := 118140960795 + 329635 * 2 ^ 59
def prefixEnd_329635 : Nat := 4983230072969 + 3 ^ 40 * 329635 * 2
def baseEnd_329635 : Nat := 150454396039931586885815

theorem tailTrace_329635 : CollatzResearch.WordTrace tailWord_329635 prefixEnd_329635 150454396039931586885815 := by
  unfold tailWord_329635
  simp only [CollatzResearch.WordTrace]
  refine ⟨12022776160796167021062359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8015184107197444680708239 12022776160796167021062359)
  ·
    refine ⟨18034164241194250531593539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12022776160796167021062359 18034164241194250531593539)
    ·
      refine ⟨27051246361791375797390309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18034164241194250531593539 27051246361791375797390309)
      ·
        refine ⟨5072108692835882962010683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27051246361791375797390309 5072108692835882962010683)
        ·
          refine ⟨7608163039253824443016025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5072108692835882962010683 7608163039253824443016025)
          ·
            refine ⟨5706122279440368332262019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7608163039253824443016025 5706122279440368332262019)
            ·
              refine ⟨8559183419160552498393029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5706122279440368332262019 8559183419160552498393029)
              ·
                refine ⟨1604846891092603593448693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8559183419160552498393029 1604846891092603593448693)
                ·
                  refine ⟨150454396039931586885815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1604846891092603593448693 150454396039931586885815)
                  ·
                    rfl

theorem cell20_329635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_329635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329635 prefixEnd_329635 := by exact prefixLift 329635
  have htrace : WordTrace (prefixWord ++ tailWord_329635) baseStart_329635 baseEnd_329635 := by
    simpa [prefixWord, tailWord_329635, baseEnd_329635] using wordTrace_append hprefix tailTrace_329635
  have hstable : (prefixWord ++ tailWord_329635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329635).length < 2 ^ (prefixWord ++ tailWord_329635).sum := by decide
  have hdescent : baseEnd_329635 < baseStart_329635 := by decide
  rcases family_descends (prefixWord ++ tailWord_329635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329710 : List Nat := [4, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_329710 : Nat := 118140960795 + 329710 * 2 ^ 59
def prefixEnd_329710 : Nat := 4983230072969 + 3 ^ 40 * 329710 * 2
def baseEnd_329710 : Nat := 150488628083564659385509

theorem tailTrace_329710 : CollatzResearch.WordTrace tailWord_329710 prefixEnd_329710 150488628083564659385509 := by
  unfold tailWord_329710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503188954440556853755323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8017007757016303220028389 1503188954440556853755323)
  ·
    refine ⟨2254783431660835280632985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1503188954440556853755323 2254783431660835280632985)
    ·
      refine ⟨1691087573745626460474739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2254783431660835280632985 1691087573745626460474739)
      ·
        refine ⟨2536631360618439690712109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691087573745626460474739 2536631360618439690712109)
        ·
          refine ⟨951236760231914884017041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2536631360618439690712109 951236760231914884017041)
          ·
            refine ⟨713427570173936163012781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951236760231914884017041 713427570173936163012781)
            ·
              refine ⟨267535338815226061129793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 713427570173936163012781 267535338815226061129793)
              ·
                refine ⟨200651504111419545847345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267535338815226061129793 200651504111419545847345)
                ·
                  refine ⟨150488628083564659385509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200651504111419545847345 150488628083564659385509)
                  ·
                    rfl

theorem cell20_329710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_329710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329710 prefixEnd_329710 := by exact prefixLift 329710
  have htrace : WordTrace (prefixWord ++ tailWord_329710) baseStart_329710 baseEnd_329710 := by
    simpa [prefixWord, tailWord_329710, baseEnd_329710] using wordTrace_append hprefix tailTrace_329710
  have hstable : (prefixWord ++ tailWord_329710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329710).length < 2 ^ (prefixWord ++ tailWord_329710).sum := by decide
  have hdescent : baseEnd_329710 < baseStart_329710 := by decide
  rcases family_descends (prefixWord ++ tailWord_329710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329711 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_329711 : Nat := 118140960795 + 329711 * 2 ^ 59
def prefixEnd_329711 : Nat := 4983230072969 + 3 ^ 40 * 329711 * 2
def baseEnd_329711 : Nat := 150489084510813100352171

theorem tailTrace_329711 : CollatzResearch.WordTrace tailWord_329711 prefixEnd_329711 150489084510813100352171 := by
  unfold tailWord_329711
  simp only [CollatzResearch.WordTrace]
  refine ⟨12025548108520832000828987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8017032072347221333885991 12025548108520832000828987)
  ·
    refine ⟨18038322162781248001243481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12025548108520832000828987 18038322162781248001243481)
    ·
      refine ⟨13528741622085936000932611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18038322162781248001243481 13528741622085936000932611)
      ·
        refine ⟨20293112433128904001398917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13528741622085936000932611 20293112433128904001398917)
        ·
          refine ⟨3804958581211669500262297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20293112433128904001398917 3804958581211669500262297)
          ·
            refine ⟨2853718935908752125196723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3804958581211669500262297 2853718935908752125196723)
            ·
              refine ⟨4280578403863128187795085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853718935908752125196723 4280578403863128187795085)
              ·
                refine ⟨1605216901448673070423157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4280578403863128187795085 1605216901448673070423157)
                ·
                  refine ⟨150489084510813100352171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1605216901448673070423157 150489084510813100352171)
                  ·
                    rfl

theorem cell20_329711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_329711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329711 prefixEnd_329711 := by exact prefixLift 329711
  have htrace : WordTrace (prefixWord ++ tailWord_329711) baseStart_329711 baseEnd_329711 := by
    simpa [prefixWord, tailWord_329711, baseEnd_329711] using wordTrace_append hprefix tailTrace_329711
  have hstable : (prefixWord ++ tailWord_329711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329711).length < 2 ^ (prefixWord ++ tailWord_329711).sum := by decide
  have hdescent : baseEnd_329711 < baseStart_329711 := by decide
  rcases family_descends (prefixWord ++ tailWord_329711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329742 : List Nat := [4, 1, 1, 2, 2, 1, 1, 8]
def baseStart_329742 : Nat := 118140960795 + 329742 * 2 ^ 59
def prefixEnd_329742 : Nat := 4983230072969 + 3 ^ 40 * 329742 * 2
def baseEnd_329742 : Nat := 50167744585171590106237

theorem tailTrace_329742 : CollatzResearch.WordTrace tailWord_329742 prefixEnd_329742 50167744585171590106237 := by
  unfold tailWord_329742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503334846426065536900935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8017785847605682863471653 1503334846426065536900935)
  ·
    refine ⟨2255002269639098305351403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1503334846426065536900935 2255002269639098305351403)
    ·
      refine ⟨3382503404458647458027105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255002269639098305351403 3382503404458647458027105)
      ·
        refine ⟨2536877553343985593520329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3382503404458647458027105 2536877553343985593520329)
        ·
          refine ⟨1902658165007989195140247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2536877553343985593520329 1902658165007989195140247)
          ·
            refine ⟨2853987247511983792710371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902658165007989195140247 2853987247511983792710371)
            ·
              refine ⟨4280980871267975689065557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853987247511983792710371 4280980871267975689065557)
              ·
                refine ⟨50167744585171590106237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4280980871267975689065557 50167744585171590106237)
                ·
                  rfl

theorem cell20_329742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_329742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329742 prefixEnd_329742 := by exact prefixLift 329742
  have htrace : WordTrace (prefixWord ++ tailWord_329742) baseStart_329742 baseEnd_329742 := by
    simpa [prefixWord, tailWord_329742, baseEnd_329742] using wordTrace_append hprefix tailTrace_329742
  have hstable : (prefixWord ++ tailWord_329742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329742).length < 2 ^ (prefixWord ++ tailWord_329742).sum := by decide
  have hdescent : baseEnd_329742 < baseStart_329742 := by decide
  rcases family_descends (prefixWord ++ tailWord_329742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329752 : List Nat := [2, 1, 2, 3, 2, 1, 2, 5, 2]
def baseStart_329752 : Nat := 118140960795 + 329752 * 2 ^ 59
def prefixEnd_329752 : Nat := 4983230072969 + 3 ^ 40 * 329752 * 2
def baseEnd_329752 : Nat := 150507798027999179985337

theorem tailTrace_329752 : CollatzResearch.WordTrace tailWord_329752 prefixEnd_329752 150507798027999179985337 := by
  unfold tailWord_329752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6013521750686148001535755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8018029000914864002047673 6013521750686148001535755)
  ·
    refine ⟨9020282626029222002303633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6013521750686148001535755 9020282626029222002303633)
    ·
      refine ⟨6765211969521916501727725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9020282626029222002303633 6765211969521916501727725)
      ·
        refine ⟨2536954488570718688147897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6765211969521916501727725 2536954488570718688147897)
        ·
          refine ⟨1902715866428039016110923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2536954488570718688147897 1902715866428039016110923)
          ·
            refine ⟨2854073799642058524166385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902715866428039016110923 2854073799642058524166385)
            ·
              refine ⟨2140555349731543893124789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2854073799642058524166385 2140555349731543893124789)
              ·
                refine ⟨200677064037332239980449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2140555349731543893124789 200677064037332239980449)
                ·
                  refine ⟨150507798027999179985337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200677064037332239980449 150507798027999179985337)
                  ·
                    rfl

theorem cell20_329752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_329752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329752 prefixEnd_329752 := by exact prefixLift 329752
  have htrace : WordTrace (prefixWord ++ tailWord_329752) baseStart_329752 baseEnd_329752 := by
    simpa [prefixWord, tailWord_329752, baseEnd_329752] using wordTrace_append hprefix tailTrace_329752
  have hstable : (prefixWord ++ tailWord_329752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329752).length < 2 ^ (prefixWord ++ tailWord_329752).sum := by decide
  have hdescent : baseEnd_329752 < baseStart_329752 := by decide
  rcases family_descends (prefixWord ++ tailWord_329752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329814 : List Nat := [5, 2, 2, 1, 1, 2, 7]
def baseStart_329814 : Nat := 118140960795 + 329814 * 2 ^ 59
def prefixEnd_329814 : Nat := 4983230072969 + 3 ^ 40 * 329814 * 2
def baseEnd_329814 : Nat := 16726232946378057768713

theorem tailTrace_329814 : CollatzResearch.WordTrace tailWord_329814 prefixEnd_329814 16726232946378057768713 := by
  unfold tailWord_329814
  simp only [CollatzResearch.WordTrace]
  refine ⟨751831551696730036989281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8019536551431787061218997 751831551696730036989281)
  ·
    refine ⟨563873663772547527741961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 751831551696730036989281 563873663772547527741961)
    ·
      refine ⟨422905247829410645806471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 563873663772547527741961 422905247829410645806471)
      ·
        refine ⟨634357871744115968709707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422905247829410645806471 634357871744115968709707)
        ·
          refine ⟨951536807616173953064561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634357871744115968709707 951536807616173953064561)
          ·
            refine ⟨713652605712130464798421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951536807616173953064561 713652605712130464798421)
            ·
              refine ⟨16726232946378057768713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 713652605712130464798421 16726232946378057768713)
              ·
                rfl

theorem cell20_329814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 7].length) (baseStart_329814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329814 prefixEnd_329814 := by exact prefixLift 329814
  have htrace : WordTrace (prefixWord ++ tailWord_329814) baseStart_329814 baseEnd_329814 := by
    simpa [prefixWord, tailWord_329814, baseEnd_329814] using wordTrace_append hprefix tailTrace_329814
  have hstable : (prefixWord ++ tailWord_329814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329814).length < 2 ^ (prefixWord ++ tailWord_329814).sum := by decide
  have hdescent : baseEnd_329814 < baseStart_329814 := by decide
  rcases family_descends (prefixWord ++ tailWord_329814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329821 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 5]
def baseStart_329821 : Nat := 118140960795 + 329821 * 2 ^ 59
def prefixEnd_329821 : Nat := 4983230072969 + 3 ^ 40 * 329821 * 2
def baseEnd_329821 : Nat := 150539291508141606685055

theorem tailTrace_329821 : CollatzResearch.WordTrace tailWord_329821 prefixEnd_329821 150539291508141606685055 := by
  unfold tailWord_329821
  simp only [CollatzResearch.WordTrace]
  refine ⟨12029560138122320787333317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8019706758748213858222211 12029560138122320787333317)
  ·
    refine ⟨2255542525897935147624997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12029560138122320787333317 2255542525897935147624997)
    ·
      refine ⟨422914223605862840179687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2255542525897935147624997 422914223605862840179687)
      ·
        refine ⟨634371335408794260269531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422914223605862840179687 634371335408794260269531)
        ·
          refine ⟨951557003113191390404297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634371335408794260269531 951557003113191390404297)
          ·
            refine ⟨713667752334893542803223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951557003113191390404297 713667752334893542803223)
            ·
              refine ⟨1070501628502340314204835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713667752334893542803223 1070501628502340314204835)
              ·
                refine ⟨1605752442753510471307253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070501628502340314204835 1605752442753510471307253)
                ·
                  refine ⟨150539291508141606685055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1605752442753510471307253 150539291508141606685055)
                  ·
                    rfl

theorem cell20_329821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_329821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329821 prefixEnd_329821 := by exact prefixLift 329821
  have htrace : WordTrace (prefixWord ++ tailWord_329821) baseStart_329821 baseEnd_329821 := by
    simpa [prefixWord, tailWord_329821, baseEnd_329821] using wordTrace_append hprefix tailTrace_329821
  have hstable : (prefixWord ++ tailWord_329821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329821).length < 2 ^ (prefixWord ++ tailWord_329821).sum := by decide
  have hdescent : baseEnd_329821 < baseStart_329821 := by decide
  rcases family_descends (prefixWord ++ tailWord_329821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329828 : List Nat := [2, 3, 1, 1, 2, 1, 4, 4, 2]
def baseStart_329828 : Nat := 118140960795 + 329828 * 2 ^ 59
def prefixEnd_329828 : Nat := 4983230072969 + 3 ^ 40 * 329828 * 2
def baseEnd_329828 : Nat := 150542486498880693451693

theorem tailTrace_329828 : CollatzResearch.WordTrace tailWord_329828 prefixEnd_329828 150542486498880693451693 := by
  unfold tailWord_329828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6014907724548480491419069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8019876966064640655225425 6014907724548480491419069)
  ·
    refine ⟨2255590396705680184282151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6014907724548480491419069 2255590396705680184282151)
    ·
      refine ⟨3383385595058520276423227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255590396705680184282151 3383385595058520276423227)
      ·
        refine ⟨5075078392587780414634841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383385595058520276423227 5075078392587780414634841)
        ·
          refine ⟨3806308794440835310976131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5075078392587780414634841 3806308794440835310976131)
          ·
            refine ⟨5709463191661252966464197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806308794440835310976131 5709463191661252966464197)
            ·
              refine ⟨1070524348436484931212037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5709463191661252966464197 1070524348436484931212037)
              ·
                refine ⟨200723315331840924602257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1070524348436484931212037 200723315331840924602257)
                ·
                  refine ⟨150542486498880693451693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200723315331840924602257 150542486498880693451693)
                  ·
                    rfl

theorem cell20_329828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_329828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329828 prefixEnd_329828 := by exact prefixLift 329828
  have htrace : WordTrace (prefixWord ++ tailWord_329828) baseStart_329828 baseEnd_329828 := by
    simpa [prefixWord, tailWord_329828, baseEnd_329828] using wordTrace_append hprefix tailTrace_329828
  have hstable : (prefixWord ++ tailWord_329828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329828).length < 2 ^ (prefixWord ++ tailWord_329828).sum := by decide
  have hdescent : baseEnd_329828 < baseStart_329828 := by decide
  rcases family_descends (prefixWord ++ tailWord_329828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329849 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_329849 : Nat := 118140960795 + 329849 * 2 ^ 59
def prefixEnd_329849 : Nat := 4983230072969 + 3 ^ 40 * 329849 * 2
def baseEnd_329849 : Nat := 150552071471097953751607

theorem tailTrace_329849 : CollatzResearch.WordTrace tailWord_329849 prefixEnd_329849 150552071471097953751607 := by
  unfold tailWord_329849
  simp only [CollatzResearch.WordTrace]
  refine ⟨12030581382020881569352601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8020387588013921046235067 12030581382020881569352601)
  ·
    refine ⟨9022936036515661177014451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12030581382020881569352601 9022936036515661177014451)
    ·
      refine ⟨13534404054773491765521677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9022936036515661177014451 13534404054773491765521677)
      ·
        refine ⟨5075401520540059412070629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13534404054773491765521677 5075401520540059412070629)
        ·
          refine ⟨951637785101261139763243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5075401520540059412070629 951637785101261139763243)
          ·
            refine ⟨1427456677651891709644865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951637785101261139763243 1427456677651891709644865)
            ·
              refine ⟨1070592508238918782233649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1427456677651891709644865 1070592508238918782233649)
              ·
                refine ⟨802944381179189086675237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070592508238918782233649 802944381179189086675237)
                ·
                  refine ⟨150552071471097953751607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 802944381179189086675237 150552071471097953751607)
                  ·
                    rfl

theorem cell20_329849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_329849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329849 prefixEnd_329849 := by exact prefixLift 329849
  have htrace : WordTrace (prefixWord ++ tailWord_329849) baseStart_329849 baseEnd_329849 := by
    simpa [prefixWord, tailWord_329849, baseEnd_329849] using wordTrace_append hprefix tailTrace_329849
  have hstable : (prefixWord ++ tailWord_329849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329849).length < 2 ^ (prefixWord ++ tailWord_329849).sum := by decide
  have hdescent : baseEnd_329849 < baseStart_329849 := by decide
  rcases family_descends (prefixWord ++ tailWord_329849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329863 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_329863 : Nat := 118140960795 + 329863 * 2 ^ 59
def prefixEnd_329863 : Nat := 4983230072969 + 3 ^ 40 * 329863 * 2
def baseEnd_329863 : Nat := 150558461452576127284883

theorem tailTrace_329863 : CollatzResearch.WordTrace tailWord_329863 prefixEnd_329863 150558461452576127284883 := by
  unfold tailWord_329863
  simp only [CollatzResearch.WordTrace]
  refine ⟨12031092003970161960362243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8020728002646774640241495 12031092003970161960362243)
  ·
    refine ⟨18046638005955242940543365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12031092003970161960362243 18046638005955242940543365)
    ·
      refine ⟨3383744626116608051351881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18046638005955242940543365 3383744626116608051351881)
      ·
        refine ⟨2537808469587456038513911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3383744626116608051351881 2537808469587456038513911)
        ·
          refine ⟨3806712704381184057770867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537808469587456038513911 3806712704381184057770867)
          ·
            refine ⟨5710069056571776086656301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806712704381184057770867 5710069056571776086656301)
            ·
              refine ⟨2141275896214416032496113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5710069056571776086656301 2141275896214416032496113)
              ·
                refine ⟨1605956922160812024372085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2141275896214416032496113 1605956922160812024372085)
                ·
                  refine ⟨150558461452576127284883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1605956922160812024372085 150558461452576127284883)
                  ·
                    rfl

theorem cell20_329863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_329863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329863 prefixEnd_329863 := by exact prefixLift 329863
  have htrace : WordTrace (prefixWord ++ tailWord_329863) baseStart_329863 baseEnd_329863 := by
    simpa [prefixWord, tailWord_329863, baseEnd_329863] using wordTrace_append hprefix tailTrace_329863
  have hstable : (prefixWord ++ tailWord_329863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329863).length < 2 ^ (prefixWord ++ tailWord_329863).sum := by decide
  have hdescent : baseEnd_329863 < baseStart_329863 := by decide
  rcases family_descends (prefixWord ++ tailWord_329863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329915 : List Nat := [1, 1, 1, 1, 1, 2, 5, 8]
def baseStart_329915 : Nat := 118140960795 + 329915 * 2 ^ 59
def prefixEnd_329915 : Nat := 4983230072969 + 3 ^ 40 * 329915 * 2
def baseEnd_329915 : Nat := 50194065223165019183779

theorem tailTrace_329915 : CollatzResearch.WordTrace tailWord_329915 prefixEnd_329915 50194065223165019183779 := by
  unfold tailWord_329915
  simp only [CollatzResearch.WordTrace]
  refine ⟨12032988599781774841255199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8021992399854516560836799 12032988599781774841255199)
  ·
    refine ⟨18049482899672662261882799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12032988599781774841255199 18049482899672662261882799)
    ·
      refine ⟨27074224349508993392824199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18049482899672662261882799 27074224349508993392824199)
      ·
        refine ⟨40611336524263490089236299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27074224349508993392824199 40611336524263490089236299)
        ·
          refine ⟨60917004786395235133854449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40611336524263490089236299 60917004786395235133854449)
          ·
            refine ⟨45687753589796426350390837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60917004786395235133854449 45687753589796426350390837)
            ·
              refine ⟨4283226899043414970349141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45687753589796426350390837 4283226899043414970349141)
              ·
                refine ⟨50194065223165019183779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4283226899043414970349141 50194065223165019183779)
                ·
                  rfl

theorem cell20_329915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_329915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329915 prefixEnd_329915 := by exact prefixLift 329915
  have htrace : WordTrace (prefixWord ++ tailWord_329915) baseStart_329915 baseEnd_329915 := by
    simpa [prefixWord, tailWord_329915, baseEnd_329915] using wordTrace_append hprefix tailTrace_329915
  have hstable : (prefixWord ++ tailWord_329915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329915).length < 2 ^ (prefixWord ++ tailWord_329915).sum := by decide
  have hdescent : baseEnd_329915 < baseStart_329915 := by decide
  rcases family_descends (prefixWord ++ tailWord_329915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329932 : List Nat := [2, 2, 1, 6, 9]
def baseStart_329932 : Nat := 118140960795 + 329932 * 2 ^ 59
def prefixEnd_329932 : Nat := 4983230072969 + 3 ^ 40 * 329932 * 2
def baseEnd_329932 : Nat := 1859135246082945110921

theorem tailTrace_329932 : CollatzResearch.WordTrace tailWord_329932 prefixEnd_329932 1859135246082945110921 := by
  unfold tailWord_329932
  simp only [CollatzResearch.WordTrace]
  refine ⟨6016804320360093372312025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8022405760480124496416033 6016804320360093372312025)
  ·
    refine ⟨4512603240270070029234019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6016804320360093372312025 4512603240270070029234019)
    ·
      refine ⟨6768904860405105043851029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4512603240270070029234019 6768904860405105043851029)
      ·
        refine ⟨317292415331489298930517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6768904860405105043851029 317292415331489298930517)
        ·
          refine ⟨1859135246082945110921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 317292415331489298930517 1859135246082945110921)
          ·
            rfl

theorem cell20_329932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 9].length) (baseStart_329932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329932 prefixEnd_329932 := by exact prefixLift 329932
  have htrace : WordTrace (prefixWord ++ tailWord_329932) baseStart_329932 baseEnd_329932 := by
    simpa [prefixWord, tailWord_329932, baseEnd_329932] using wordTrace_append hprefix tailTrace_329932
  have hstable : (prefixWord ++ tailWord_329932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329932).length < 2 ^ (prefixWord ++ tailWord_329932).sum := by decide
  have hdescent : baseEnd_329932 < baseStart_329932 := by decide
  rcases family_descends (prefixWord ++ tailWord_329932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329938 : List Nat := [3, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_329938 : Nat := 118140960795 + 329938 * 2 ^ 59
def prefixEnd_329938 : Nat := 4983230072969 + 3 ^ 40 * 329938 * 2
def baseEnd_329938 : Nat := 150592693496209199784577

theorem tailTrace_329938 : CollatzResearch.WordTrace tailWord_329938 prefixEnd_329938 150592693496209199784577 := by
  unfold tailWord_329938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008456869674612442335617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8022551652465633179561645 3008456869674612442335617)
  ·
    refine ⟨2256342652255959331751713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3008456869674612442335617 2256342652255959331751713)
    ·
      refine ⟨1692256989191969498813785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2256342652255959331751713 1692256989191969498813785)
      ·
        refine ⟨1269192741893977124110339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1692256989191969498813785 1269192741893977124110339)
        ·
          refine ⟨1903789112840965686165509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269192741893977124110339 1903789112840965686165509)
          ·
            refine ⟨356960458657681066156033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1903789112840965686165509 356960458657681066156033)
            ·
              refine ⟨267720343993260799617025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356960458657681066156033 267720343993260799617025)
              ·
                refine ⟨200790257994945599712769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267720343993260799617025 200790257994945599712769)
                ·
                  refine ⟨150592693496209199784577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200790257994945599712769 150592693496209199784577)
                  ·
                    rfl

theorem cell20_329938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_329938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329938 prefixEnd_329938 := by exact prefixLift 329938
  have htrace : WordTrace (prefixWord ++ tailWord_329938) baseStart_329938 baseEnd_329938 := by
    simpa [prefixWord, tailWord_329938, baseEnd_329938] using wordTrace_append hprefix tailTrace_329938
  have hstable : (prefixWord ++ tailWord_329938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329938).length < 2 ^ (prefixWord ++ tailWord_329938).sum := by decide
  have hdescent : baseEnd_329938 < baseStart_329938 := by decide
  rcases family_descends (prefixWord ++ tailWord_329938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329949 : List Nat := [1, 4, 3, 2, 1, 1, 3, 5]
def baseStart_329949 : Nat := 118140960795 + 329949 * 2 ^ 59
def prefixEnd_329949 : Nat := 4983230072969 + 3 ^ 40 * 329949 * 2
def baseEnd_329949 : Nat := 50199238065314016805955

theorem tailTrace_329949 : CollatzResearch.WordTrace tailWord_329949 prefixEnd_329949 50199238065314016805955 := by
  unfold tailWord_329949
  simp only [CollatzResearch.WordTrace]
  refine ⟨12034228681658598647992901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8022819121105732431995267 12034228681658598647992901)
  ·
    refine ⟨2256417877810987246498669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12034228681658598647992901 2256417877810987246498669)
    ·
      refine ⟨846156704179120217437001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2256417877810987246498669 846156704179120217437001)
      ·
        refine ⟨634617528134340163077751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 846156704179120217437001 634617528134340163077751)
        ·
          refine ⟨951926292201510244616627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634617528134340163077751 951926292201510244616627)
          ·
            refine ⟨1427889438302265366924941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951926292201510244616627 1427889438302265366924941)
            ·
              refine ⟨535458539363349512596853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1427889438302265366924941 535458539363349512596853)
              ·
                refine ⟨50199238065314016805955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 535458539363349512596853 50199238065314016805955)
                ·
                  rfl

theorem cell20_329949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_329949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329949 prefixEnd_329949 := by exact prefixLift 329949
  have htrace : WordTrace (prefixWord ++ tailWord_329949) baseStart_329949 baseEnd_329949 := by
    simpa [prefixWord, tailWord_329949, baseEnd_329949] using wordTrace_append hprefix tailTrace_329949
  have hstable : (prefixWord ++ tailWord_329949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329949).length < 2 ^ (prefixWord ++ tailWord_329949).sum := by decide
  have hdescent : baseEnd_329949 < baseStart_329949 := by decide
  rcases family_descends (prefixWord ++ tailWord_329949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329980 : List Nat := [2, 2, 2, 1, 4, 1, 1, 5, 2]
def baseStart_329980 : Nat := 118140960795 + 329980 * 2 ^ 59
def prefixEnd_329980 : Nat := 4983230072969 + 3 ^ 40 * 329980 * 2
def baseEnd_329980 : Nat := 150611863440643720384405

theorem tailTrace_329980 : CollatzResearch.WordTrace tailWord_329980 prefixEnd_329980 150611863440643720384405 := by
  unfold tailWord_329980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6017679672273145471185697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8023572896364193961580929 6017679672273145471185697)
  ·
    refine ⟨4513259754204859103389273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6017679672273145471185697 4513259754204859103389273)
    ·
      refine ⟨3384944815653644327541955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4513259754204859103389273 3384944815653644327541955)
      ·
        refine ⟨5077417223480466491312933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3384944815653644327541955 5077417223480466491312933)
        ·
          refine ⟨952015729402587467121175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5077417223480466491312933 952015729402587467121175)
          ·
            refine ⟨1428023594103881200681763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952015729402587467121175 1428023594103881200681763)
            ·
              refine ⟨2142035391155821801022645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428023594103881200681763 2142035391155821801022645)
              ·
                refine ⟨200815817920858293845873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2142035391155821801022645 200815817920858293845873)
                ·
                  refine ⟨150611863440643720384405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200815817920858293845873 150611863440643720384405)
                  ·
                    rfl

theorem cell20_329980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_329980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329980 prefixEnd_329980 := by exact prefixLift 329980
  have htrace : WordTrace (prefixWord ++ tailWord_329980) baseStart_329980 baseEnd_329980 := by
    simpa [prefixWord, tailWord_329980, baseEnd_329980] using wordTrace_append hprefix tailTrace_329980
  have hstable : (prefixWord ++ tailWord_329980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329980).length < 2 ^ (prefixWord ++ tailWord_329980).sum := by decide
  have hdescent : baseEnd_329980 < baseStart_329980 := by decide
  rcases family_descends (prefixWord ++ tailWord_329980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329994 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_329994 : Nat := 118140960795 + 329994 * 2 ^ 59
def prefixEnd_329994 : Nat := 4983230072969 + 3 ^ 40 * 329994 * 2
def baseEnd_329994 : Nat := 150618253422121893917681

theorem tailTrace_329994 : CollatzResearch.WordTrace tailWord_329994 prefixEnd_329994 150618253422121893917681 := by
  unfold tailWord_329994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008967491623892833345259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8023913310997047555587357 3008967491623892833345259)
  ·
    refine ⟨4513451237435839250017889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3008967491623892833345259 4513451237435839250017889)
    ·
      refine ⟨3385088428076879437513417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4513451237435839250017889 3385088428076879437513417)
      ·
        refine ⟨2538816321057659578135063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3385088428076879437513417 2538816321057659578135063)
        ·
          refine ⟨3808224481586489367202595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538816321057659578135063 3808224481586489367202595)
          ·
            refine ⟨5712336722379734050803893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808224481586489367202595 5712336722379734050803893)
            ·
              refine ⟨535531567723100067262865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5712336722379734050803893 535531567723100067262865)
              ·
                refine ⟨401648675792325050447149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535531567723100067262865 401648675792325050447149)
                ·
                  refine ⟨150618253422121893917681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401648675792325050447149 150618253422121893917681)
                  ·
                    rfl

theorem cell20_329994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_329994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_329994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_329994 prefixEnd_329994 := by exact prefixLift 329994
  have htrace : WordTrace (prefixWord ++ tailWord_329994) baseStart_329994 baseEnd_329994 := by
    simpa [prefixWord, tailWord_329994, baseEnd_329994] using wordTrace_append hprefix tailTrace_329994
  have hstable : (prefixWord ++ tailWord_329994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329994).length < 2 ^ (prefixWord ++ tailWord_329994).sum := by decide
  have hdescent : baseEnd_329994 < baseStart_329994 := by decide
  rcases family_descends (prefixWord ++ tailWord_329994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330001 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_330001 : Nat := 118140960795 + 330001 * 2 ^ 59
def prefixEnd_330001 : Nat := 4983230072969 + 3 ^ 40 * 330001 * 2
def baseEnd_330001 : Nat := 150621448412860980684319

theorem tailTrace_330001 : CollatzResearch.WordTrace tailWord_330001 prefixEnd_330001 150621448412860980684319 := by
  unfold tailWord_330001
  simp only [CollatzResearch.WordTrace]
  refine ⟨12036125277470211528885857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8024083518313474352590571 12036125277470211528885857)
  ·
    refine ⟨9027093958102658646664393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12036125277470211528885857 9027093958102658646664393)
    ·
      refine ⟨6770320468576993984998295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9027093958102658646664393 6770320468576993984998295)
      ·
        refine ⟨10155480702865490977497443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6770320468576993984998295 10155480702865490977497443)
        ·
          refine ⟨15233221054298236466246165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10155480702865490977497443 15233221054298236466246165)
          ·
            refine ⟨714057236920229834355289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15233221054298236466246165 714057236920229834355289)
            ·
              refine ⟨535542927690172375766467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714057236920229834355289 535542927690172375766467)
              ·
                refine ⟨803314391535258563649701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535542927690172375766467 803314391535258563649701)
                ·
                  refine ⟨150621448412860980684319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803314391535258563649701 150621448412860980684319)
                  ·
                    rfl

theorem cell20_330001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_330001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330001 prefixEnd_330001 := by exact prefixLift 330001
  have htrace : WordTrace (prefixWord ++ tailWord_330001) baseStart_330001 baseEnd_330001 := by
    simpa [prefixWord, tailWord_330001, baseEnd_330001] using wordTrace_append hprefix tailTrace_330001
  have hstable : (prefixWord ++ tailWord_330001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330001).length < 2 ^ (prefixWord ++ tailWord_330001).sum := by decide
  have hdescent : baseEnd_330001 < baseStart_330001 := by decide
  rcases family_descends (prefixWord ++ tailWord_330001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330046 : List Nat := [4, 2, 1, 2, 1, 2, 8]
def baseStart_330046 : Nat := 118140960795 + 330046 * 2 ^ 59
def prefixEnd_330046 : Nat := 4983230072969 + 3 ^ 40 * 330046 * 2
def baseEnd_330046 : Nat := 16737998626560091576015

theorem tailTrace_330046 : CollatzResearch.WordTrace tailWord_330046 prefixEnd_330046 16737998626560091576015 := by
  unfold tailWord_330046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504720820288398026784249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8025177708204789476182661 1504720820288398026784249)
  ·
    refine ⟨1128540615216298520088187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1504720820288398026784249 1128540615216298520088187)
    ·
      refine ⟨1692810922824447780132281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128540615216298520088187 1692810922824447780132281)
      ·
        refine ⟨1269608192118335835099211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1692810922824447780132281 1269608192118335835099211)
        ·
          refine ⟨1904412288177503752648817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269608192118335835099211 1904412288177503752648817)
          ·
            refine ⟨1428309216133127814486613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1904412288177503752648817 1428309216133127814486613)
            ·
              refine ⟨16737998626560091576015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1428309216133127814486613 16737998626560091576015)
              ·
                rfl

theorem cell20_330046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 8].length) (baseStart_330046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330046 prefixEnd_330046 := by exact prefixLift 330046
  have htrace : WordTrace (prefixWord ++ tailWord_330046) baseStart_330046 baseEnd_330046 := by
    simpa [prefixWord, tailWord_330046, baseEnd_330046] using wordTrace_append hprefix tailTrace_330046
  have hstable : (prefixWord ++ tailWord_330046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330046).length < 2 ^ (prefixWord ++ tailWord_330046).sum := by decide
  have hdescent : baseEnd_330046 < baseStart_330046 := by decide
  rcases family_descends (prefixWord ++ tailWord_330046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330052 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 4]
def baseStart_330052 : Nat := 118140960795 + 330052 * 2 ^ 59
def prefixEnd_330052 : Nat := 4983230072969 + 3 ^ 40 * 330052 * 2
def baseEnd_330052 : Nat := 150644726202531469984111

theorem tailTrace_330052 : CollatzResearch.WordTrace tailWord_330052 prefixEnd_330052 150644726202531469984111 := by
  unfold tailWord_330052
  simp only [CollatzResearch.WordTrace]
  refine ⟨6018992700142723619496205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8025323600190298159328273 6018992700142723619496205)
  ·
    refine ⟨2257122262553521357311077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6018992700142723619496205 2257122262553521357311077)
    ·
      refine ⟨423210424228785254495827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2257122262553521357311077 423210424228785254495827)
      ·
        refine ⟨634815636343177881743741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423210424228785254495827 634815636343177881743741)
        ·
          refine ⟨238055863628691705653903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 634815636343177881743741 238055863628691705653903)
          ·
            refine ⟨357083795443037558480855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238055863628691705653903 357083795443037558480855)
            ·
              refine ⟨535625693164556337721283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357083795443037558480855 535625693164556337721283)
              ·
                refine ⟨803438539746834506581925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535625693164556337721283 803438539746834506581925)
                ·
                  refine ⟨150644726202531469984111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803438539746834506581925 150644726202531469984111)
                  ·
                    rfl

theorem cell20_330052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_330052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330052 prefixEnd_330052 := by exact prefixLift 330052
  have htrace : WordTrace (prefixWord ++ tailWord_330052) baseStart_330052 baseEnd_330052 := by
    simpa [prefixWord, tailWord_330052, baseEnd_330052] using wordTrace_append hprefix tailTrace_330052
  have hstable : (prefixWord ++ tailWord_330052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330052).length < 2 ^ (prefixWord ++ tailWord_330052).sum := by decide
  have hdescent : baseEnd_330052 < baseStart_330052 := by decide
  rcases family_descends (prefixWord ++ tailWord_330052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330132 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_330132 : Nat := 118140960795 + 330132 * 2 ^ 59
def prefixEnd_330132 : Nat := 4983230072969 + 3 ^ 40 * 330132 * 2
def baseEnd_330132 : Nat := 150681240382406747317117

theorem tailTrace_330132 : CollatzResearch.WordTrace tailWord_330132 prefixEnd_330132 150681240382406747317117 := by
  unfold tailWord_330132
  simp only [CollatzResearch.WordTrace]
  refine ⟨6020451619997810450952325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8027268826663747267936433 6020451619997810450952325)
  ·
    refine ⟨1128834678749589459553561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6020451619997810450952325 1128834678749589459553561)
    ·
      refine ⟨846626009062192094665171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1128834678749589459553561 846626009062192094665171)
      ·
        refine ⟨1269939013593288141997757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846626009062192094665171 1269939013593288141997757)
        ·
          refine ⟨476227130097483053249159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1269939013593288141997757 476227130097483053249159)
          ·
            refine ⟨714340695146224579873739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476227130097483053249159 714340695146224579873739)
            ·
              refine ⟨1071511042719336869810609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714340695146224579873739 1071511042719336869810609)
              ·
                refine ⟨803633282039502652357957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071511042719336869810609 803633282039502652357957)
                ·
                  refine ⟨150681240382406747317117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 803633282039502652357957 150681240382406747317117)
                  ·
                    rfl

theorem cell20_330132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_330132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330132 prefixEnd_330132 := by exact prefixLift 330132
  have htrace : WordTrace (prefixWord ++ tailWord_330132) baseStart_330132 baseEnd_330132 := by
    simpa [prefixWord, tailWord_330132, baseEnd_330132] using wordTrace_append hprefix tailTrace_330132
  have hstable : (prefixWord ++ tailWord_330132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330132).length < 2 ^ (prefixWord ++ tailWord_330132).sum := by decide
  have hdescent : baseEnd_330132 < baseStart_330132 := by decide
  rcases family_descends (prefixWord ++ tailWord_330132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330167 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_330167 : Nat := 118140960795 + 330167 * 2 ^ 59
def prefixEnd_330167 : Nat := 4983230072969 + 3 ^ 40 * 330167 * 2
def baseEnd_330167 : Nat := 150697215336102181150307

theorem tailTrace_330167 : CollatzResearch.WordTrace tailWord_330167 prefixEnd_330167 150697215336102181150307 := by
  unfold tailWord_330167
  simp only [CollatzResearch.WordTrace]
  refine ⟨12042179794868821879428755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8028119863245881252952503 12042179794868821879428755)
  ·
    refine ⟨18063269692303232819143133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12042179794868821879428755 18063269692303232819143133)
    ·
      refine ⟨6773726134613712307178675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18063269692303232819143133 6773726134613712307178675)
      ·
        refine ⟨10160589201920568460768013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6773726134613712307178675 10160589201920568460768013)
        ·
          refine ⟨3810220950720213172788005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10160589201920568460768013 3810220950720213172788005)
          ·
            refine ⟨714416428260039969897751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3810220950720213172788005 714416428260039969897751)
            ·
              refine ⟨1071624642390059954846627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714416428260039969897751 1071624642390059954846627)
              ·
                refine ⟨1607436963585089932269941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071624642390059954846627 1607436963585089932269941)
                ·
                  refine ⟨150697215336102181150307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1607436963585089932269941 150697215336102181150307)
                  ·
                    rfl

theorem cell20_330167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_330167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330167 prefixEnd_330167 := by exact prefixLift 330167
  have htrace : WordTrace (prefixWord ++ tailWord_330167) baseStart_330167 baseEnd_330167 := by
    simpa [prefixWord, tailWord_330167, baseEnd_330167] using wordTrace_append hprefix tailTrace_330167
  have hstable : (prefixWord ++ tailWord_330167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330167).length < 2 ^ (prefixWord ++ tailWord_330167).sum := by decide
  have hdescent : baseEnd_330167 < baseStart_330167 := by decide
  rcases family_descends (prefixWord ++ tailWord_330167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330180 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 3]
def baseStart_330180 : Nat := 118140960795 + 330180 * 2 ^ 59
def prefixEnd_330180 : Nat := 4983230072969 + 3 ^ 40 * 330180 * 2
def baseEnd_330180 : Nat := 150703148890331913716921

theorem tailTrace_330180 : CollatzResearch.WordTrace tailWord_330180 prefixEnd_330180 150703148890331913716921 := by
  unfold tailWord_330180
  simp only [CollatzResearch.WordTrace]
  refine ⟨6021326971910862549825997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8028435962547816733101329 6021326971910862549825997)
  ·
    refine ⟨2257997614466573456184749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6021326971910862549825997 2257997614466573456184749)
    ·
      refine ⟨846749105424965046069281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2257997614466573456184749 846749105424965046069281)
      ·
        refine ⟨635061829068723784551961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 846749105424965046069281 635061829068723784551961)
        ·
          refine ⟨476296371801542838413971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 635061829068723784551961 476296371801542838413971)
          ·
            refine ⟨714444557702314257620957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476296371801542838413971 714444557702314257620957)
            ·
              refine ⟨267916709138367846607859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 714444557702314257620957 267916709138367846607859)
              ·
                refine ⟨401875063707551769911789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267916709138367846607859 401875063707551769911789)
                ·
                  refine ⟨150703148890331913716921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401875063707551769911789 150703148890331913716921)
                  ·
                    rfl

theorem cell20_330180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_330180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330180 prefixEnd_330180 := by exact prefixLift 330180
  have htrace : WordTrace (prefixWord ++ tailWord_330180) baseStart_330180 baseEnd_330180 := by
    simpa [prefixWord, tailWord_330180, baseEnd_330180] using wordTrace_append hprefix tailTrace_330180
  have hstable : (prefixWord ++ tailWord_330180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330180).length < 2 ^ (prefixWord ++ tailWord_330180).sum := by decide
  have hdescent : baseEnd_330180 < baseStart_330180 := by decide
  rcases family_descends (prefixWord ++ tailWord_330180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330205 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_330205 : Nat := 118140960795 + 330205 * 2 ^ 59
def prefixEnd_330205 : Nat := 4983230072969 + 3 ^ 40 * 330205 * 2
def baseEnd_330205 : Nat := 150714559571542937883485

theorem tailTrace_330205 : CollatzResearch.WordTrace tailWord_330205 prefixEnd_330205 150714559571542937883485 := by
  unfold tailWord_330205
  simp only [CollatzResearch.WordTrace]
  refine ⟨12043565768731154369312069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8029043845820769579541379 12043565768731154369312069)
  ·
    refine ⟨2258168581637091444246013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12043565768731154369312069 2258168581637091444246013)
    ·
      refine ⟨846813218113909291592255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2258168581637091444246013 846813218113909291592255)
      ·
        refine ⟨1270219827170863937388383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846813218113909291592255 1270219827170863937388383)
        ·
          refine ⟨1905329740756295906082575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270219827170863937388383 1905329740756295906082575)
          ·
            refine ⟨2857994611134443859123863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905329740756295906082575 2857994611134443859123863)
            ·
              refine ⟨4286991916701665788685795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857994611134443859123863 4286991916701665788685795)
              ·
                refine ⟨6430487875052498683028693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286991916701665788685795 6430487875052498683028693)
                ·
                  refine ⟨150714559571542937883485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6430487875052498683028693 150714559571542937883485)
                  ·
                    rfl

theorem cell20_330205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_330205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330205 prefixEnd_330205 := by exact prefixLift 330205
  have htrace : WordTrace (prefixWord ++ tailWord_330205) baseStart_330205 baseEnd_330205 := by
    simpa [prefixWord, tailWord_330205, baseEnd_330205] using wordTrace_append hprefix tailTrace_330205
  have hstable : (prefixWord ++ tailWord_330205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330205).length < 2 ^ (prefixWord ++ tailWord_330205).sum := by decide
  have hdescent : baseEnd_330205 < baseStart_330205 := by decide
  rcases family_descends (prefixWord ++ tailWord_330205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330243 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 3]
def baseStart_330243 : Nat := 118140960795 + 330243 * 2 ^ 59
def prefixEnd_330243 : Nat := 4983230072969 + 3 ^ 40 * 330243 * 2
def baseEnd_330243 : Nat := 150731903806983694616663

theorem tailTrace_330243 : CollatzResearch.WordTrace tailWord_330243 prefixEnd_330243 150731903806983694616663 := by
  unfold tailWord_330243
  simp only [CollatzResearch.WordTrace]
  refine ⟨12044951742593486859195383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8029967828395657906130255 12044951742593486859195383)
  ·
    refine ⟨18067427613890230288793075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12044951742593486859195383 18067427613890230288793075)
    ·
      refine ⟨27101141420835345433189613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18067427613890230288793075 27101141420835345433189613)
      ·
        refine ⟨10162928032813254537446105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27101141420835345433189613 10162928032813254537446105)
        ·
          refine ⟨7622196024609940903084579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10162928032813254537446105 7622196024609940903084579)
          ·
            refine ⟨11433294036914911354626869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7622196024609940903084579 11433294036914911354626869)
            ·
              refine ⟨1071871315960772939496269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11433294036914911354626869 1071871315960772939496269)
              ·
                refine ⟨401951743485289852311101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1071871315960772939496269 401951743485289852311101)
                ·
                  refine ⟨150731903806983694616663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 401951743485289852311101 150731903806983694616663)
                  ·
                    rfl

theorem cell20_330243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_330243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330243 prefixEnd_330243 := by exact prefixLift 330243
  have htrace : WordTrace (prefixWord ++ tailWord_330243) baseStart_330243 baseEnd_330243 := by
    simpa [prefixWord, tailWord_330243, baseEnd_330243] using wordTrace_append hprefix tailTrace_330243
  have hstable : (prefixWord ++ tailWord_330243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330243).length < 2 ^ (prefixWord ++ tailWord_330243).sum := by decide
  have hdescent : baseEnd_330243 < baseStart_330243 := by decide
  rcases family_descends (prefixWord ++ tailWord_330243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330250 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_330250 : Nat := 118140960795 + 330250 * 2 ^ 59
def prefixEnd_330250 : Nat := 4983230072969 + 3 ^ 40 * 330250 * 2
def baseEnd_330250 : Nat := 150735098797722781383301

theorem tailTrace_330250 : CollatzResearch.WordTrace tailWord_330250 prefixEnd_330250 150735098797722781383301 := by
  unfold tailWord_330250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011301763392031763675051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8030138035712084703133469 3011301763392031763675051)
  ·
    refine ⟨4516952645088047645512577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3011301763392031763675051 4516952645088047645512577)
    ·
      refine ⟨3387714483816035734134433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4516952645088047645512577 3387714483816035734134433)
      ·
        refine ⟨2540785862862026800600825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3387714483816035734134433 2540785862862026800600825)
        ·
          refine ⟨1905589397146520100450619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2540785862862026800600825 1905589397146520100450619)
          ·
            refine ⟨2858384095719780150675929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905589397146520100450619 2858384095719780150675929)
            ·
              refine ⟨2143788071789835113006947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2858384095719780150675929 2143788071789835113006947)
              ·
                refine ⟨3215682107684752669510421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143788071789835113006947 3215682107684752669510421)
                ·
                  refine ⟨150735098797722781383301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3215682107684752669510421 150735098797722781383301)
                  ·
                    rfl

theorem cell20_330250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_330250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330250 prefixEnd_330250 := by exact prefixLift 330250
  have htrace : WordTrace (prefixWord ++ tailWord_330250) baseStart_330250 baseEnd_330250 := by
    simpa [prefixWord, tailWord_330250, baseEnd_330250] using wordTrace_append hprefix tailTrace_330250
  have hstable : (prefixWord ++ tailWord_330250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330250).length < 2 ^ (prefixWord ++ tailWord_330250).sum := by decide
  have hdescent : baseEnd_330250 < baseStart_330250 := by decide
  rcases family_descends (prefixWord ++ tailWord_330250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330280 : List Nat := [2, 1, 5, 2, 1, 3, 2, 2, 2]
def baseStart_330280 : Nat := 118140960795 + 330280 * 2 ^ 59
def prefixEnd_330280 : Nat := 4983230072969 + 3 ^ 40 * 330280 * 2
def baseEnd_330280 : Nat := 150748791615176010383179

theorem tailTrace_330280 : CollatzResearch.WordTrace tailWord_330280 prefixEnd_330280 150748791615176010383179 := by
  unfold tailWord_330280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6023150621729721089146147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8030867495639628118861529 6023150621729721089146147)
  ·
    refine ⟨9034725932594581633719221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6023150621729721089146147 9034725932594581633719221)
    ·
      refine ⟨847005556180742028161177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9034725932594581633719221 847005556180742028161177)
      ·
        refine ⟨635254167135556521120883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 847005556180742028161177 635254167135556521120883)
        ·
          refine ⟨952881250703334781681325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635254167135556521120883 952881250703334781681325)
          ·
            refine ⟨357330469013750543130497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 952881250703334781681325 357330469013750543130497)
            ·
              refine ⟨267997851760312907347873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357330469013750543130497 267997851760312907347873)
              ·
                refine ⟨200998388820234680510905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267997851760312907347873 200998388820234680510905)
                ·
                  refine ⟨150748791615176010383179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200998388820234680510905 150748791615176010383179)
                  ·
                    rfl

theorem cell20_330280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_330280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330280 prefixEnd_330280 := by exact prefixLift 330280
  have htrace : WordTrace (prefixWord ++ tailWord_330280) baseStart_330280 baseEnd_330280 := by
    simpa [prefixWord, tailWord_330280, baseEnd_330280] using wordTrace_append hprefix tailTrace_330280
  have hstable : (prefixWord ++ tailWord_330280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330280).length < 2 ^ (prefixWord ++ tailWord_330280).sum := by decide
  have hdescent : baseEnd_330280 < baseStart_330280 := by decide
  rcases family_descends (prefixWord ++ tailWord_330280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330305 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_330305 : Nat := 118140960795 + 330305 * 2 ^ 59
def prefixEnd_330305 : Nat := 4983230072969 + 3 ^ 40 * 330305 * 2
def baseEnd_330305 : Nat := 150760202296387034549743

theorem tailTrace_330305 : CollatzResearch.WordTrace tailWord_330305 prefixEnd_330305 150760202296387034549743 := by
  unfold tailWord_330305
  simp only [CollatzResearch.WordTrace]
  refine ⟨12047213068368871447952369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8031475378912580965301579 12047213068368871447952369)
  ·
    refine ⟨9035409801276653585964277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12047213068368871447952369 9035409801276653585964277)
    ·
      refine ⟨847069668869686273684151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9035409801276653585964277 847069668869686273684151)
      ·
        refine ⟨1270604503304529410526227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847069668869686273684151 1270604503304529410526227)
        ·
          refine ⟨1905906754956794115789341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270604503304529410526227 1905906754956794115789341)
          ·
            refine ⟨714715033108797793421003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1905906754956794115789341 714715033108797793421003)
            ·
              refine ⟨1072072549663196690131505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714715033108797793421003 1072072549663196690131505)
              ·
                refine ⟨804054412247397517598629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072072549663196690131505 804054412247397517598629)
                ·
                  refine ⟨150760202296387034549743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 804054412247397517598629 150760202296387034549743)
                  ·
                    rfl

theorem cell20_330305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_330305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330305 prefixEnd_330305 := by exact prefixLift 330305
  have htrace : WordTrace (prefixWord ++ tailWord_330305) baseStart_330305 baseEnd_330305 := by
    simpa [prefixWord, tailWord_330305, baseEnd_330305] using wordTrace_append hprefix tailTrace_330305
  have hstable : (prefixWord ++ tailWord_330305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330305).length < 2 ^ (prefixWord ++ tailWord_330305).sum := by decide
  have hdescent : baseEnd_330305 < baseStart_330305 := by decide
  rcases family_descends (prefixWord ++ tailWord_330305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330322 : List Nat := [3, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_330322 : Nat := 118140960795 + 330322 * 2 ^ 59
def prefixEnd_330322 : Nat := 4983230072969 + 3 ^ 40 * 330322 * 2
def baseEnd_330322 : Nat := 150767961559610530983007

theorem tailTrace_330322 : CollatzResearch.WordTrace tailWord_330322 prefixEnd_330322 150767961559610530983007 := by
  unfold tailWord_330322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011958277326820837830305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8031888739538188900880813 3011958277326820837830305)
  ·
    refine ⟨2258968707995115628372729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3011958277326820837830305 2258968707995115628372729)
    ·
      refine ⟨1694226530996336721279547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2258968707995115628372729 1694226530996336721279547)
      ·
        refine ⟨2541339796494505081919321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1694226530996336721279547 2541339796494505081919321)
        ·
          refine ⟨1906004847370878811439491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2541339796494505081919321 1906004847370878811439491)
          ·
            refine ⟨2859007271056318217159237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906004847370878811439491 2859007271056318217159237)
            ·
              refine ⟨536063863323059665717357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2859007271056318217159237 536063863323059665717357)
              ·
                refine ⟨201023948746147374644009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 536063863323059665717357 201023948746147374644009)
                ·
                  refine ⟨150767961559610530983007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201023948746147374644009 150767961559610530983007)
                  ·
                    rfl

theorem cell20_330322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_330322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330322 prefixEnd_330322 := by exact prefixLift 330322
  have htrace : WordTrace (prefixWord ++ tailWord_330322) baseStart_330322 baseEnd_330322 := by
    simpa [prefixWord, tailWord_330322, baseEnd_330322] using wordTrace_append hprefix tailTrace_330322
  have hstable : (prefixWord ++ tailWord_330322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330322).length < 2 ^ (prefixWord ++ tailWord_330322).sum := by decide
  have hdescent : baseEnd_330322 < baseStart_330322 := by decide
  rcases family_descends (prefixWord ++ tailWord_330322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330332 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 3]
def baseStart_330332 : Nat := 118140960795 + 330332 * 2 ^ 59
def prefixEnd_330332 : Nat := 4983230072969 + 3 ^ 40 * 330332 * 2
def baseEnd_330332 : Nat := 150772525832094940649633

theorem tailTrace_330332 : CollatzResearch.WordTrace tailWord_330332 prefixEnd_330332 150772525832094940649633 := by
  unfold tailWord_330332
  simp only [CollatzResearch.WordTrace]
  refine ⟨6024098919635527529592625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8032131892847370039456833 6024098919635527529592625)
  ·
    refine ⟨4518074189726645647194469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6024098919635527529592625 4518074189726645647194469)
    ·
      refine ⟨847138910573746058848963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4518074189726645647194469 847138910573746058848963)
      ·
        refine ⟨1270708365860619088273445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847138910573746058848963 1270708365860619088273445)
        ·
          refine ⟨238257818598866079051271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1270708365860619088273445 238257818598866079051271)
          ·
            refine ⟨357386727898299118576907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238257818598866079051271 357386727898299118576907)
            ·
              refine ⟨536080091847448677865361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357386727898299118576907 536080091847448677865361)
              ·
                refine ⟨402060068885586508399021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536080091847448677865361 402060068885586508399021)
                ·
                  refine ⟨150772525832094940649633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402060068885586508399021 150772525832094940649633)
                  ·
                    rfl

theorem cell20_330332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_330332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330332 prefixEnd_330332 := by exact prefixLift 330332
  have htrace : WordTrace (prefixWord ++ tailWord_330332) baseStart_330332 baseEnd_330332 := by
    simpa [prefixWord, tailWord_330332, baseEnd_330332] using wordTrace_append hprefix tailTrace_330332
  have hstable : (prefixWord ++ tailWord_330332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330332).length < 2 ^ (prefixWord ++ tailWord_330332).sum := by decide
  have hdescent : baseEnd_330332 < baseStart_330332 := by decide
  rcases family_descends (prefixWord ++ tailWord_330332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330364 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_330364 : Nat := 118140960795 + 330364 * 2 ^ 59
def prefixEnd_330364 : Nat := 4983230072969 + 3 ^ 40 * 330364 * 2
def baseEnd_330364 : Nat := 150787131504045051582835

theorem tailTrace_330364 : CollatzResearch.WordTrace tailWord_330364 prefixEnd_330364 150787131504045051582835 := by
  unfold tailWord_330364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6024682487577562262175073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8032909983436749682900097 6024682487577562262175073)
  ·
    refine ⟨4518511865683171696631305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6024682487577562262175073 4518511865683171696631305)
    ·
      refine ⟨3388883899262378772473479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4518511865683171696631305 3388883899262378772473479)
      ·
        refine ⟨5083325848893568158710219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3388883899262378772473479 5083325848893568158710219)
        ·
          refine ⟨7624988773340352238065329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083325848893568158710219 7624988773340352238065329)
          ·
            refine ⟨5718741580005264178548997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7624988773340352238065329 5718741580005264178548997)
            ·
              refine ⟨1072264046250987033477937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5718741580005264178548997 1072264046250987033477937)
              ·
                refine ⟨804198034688240275108453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072264046250987033477937 804198034688240275108453)
                ·
                  refine ⟨150787131504045051582835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 804198034688240275108453 150787131504045051582835)
                  ·
                    rfl

theorem cell20_330364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_330364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330364 prefixEnd_330364 := by exact prefixLift 330364
  have htrace : WordTrace (prefixWord ++ tailWord_330364) baseStart_330364 baseEnd_330364 := by
    simpa [prefixWord, tailWord_330364, baseEnd_330364] using wordTrace_append hprefix tailTrace_330364
  have hstable : (prefixWord ++ tailWord_330364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330364).length < 2 ^ (prefixWord ++ tailWord_330364).sum := by decide
  have hdescent : baseEnd_330364 < baseStart_330364 := by decide
  rcases family_descends (prefixWord ++ tailWord_330364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330388 : List Nat := [2, 4, 2, 2, 1, 1, 8]
def baseStart_330388 : Nat := 118140960795 + 330388 * 2 ^ 59
def prefixEnd_330388 : Nat := 4983230072969 + 3 ^ 40 * 330388 * 2
def baseEnd_330388 : Nat := 16755342862000848309193

theorem tailTrace_330388 : CollatzResearch.WordTrace tailWord_330388 prefixEnd_330388 16755342862000848309193 := by
  unfold tailWord_330388
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025120163534088311611909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8033493551378784415482545 6025120163534088311611909)
  ·
    refine ⟨1129710030662641558427233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6025120163534088311611909 1129710030662641558427233)
    ·
      refine ⟨847282522996981168820425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1129710030662641558427233 847282522996981168820425)
      ·
        refine ⟨635461892247735876615319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 847282522996981168820425 635461892247735876615319)
        ·
          refine ⟨953192838371603814922979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635461892247735876615319 953192838371603814922979)
          ·
            refine ⟨1429789257557405722384469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953192838371603814922979 1429789257557405722384469)
            ·
              refine ⟨16755342862000848309193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1429789257557405722384469 16755342862000848309193)
              ·
                rfl

theorem cell20_330388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 8].length) (baseStart_330388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330388 prefixEnd_330388 := by exact prefixLift 330388
  have htrace : WordTrace (prefixWord ++ tailWord_330388) baseStart_330388 baseEnd_330388 := by
    simpa [prefixWord, tailWord_330388, baseEnd_330388] using wordTrace_append hprefix tailTrace_330388
  have hstable : (prefixWord ++ tailWord_330388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330388).length < 2 ^ (prefixWord ++ tailWord_330388).sum := by decide
  have hdescent : baseEnd_330388 < baseStart_330388 := by decide
  rcases family_descends (prefixWord ++ tailWord_330388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330394 : List Nat := [3, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_330394 : Nat := 118140960795 + 330394 * 2 ^ 59
def prefixEnd_330394 : Nat := 4983230072969 + 3 ^ 40 * 330394 * 2
def baseEnd_330394 : Nat := 150800824321498280582713

theorem tailTrace_330394 : CollatzResearch.WordTrace tailWord_330394 prefixEnd_330394 150800824321498280582713 := by
  unfold tailWord_330394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3012614791261609911985559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8033639443364293098628157 3012614791261609911985559)
  ·
    refine ⟨4518922186892414867978339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3012614791261609911985559 4518922186892414867978339)
    ·
      refine ⟨6778383280338622301967509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4518922186892414867978339 6778383280338622301967509)
      ·
        refine ⟨317736716265872920404727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6778383280338622301967509 317736716265872920404727)
        ·
          refine ⟨476605074398809380607091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317736716265872920404727 476605074398809380607091)
          ·
            refine ⟨714907611598214070910637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476605074398809380607091 714907611598214070910637)
            ·
              refine ⟨268090354349330276591489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 714907611598214070910637 268090354349330276591489)
              ·
                refine ⟨201067765761997707443617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268090354349330276591489 201067765761997707443617)
                ·
                  refine ⟨150800824321498280582713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201067765761997707443617 150800824321498280582713)
                  ·
                    rfl

theorem cell20_330394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_330394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330394 prefixEnd_330394 := by exact prefixLift 330394
  have htrace : WordTrace (prefixWord ++ tailWord_330394) baseStart_330394 baseEnd_330394 := by
    simpa [prefixWord, tailWord_330394, baseEnd_330394] using wordTrace_append hprefix tailTrace_330394
  have hstable : (prefixWord ++ tailWord_330394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330394).length < 2 ^ (prefixWord ++ tailWord_330394).sum := by decide
  have hdescent : baseEnd_330394 < baseStart_330394 := by decide
  rcases family_descends (prefixWord ++ tailWord_330394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330453 : List Nat := [1, 3, 2, 5, 1, 1, 1, 4, 2]
def baseStart_330453 : Nat := 118140960795 + 330453 * 2 ^ 59
def prefixEnd_330453 : Nat := 4983230072969 + 3 ^ 40 * 330453 * 2
def baseEnd_330453 : Nat := 150827753529156297615805

theorem tailTrace_330453 : CollatzResearch.WordTrace tailWord_330453 prefixEnd_330453 150827753529156297615805 := by
  unfold tailWord_330453
  simp only [CollatzResearch.WordTrace]
  refine ⟨12052611071832692724340013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8035074047888461816226675 12052611071832692724340013)
  ·
    refine ⟨4519729151937259771627505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12052611071832692724340013 4519729151937259771627505)
    ·
      refine ⟨3389796863952944828720629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4519729151937259771627505 3389796863952944828720629)
      ·
        refine ⟨317793455995588577692559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3389796863952944828720629 317793455995588577692559)
        ·
          refine ⟨476690183993382866538839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317793455995588577692559 476690183993382866538839)
          ·
            refine ⟨715035275990074299808259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476690183993382866538839 715035275990074299808259)
            ·
              refine ⟨1072552913985111449712389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715035275990074299808259 1072552913985111449712389)
              ·
                refine ⟨201103671372208396821073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1072552913985111449712389 201103671372208396821073)
                ·
                  refine ⟨150827753529156297615805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201103671372208396821073 150827753529156297615805)
                  ·
                    rfl

theorem cell20_330453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_330453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330453 prefixEnd_330453 := by exact prefixLift 330453
  have htrace : WordTrace (prefixWord ++ tailWord_330453) baseStart_330453 baseEnd_330453 := by
    simpa [prefixWord, tailWord_330453, baseEnd_330453] using wordTrace_append hprefix tailTrace_330453
  have hstable : (prefixWord ++ tailWord_330453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330453).length < 2 ^ (prefixWord ++ tailWord_330453).sum := by decide
  have hdescent : baseEnd_330453 < baseStart_330453 := by decide
  rcases family_descends (prefixWord ++ tailWord_330453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330457 : List Nat := [1, 2, 1, 2, 3, 2, 3, 4, 2]
def baseStart_330457 : Nat := 118140960795 + 330457 * 2 ^ 59
def prefixEnd_330457 : Nat := 4983230072969 + 3 ^ 40 * 330457 * 2
def baseEnd_330457 : Nat := 150829579238150061482455

theorem tailTrace_330457 : CollatzResearch.WordTrace tailWord_330457 prefixEnd_330457 150829579238150061482455 := by
  unfold tailWord_330457
  simp only [CollatzResearch.WordTrace]
  refine ⟨12052756963818201407485625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8035171309212134271657083 12052756963818201407485625)
  ·
    refine ⟨9039567722863651055614219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12052756963818201407485625 9039567722863651055614219)
    ·
      refine ⟨13559351584295476583421329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9039567722863651055614219 13559351584295476583421329)
      ·
        refine ⟨10169513688221607437565997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13559351584295476583421329 10169513688221607437565997)
        ·
          refine ⟨3813567633083102789087249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10169513688221607437565997 3813567633083102789087249)
          ·
            refine ⟨2860175724812327091815437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813567633083102789087249 2860175724812327091815437)
            ·
              refine ⟨1072565896804622659430789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2860175724812327091815437 1072565896804622659430789)
              ·
                refine ⟨201106105650866748643273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1072565896804622659430789 201106105650866748643273)
                ·
                  refine ⟨150829579238150061482455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201106105650866748643273 150829579238150061482455)
                  ·
                    rfl

theorem cell20_330457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_330457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330457 prefixEnd_330457 := by exact prefixLift 330457
  have htrace : WordTrace (prefixWord ++ tailWord_330457) baseStart_330457 baseEnd_330457 := by
    simpa [prefixWord, tailWord_330457, baseEnd_330457] using wordTrace_append hprefix tailTrace_330457
  have hstable : (prefixWord ++ tailWord_330457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330457).length < 2 ^ (prefixWord ++ tailWord_330457).sum := by decide
  have hdescent : baseEnd_330457 < baseStart_330457 := by decide
  rcases family_descends (prefixWord ++ tailWord_330457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330478 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_330478 : Nat := 118140960795 + 330478 * 2 ^ 59
def prefixEnd_330478 : Nat := 4983230072969 + 3 ^ 40 * 330478 * 2
def baseEnd_330478 : Nat := 150839164210367321782369

theorem tailTrace_330478 : CollatzResearch.WordTrace tailWord_330478 prefixEnd_330478 150839164210367321782369 := by
  unfold tailWord_330478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506690362092765249250011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8035681931161414662666725 1506690362092765249250011)
  ·
    refine ⟨2260035543139147873875017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1506690362092765249250011 2260035543139147873875017)
    ·
      refine ⟨1695026657354360905406263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2260035543139147873875017 1695026657354360905406263)
      ·
        refine ⟨2542539986031541358109395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695026657354360905406263 2542539986031541358109395)
        ·
          refine ⟨3813809979047312037164093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542539986031541358109395 3813809979047312037164093)
          ·
            refine ⟨1430178742142742013936535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3813809979047312037164093 1430178742142742013936535)
            ·
              refine ⟨2145268113214113020904803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430178742142742013936535 2145268113214113020904803)
              ·
                refine ⟨3217902169821169531357205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145268113214113020904803 3217902169821169531357205)
                ·
                  refine ⟨150839164210367321782369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3217902169821169531357205 150839164210367321782369)
                  ·
                    rfl

theorem cell20_330478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_330478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330478 prefixEnd_330478 := by exact prefixLift 330478
  have htrace : WordTrace (prefixWord ++ tailWord_330478) baseStart_330478 baseEnd_330478 := by
    simpa [prefixWord, tailWord_330478, baseEnd_330478] using wordTrace_append hprefix tailTrace_330478
  have hstable : (prefixWord ++ tailWord_330478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330478).length < 2 ^ (prefixWord ++ tailWord_330478).sum := by decide
  have hdescent : baseEnd_330478 < baseStart_330478 := by decide
  rcases family_descends (prefixWord ++ tailWord_330478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330499 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_330499 : Nat := 118140960795 + 330499 * 2 ^ 59
def prefixEnd_330499 : Nat := 4983230072969 + 3 ^ 40 * 330499 * 2
def baseEnd_330499 : Nat := 150848749182584582082283

theorem tailTrace_330499 : CollatzResearch.WordTrace tailWord_330499 prefixEnd_330499 150848749182584582082283 := by
  unfold tailWord_330499
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054288829666042580514551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8036192553110695053676367 12054288829666042580514551)
  ·
    refine ⟨18081433244499063870771827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12054288829666042580514551 18081433244499063870771827)
    ·
      refine ⟨27122149866748595806157741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18081433244499063870771827 27122149866748595806157741)
      ·
        refine ⟨10170806200030723427309153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27122149866748595806157741 10170806200030723427309153)
        ·
          refine ⟨7628104650023042570481865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10170806200030723427309153 7628104650023042570481865)
          ·
            refine ⟨5721078487517281927861399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7628104650023042570481865 5721078487517281927861399)
            ·
              refine ⟨8581617731275922891792099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5721078487517281927861399 8581617731275922891792099)
              ·
                refine ⟨12872426596913884337688149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8581617731275922891792099 12872426596913884337688149)
                ·
                  refine ⟨150848749182584582082283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12872426596913884337688149 150848749182584582082283)
                  ·
                    rfl

theorem cell20_330499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_330499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330499 prefixEnd_330499 := by exact prefixLift 330499
  have htrace : WordTrace (prefixWord ++ tailWord_330499) baseStart_330499 baseEnd_330499 := by
    simpa [prefixWord, tailWord_330499, baseEnd_330499] using wordTrace_append hprefix tailTrace_330499
  have hstable : (prefixWord ++ tailWord_330499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330499).length < 2 ^ (prefixWord ++ tailWord_330499).sum := by decide
  have hdescent : baseEnd_330499 < baseStart_330499 := by decide
  rcases family_descends (prefixWord ++ tailWord_330499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330557 : List Nat := [1, 4, 1, 4, 3, 1, 6]
def baseStart_330557 : Nat := 118140960795 + 330557 * 2 ^ 59
def prefixEnd_330557 : Nat := 4983230072969 + 3 ^ 40 * 330557 * 2
def baseEnd_330557 : Nat := 16763913551443795349857

theorem tailTrace_330557 : CollatzResearch.WordTrace tailWord_330557 prefixEnd_330557 16763913551443795349857 := by
  unfold tailWord_330557
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056404263455918486125925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8037602842303945657417283 12056404263455918486125925)
  ·
    refine ⟨2260575799397984716148611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12056404263455918486125925 2260575799397984716148611)
    ·
      refine ⟨3390863699096977074222917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260575799397984716148611 3390863699096977074222917)
      ·
        refine ⟨635786943580683201416797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3390863699096977074222917 635786943580683201416797)
        ·
          refine ⟨238420103842756200531299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 635786943580683201416797 238420103842756200531299)
          ·
            refine ⟨357630155764134300796949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238420103842756200531299 357630155764134300796949)
            ·
              refine ⟨16763913551443795349857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 357630155764134300796949 16763913551443795349857)
              ·
                rfl

theorem cell20_330557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 6].length) (baseStart_330557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330557 prefixEnd_330557 := by exact prefixLift 330557
  have htrace : WordTrace (prefixWord ++ tailWord_330557) baseStart_330557 baseEnd_330557 := by
    simpa [prefixWord, tailWord_330557, baseEnd_330557] using wordTrace_append hprefix tailTrace_330557
  have hstable : (prefixWord ++ tailWord_330557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330557).length < 2 ^ (prefixWord ++ tailWord_330557).sum := by decide
  have hdescent : baseEnd_330557 < baseStart_330557 := by decide
  rcases family_descends (prefixWord ++ tailWord_330557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330568 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_330568 : Nat := 118140960795 + 330568 * 2 ^ 59
def prefixEnd_330568 : Nat := 4983230072969 + 3 ^ 40 * 330568 * 2
def baseEnd_330568 : Nat := 150880242662727008782001

theorem tailTrace_330568 : CollatzResearch.WordTrace tailWord_330568 prefixEnd_330568 150880242662727008782001 := by
  unfold tailWord_330568
  simp only [CollatzResearch.WordTrace]
  refine ⟨6028402733208033682388179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8037870310944044909850905 6028402733208033682388179)
  ·
    refine ⟨9042604099812050523582269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6028402733208033682388179 9042604099812050523582269)
    ·
      refine ⟨3390976537429518946343351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9042604099812050523582269 3390976537429518946343351)
      ·
        refine ⟨5086464806144278419515027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3390976537429518946343351 5086464806144278419515027)
        ·
          refine ⟨7629697209216417629272541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5086464806144278419515027 7629697209216417629272541)
          ·
            refine ⟨2861136453456156610977203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7629697209216417629272541 2861136453456156610977203)
            ·
              refine ⟨4291704680184234916465805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2861136453456156610977203 4291704680184234916465805)
              ·
                refine ⟨1609389255069088093674677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4291704680184234916465805 1609389255069088093674677)
                ·
                  refine ⟨150880242662727008782001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1609389255069088093674677 150880242662727008782001)
                  ·
                    rfl

theorem cell20_330568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_330568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330568 prefixEnd_330568 := by exact prefixLift 330568
  have htrace : WordTrace (prefixWord ++ tailWord_330568) baseStart_330568 baseEnd_330568 := by
    simpa [prefixWord, tailWord_330568, baseEnd_330568] using wordTrace_append hprefix tailTrace_330568
  have hstable : (prefixWord ++ tailWord_330568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330568).length < 2 ^ (prefixWord ++ tailWord_330568).sum := by decide
  have hdescent : baseEnd_330568 < baseStart_330568 := by decide
  rcases family_descends (prefixWord ++ tailWord_330568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330585 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 3]
def baseStart_330585 : Nat := 118140960795 + 330585 * 2 ^ 59
def prefixEnd_330585 : Nat := 4983230072969 + 3 ^ 40 * 330585 * 2
def baseEnd_330585 : Nat := 150888001925950505215265

theorem tailTrace_330585 : CollatzResearch.WordTrace tailWord_330585 prefixEnd_330585 150888001925950505215265 := by
  unfold tailWord_330585
  simp only [CollatzResearch.WordTrace]
  refine ⟨12057425507354479268145209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8038283671569652845430139 12057425507354479268145209)
  ·
    refine ⟨9043069130515859451108907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12057425507354479268145209 9043069130515859451108907)
    ·
      refine ⟨13564603695773789176663361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9043069130515859451108907 13564603695773789176663361)
      ·
        refine ⟨10173452771830341882497521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13564603695773789176663361 10173452771830341882497521)
        ·
          refine ⟨7630089578872756411873141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10173452771830341882497521 7630089578872756411873141)
          ·
            refine ⟨715320898019320913613107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7630089578872756411873141 715320898019320913613107)
            ·
              refine ⟨1072981347028981370419661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715320898019320913613107 1072981347028981370419661)
              ·
                refine ⟨402368005135868013907373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1072981347028981370419661 402368005135868013907373)
                ·
                  refine ⟨150888001925950505215265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402368005135868013907373 150888001925950505215265)
                  ·
                    rfl

theorem cell20_330585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_330585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330585 prefixEnd_330585 := by exact prefixLift 330585
  have htrace : WordTrace (prefixWord ++ tailWord_330585) baseStart_330585 baseEnd_330585 := by
    simpa [prefixWord, tailWord_330585, baseEnd_330585] using wordTrace_append hprefix tailTrace_330585
  have hstable : (prefixWord ++ tailWord_330585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330585).length < 2 ^ (prefixWord ++ tailWord_330585).sum := by decide
  have hdescent : baseEnd_330585 < baseStart_330585 := by decide
  rcases family_descends (prefixWord ++ tailWord_330585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330599 : List Nat := [1, 1, 5, 1, 2, 2, 2, 6]
def baseStart_330599 : Nat := 118140960795 + 330599 * 2 ^ 59
def prefixEnd_330599 : Nat := 4983230072969 + 3 ^ 40 * 330599 * 2
def baseEnd_330599 : Nat := 50298130635809559582847

theorem tailTrace_330599 : CollatzResearch.WordTrace tailWord_330599 prefixEnd_330599 50298130635809559582847 := by
  unfold tailWord_330599
  simp only [CollatzResearch.WordTrace]
  refine ⟨12057936129303759659154851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8038624086202506439436567 12057936129303759659154851)
  ·
    refine ⟨18086904193955639488732277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12057936129303759659154851 18086904193955639488732277)
    ·
      refine ⟨1695647268183341202068651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18086904193955639488732277 1695647268183341202068651)
      ·
        refine ⟨2543470902275011803102977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695647268183341202068651 2543470902275011803102977)
        ·
          refine ⟨1907603176706258852327233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2543470902275011803102977 1907603176706258852327233)
          ·
            refine ⟨1430702382529694139245425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1907603176706258852327233 1430702382529694139245425)
            ·
              refine ⟨1073026786897270604434069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430702382529694139245425 1073026786897270604434069)
              ·
                refine ⟨50298130635809559582847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1073026786897270604434069 50298130635809559582847)
                ·
                  rfl

theorem cell20_330599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_330599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330599 prefixEnd_330599 := by exact prefixLift 330599
  have htrace : WordTrace (prefixWord ++ tailWord_330599) baseStart_330599 baseEnd_330599 := by
    simpa [prefixWord, tailWord_330599, baseEnd_330599] using wordTrace_append hprefix tailTrace_330599
  have hstable : (prefixWord ++ tailWord_330599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330599).length < 2 ^ (prefixWord ++ tailWord_330599).sum := by decide
  have hdescent : baseEnd_330599 < baseStart_330599 := by decide
  rcases family_descends (prefixWord ++ tailWord_330599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330682 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_330682 : Nat := 118140960795 + 330682 * 2 ^ 59
def prefixEnd_330682 : Nat := 4983230072969 + 3 ^ 40 * 330682 * 2
def baseEnd_330682 : Nat := 150932275369049278981535

theorem tailTrace_330682 : CollatzResearch.WordTrace tailWord_330682 prefixEnd_330682 150932275369049278981535 := by
  unfold tailWord_330682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3015240847000766208606575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8040642258668709889617533 3015240847000766208606575)
  ·
    refine ⟨4522861270501149312909863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3015240847000766208606575 4522861270501149312909863)
    ·
      refine ⟨6784291905751723969364795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4522861270501149312909863 6784291905751723969364795)
      ·
        refine ⟨10176437858627585954047193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6784291905751723969364795 10176437858627585954047193)
        ·
          refine ⟨7632328393970689465535395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10176437858627585954047193 7632328393970689465535395)
          ·
            refine ⟨11448492590956034198303093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7632328393970689465535395 11448492590956034198303093)
            ·
              refine ⟨1073296180402128206090915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11448492590956034198303093 1073296180402128206090915)
              ·
                refine ⟨1609944270603192309136373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073296180402128206090915 1609944270603192309136373)
                ·
                  refine ⟨150932275369049278981535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1609944270603192309136373 150932275369049278981535)
                  ·
                    rfl

theorem cell20_330682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_330682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330682 prefixEnd_330682 := by exact prefixLift 330682
  have htrace : WordTrace (prefixWord ++ tailWord_330682) baseStart_330682 baseEnd_330682 := by
    simpa [prefixWord, tailWord_330682, baseEnd_330682] using wordTrace_append hprefix tailTrace_330682
  have hstable : (prefixWord ++ tailWord_330682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330682).length < 2 ^ (prefixWord ++ tailWord_330682).sum := by decide
  have hdescent : baseEnd_330682 < baseStart_330682 := by decide
  rcases family_descends (prefixWord ++ tailWord_330682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330685 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 4]
def baseStart_330685 : Nat := 118140960795 + 330685 * 2 ^ 59
def prefixEnd_330685 : Nat := 4983230072969 + 3 ^ 40 * 330685 * 2
def baseEnd_330685 : Nat := 150933644650794601881523

theorem tailTrace_330685 : CollatzResearch.WordTrace tailWord_330685 prefixEnd_330685 150933644650794601881523 := by
  unfold tailWord_330685
  simp only [CollatzResearch.WordTrace]
  refine ⟨12061072806992196346785509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8040715204661464231190339 12061072806992196346785509)
  ·
    refine ⟨2261451151311036815022283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12061072806992196346785509 2261451151311036815022283)
    ·
      refine ⟨3392176726966555222533425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2261451151311036815022283 3392176726966555222533425)
      ·
        refine ⟨2544132545224916416900069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3392176726966555222533425 2544132545224916416900069)
        ·
          refine ⟨477024852229671828168763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2544132545224916416900069 477024852229671828168763)
          ·
            refine ⟨715537278344507742253145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477024852229671828168763 715537278344507742253145)
            ·
              refine ⟨536652958758380806689859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715537278344507742253145 536652958758380806689859)
              ·
                refine ⟨804979438137571210034789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536652958758380806689859 804979438137571210034789)
                ·
                  refine ⟨150933644650794601881523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 804979438137571210034789 150933644650794601881523)
                  ·
                    rfl

theorem cell20_330685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_330685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330685 prefixEnd_330685 := by exact prefixLift 330685
  have htrace : WordTrace (prefixWord ++ tailWord_330685) baseStart_330685 baseEnd_330685 := by
    simpa [prefixWord, tailWord_330685, baseEnd_330685] using wordTrace_append hprefix tailTrace_330685
  have hstable : (prefixWord ++ tailWord_330685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330685).length < 2 ^ (prefixWord ++ tailWord_330685).sum := by decide
  have hdescent : baseEnd_330685 < baseStart_330685 := by decide
  rcases family_descends (prefixWord ++ tailWord_330685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330709 : List Nat := [1, 3, 2, 3, 3, 2, 2, 4]
def baseStart_330709 : Nat := 118140960795 + 330709 * 2 ^ 59
def prefixEnd_330709 : Nat := 4983230072969 + 3 ^ 40 * 330709 * 2
def baseEnd_330709 : Nat := 50314866301585728360475

theorem tailTrace_330709 : CollatzResearch.WordTrace tailWord_330709 prefixEnd_330709 50314866301585728360475 := by
  unfold tailWord_330709
  simp only [CollatzResearch.WordTrace]
  refine ⟨12061948158905248445659181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8041298772603498963772787 12061948158905248445659181)
  ·
    refine ⟨4523230559589468167122193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12061948158905248445659181 4523230559589468167122193)
    ·
      refine ⟨3392422919692101125341645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4523230559589468167122193 3392422919692101125341645)
      ·
        refine ⟨1272158594884537922003117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3392422919692101125341645 1272158594884537922003117)
        ·
          refine ⟨477059473081701720751169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1272158594884537922003117 477059473081701720751169)
          ·
            refine ⟨357794604811276290563377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477059473081701720751169 357794604811276290563377)
            ·
              refine ⟨268345953608457217922533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357794604811276290563377 268345953608457217922533)
              ·
                refine ⟨50314866301585728360475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 268345953608457217922533 50314866301585728360475)
                ·
                  rfl

theorem cell20_330709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 4].length) (baseStart_330709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330709 prefixEnd_330709 := by exact prefixLift 330709
  have htrace : WordTrace (prefixWord ++ tailWord_330709) baseStart_330709 baseEnd_330709 := by
    simpa [prefixWord, tailWord_330709, baseEnd_330709] using wordTrace_append hprefix tailTrace_330709
  have hstable : (prefixWord ++ tailWord_330709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330709).length < 2 ^ (prefixWord ++ tailWord_330709).sum := by decide
  have hdescent : baseEnd_330709 < baseStart_330709 := by decide
  rcases family_descends (prefixWord ++ tailWord_330709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330713 : List Nat := [1, 2, 1, 2, 5, 2, 1, 6]
def baseStart_330713 : Nat := 118140960795 + 330713 * 2 ^ 59
def prefixEnd_330713 : Nat := 4983230072969 + 3 ^ 40 * 330713 * 2
def baseEnd_330713 : Nat := 50315474871250316316025

theorem tailTrace_330713 : CollatzResearch.WordTrace tailWord_330713 prefixEnd_330713 50315474871250316316025 := by
  unfold tailWord_330713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12062094050890757128804793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8041396033927171419203195 12062094050890757128804793)
  ·
    refine ⟨9046570538168067846603595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12062094050890757128804793 9046570538168067846603595)
    ·
      refine ⟨13569855807252101769905393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9046570538168067846603595 13569855807252101769905393)
      ·
        refine ⟨10177391855439076327429045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13569855807252101769905393 10177391855439076327429045)
        ·
          refine ⟨954130486447413405696473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10177391855439076327429045 954130486447413405696473)
          ·
            refine ⟨715597864835560054272355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954130486447413405696473 715597864835560054272355)
            ·
              refine ⟨1073396797253340081408533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715597864835560054272355 1073396797253340081408533)
              ·
                refine ⟨50315474871250316316025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1073396797253340081408533 50315474871250316316025)
                ·
                  rfl

theorem cell20_330713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_330713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330713 prefixEnd_330713 := by exact prefixLift 330713
  have htrace : WordTrace (prefixWord ++ tailWord_330713) baseStart_330713 baseEnd_330713 := by
    simpa [prefixWord, tailWord_330713, baseEnd_330713] using wordTrace_append hprefix tailTrace_330713
  have hstable : (prefixWord ++ tailWord_330713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330713).length < 2 ^ (prefixWord ++ tailWord_330713).sum := by decide
  have hdescent : baseEnd_330713 < baseStart_330713 := by decide
  rcases family_descends (prefixWord ++ tailWord_330713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330719 : List Nat := [1, 1, 2, 3, 6, 1, 1, 3, 2]
def baseStart_330719 : Nat := 118140960795 + 330719 * 2 ^ 59
def prefixEnd_330719 : Nat := 4983230072969 + 3 ^ 40 * 330719 * 2
def baseEnd_330719 : Nat := 150949163177241594748051

theorem tailTrace_330719 : CollatzResearch.WordTrace tailWord_330719 prefixEnd_330719 150949163177241594748051 := by
  unfold tailWord_330719
  simp only [CollatzResearch.WordTrace]
  refine ⟨12062312888869020153523211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8041541925912680102348807 12062312888869020153523211)
  ·
    refine ⟨18093469333303530230284817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12062312888869020153523211 18093469333303530230284817)
    ·
      refine ⟨13570101999977647672713613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18093469333303530230284817 13570101999977647672713613)
      ·
        refine ⟨5088788249991617877267605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13570101999977647672713613 5088788249991617877267605)
        ·
          refine ⟨238536949218357087996919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5088788249991617877267605 238536949218357087996919)
          ·
            refine ⟨357805423827535631995379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238536949218357087996919 357805423827535631995379)
            ·
              refine ⟨536708135741303447993069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357805423827535631995379 536708135741303447993069)
              ·
                refine ⟨201265550902988792997401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 536708135741303447993069 201265550902988792997401)
                ·
                  refine ⟨150949163177241594748051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201265550902988792997401 150949163177241594748051)
                  ·
                    rfl

theorem cell20_330719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 2].length) (baseStart_330719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330719 prefixEnd_330719 := by exact prefixLift 330719
  have htrace : WordTrace (prefixWord ++ tailWord_330719) baseStart_330719 baseEnd_330719 := by
    simpa [prefixWord, tailWord_330719, baseEnd_330719] using wordTrace_append hprefix tailTrace_330719
  have hstable : (prefixWord ++ tailWord_330719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330719).length < 2 ^ (prefixWord ++ tailWord_330719).sum := by decide
  have hdescent : baseEnd_330719 < baseStart_330719 := by decide
  rcases family_descends (prefixWord ++ tailWord_330719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330750 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_330750 : Nat := 118140960795 + 330750 * 2 ^ 59
def prefixEnd_330750 : Nat := 4983230072969 + 3 ^ 40 * 330750 * 2
def baseEnd_330750 : Nat := 150963312421943264714591

theorem tailTrace_330750 : CollatzResearch.WordTrace tailWord_330750 prefixEnd_330750 150963312421943264714591 := by
  unfold tailWord_330750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507930443969589055987713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8042295701171141631934469 1507930443969589055987713)
  ·
    refine ⟨1130947832977191791990785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1507930443969589055987713 1130947832977191791990785)
    ·
      refine ⟨848210874732893843993089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1130947832977191791990785 848210874732893843993089)
      ·
        refine ⟨636158156049670382994817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 848210874732893843993089 636158156049670382994817)
        ·
          refine ⟨477118617037252787246113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636158156049670382994817 477118617037252787246113)
          ·
            refine ⟨357838962777939590434585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477118617037252787246113 357838962777939590434585)
            ·
              refine ⟨268379222083454692825939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357838962777939590434585 268379222083454692825939)
              ·
                refine ⟨402568833125182039238909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268379222083454692825939 402568833125182039238909)
                ·
                  refine ⟨150963312421943264714591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402568833125182039238909 150963312421943264714591)
                  ·
                    rfl

theorem cell20_330750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_330750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330750 prefixEnd_330750 := by exact prefixLift 330750
  have htrace : WordTrace (prefixWord ++ tailWord_330750) baseStart_330750 baseEnd_330750 := by
    simpa [prefixWord, tailWord_330750, baseEnd_330750] using wordTrace_append hprefix tailTrace_330750
  have hstable : (prefixWord ++ tailWord_330750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330750).length < 2 ^ (prefixWord ++ tailWord_330750).sum := by decide
  have hdescent : baseEnd_330750 < baseStart_330750 := by decide
  rcases family_descends (prefixWord ++ tailWord_330750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330803 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_330803 : Nat := 118140960795 + 330803 * 2 ^ 59
def prefixEnd_330803 : Nat := 4983230072969 + 3 ^ 40 * 330803 * 2
def baseEnd_330803 : Nat := 150987503066110635947707

theorem tailTrace_330803 : CollatzResearch.WordTrace tailWord_330803 prefixEnd_330803 150987503066110635947707 := by
  unfold tailWord_330803
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065376620564702499581063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8043584413709801666387375 12065376620564702499581063)
  ·
    refine ⟨18098064930847053749371595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12065376620564702499581063 18098064930847053749371595)
    ·
      refine ⟨27147097396270580624057393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18098064930847053749371595 27147097396270580624057393)
      ·
        refine ⟨20360323047202935468043045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27147097396270580624057393 20360323047202935468043045)
        ·
          refine ⟨3817560571350550400258071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20360323047202935468043045 3817560571350550400258071)
          ·
            refine ⟨5726340857025825600387107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817560571350550400258071 5726340857025825600387107)
            ·
              refine ⟨8589511285538738400580661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5726340857025825600387107 8589511285538738400580661)
              ·
                refine ⟨805266683019256725054437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8589511285538738400580661 805266683019256725054437)
                ·
                  refine ⟨150987503066110635947707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805266683019256725054437 150987503066110635947707)
                  ·
                    rfl

theorem cell20_330803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_330803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330803 prefixEnd_330803 := by exact prefixLift 330803
  have htrace : WordTrace (prefixWord ++ tailWord_330803) baseStart_330803 baseEnd_330803 := by
    simpa [prefixWord, tailWord_330803, baseEnd_330803] using wordTrace_append hprefix tailTrace_330803
  have hstable : (prefixWord ++ tailWord_330803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330803).length < 2 ^ (prefixWord ++ tailWord_330803).sum := by decide
  have hdescent : baseEnd_330803 < baseStart_330803 := by decide
  rcases family_descends (prefixWord ++ tailWord_330803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330806 : List Nat := [5, 1, 2, 1, 1, 2, 3, 5]
def baseStart_330806 : Nat := 118140960795 + 330806 * 2 ^ 59
def prefixEnd_330806 : Nat := 4983230072969 + 3 ^ 40 * 330806 * 2
def baseEnd_330806 : Nat := 50329624115951986282565

theorem tailTrace_330806 : CollatzResearch.WordTrace tailWord_330806 prefixEnd_330806 50329624115951986282565 := by
  unfold tailWord_330806
  simp only [CollatzResearch.WordTrace]
  refine ⟨754092877472114625746267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8043657359702556007960181 754092877472114625746267)
  ·
    refine ⟨1131139316208171938619401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 754092877472114625746267 1131139316208171938619401)
    ·
      refine ⟨848354487156128953964551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1131139316208171938619401 848354487156128953964551)
      ·
        refine ⟨1272531730734193430946827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848354487156128953964551 1272531730734193430946827)
        ·
          refine ⟨1908797596101290146420241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272531730734193430946827 1908797596101290146420241)
          ·
            refine ⟨1431598197075967609815181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1908797596101290146420241 1431598197075967609815181)
            ·
              refine ⟨536849323903487853680693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1431598197075967609815181 536849323903487853680693)
              ·
                refine ⟨50329624115951986282565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 536849323903487853680693 50329624115951986282565)
                ·
                  rfl

theorem cell20_330806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_330806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330806 prefixEnd_330806 := by exact prefixLift 330806
  have htrace : WordTrace (prefixWord ++ tailWord_330806) baseStart_330806 baseEnd_330806 := by
    simpa [prefixWord, tailWord_330806, baseEnd_330806] using wordTrace_append hprefix tailTrace_330806
  have hstable : (prefixWord ++ tailWord_330806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330806).length < 2 ^ (prefixWord ++ tailWord_330806).sum := by decide
  have hdescent : baseEnd_330806 < baseStart_330806 := by decide
  rcases family_descends (prefixWord ++ tailWord_330806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330813 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 3]
def baseStart_330813 : Nat := 118140960795 + 330813 * 2 ^ 59
def prefixEnd_330813 : Nat := 4983230072969 + 3 ^ 40 * 330813 * 2
def baseEnd_330813 : Nat := 150992067338595045614333

theorem tailTrace_330813 : CollatzResearch.WordTrace tailWord_330813 prefixEnd_330813 150992067338595045614333 := by
  unfold tailWord_330813
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065741350528474207445093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8043827567018982804963395 12065741350528474207445093)
  ·
    refine ⟨2262326503224088913895955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12065741350528474207445093 2262326503224088913895955)
    ·
      refine ⟨3393489754836133370843933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262326503224088913895955 3393489754836133370843933)
      ·
        refine ⟨1272558658063550014066475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3393489754836133370843933 1272558658063550014066475)
        ·
          refine ⟨1908837987095325021099713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272558658063550014066475 1908837987095325021099713)
          ·
            refine ⟨1431628490321493765824785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1908837987095325021099713 1431628490321493765824785)
            ·
              refine ⟨1073721367741120324368589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1431628490321493765824785 1073721367741120324368589)
              ·
                refine ⟨402645512902920121638221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1073721367741120324368589 402645512902920121638221)
                ·
                  refine ⟨150992067338595045614333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402645512902920121638221 150992067338595045614333)
                  ·
                    rfl

theorem cell20_330813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_330813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330813 prefixEnd_330813 := by exact prefixLift 330813
  have htrace : WordTrace (prefixWord ++ tailWord_330813) baseStart_330813 baseEnd_330813 := by
    simpa [prefixWord, tailWord_330813, baseEnd_330813] using wordTrace_append hprefix tailTrace_330813
  have hstable : (prefixWord ++ tailWord_330813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330813).length < 2 ^ (prefixWord ++ tailWord_330813).sum := by decide
  have hdescent : baseEnd_330813 < baseStart_330813 := by decide
  rcases family_descends (prefixWord ++ tailWord_330813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330837 : List Nat := [1, 3, 2, 2, 1, 2, 4, 3, 2]
def baseStart_330837 : Nat := 118140960795 + 330837 * 2 ^ 59
def prefixEnd_330837 : Nat := 4983230072969 + 3 ^ 40 * 330837 * 2
def baseEnd_330837 : Nat := 151003021592557628814235

theorem tailTrace_330837 : CollatzResearch.WordTrace tailWord_330837 prefixEnd_330837 151003021592557628814235 := by
  unfold tailWord_330837
  simp only [CollatzResearch.WordTrace]
  refine ⟨12066616702441526306318765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8044411134961017537545843 12066616702441526306318765)
  ·
    refine ⟨4524981263415572364869537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12066616702441526306318765 4524981263415572364869537)
    ·
      refine ⟨3393735947561679273652153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4524981263415572364869537 3393735947561679273652153)
      ·
        refine ⟨2545301960671259455239115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3393735947561679273652153 2545301960671259455239115)
        ·
          refine ⟨3817952941006889182858673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2545301960671259455239115 3817952941006889182858673)
          ·
            refine ⟨2863464705755166887144005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3817952941006889182858673 2863464705755166887144005)
            ·
              refine ⟨536899632329093791339501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2863464705755166887144005 536899632329093791339501)
              ·
                refine ⟨201337362123410171752313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 536899632329093791339501 201337362123410171752313)
                ·
                  refine ⟨151003021592557628814235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201337362123410171752313 151003021592557628814235)
                  ·
                    rfl

theorem cell20_330837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_330837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330837 prefixEnd_330837 := by exact prefixLift 330837
  have htrace : WordTrace (prefixWord ++ tailWord_330837) baseStart_330837 baseEnd_330837 := by
    simpa [prefixWord, tailWord_330837, baseEnd_330837] using wordTrace_append hprefix tailTrace_330837
  have hstable : (prefixWord ++ tailWord_330837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330837).length < 2 ^ (prefixWord ++ tailWord_330837).sum := by decide
  have hdescent : baseEnd_330837 < baseStart_330837 := by decide
  rcases family_descends (prefixWord ++ tailWord_330837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330848 : List Nat := [2, 1, 1, 3, 2, 2, 9]
def baseStart_330848 : Nat := 118140960795 + 330848 * 2 ^ 59
def prefixEnd_330848 : Nat := 4983230072969 + 3 ^ 40 * 330848 * 2
def baseEnd_330848 : Nat := 16778671365810053271947

theorem tailTrace_330848 : CollatzResearch.WordTrace tailWord_330848 prefixEnd_330848 16778671365810053271947 := by
  unfold tailWord_330848
  simp only [CollatzResearch.WordTrace]
  refine ⟨6033508952700837592484599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8044678603601116789979465 6033508952700837592484599)
  ·
    refine ⟨9050263429051256388726899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6033508952700837592484599 9050263429051256388726899)
    ·
      refine ⟨13575395143576884583090349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9050263429051256388726899 13575395143576884583090349)
      ·
        refine ⟨5090773178841331718658881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13575395143576884583090349 5090773178841331718658881)
        ·
          refine ⟨3818079884130998788994161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5090773178841331718658881 3818079884130998788994161)
          ·
            refine ⟨2863559913098249091745621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3818079884130998788994161 2863559913098249091745621)
            ·
              refine ⟨16778671365810053271947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2863559913098249091745621 16778671365810053271947)
              ·
                rfl

theorem cell20_330848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 9].length) (baseStart_330848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330848 prefixEnd_330848 := by exact prefixLift 330848
  have htrace : WordTrace (prefixWord ++ tailWord_330848) baseStart_330848 baseEnd_330848 := by
    simpa [prefixWord, tailWord_330848, baseEnd_330848] using wordTrace_append hprefix tailTrace_330848
  have hstable : (prefixWord ++ tailWord_330848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330848).length < 2 ^ (prefixWord ++ tailWord_330848).sum := by decide
  have hdescent : baseEnd_330848 < baseStart_330848 := by decide
  rcases family_descends (prefixWord ++ tailWord_330848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330858 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_330858 : Nat := 118140960795 + 330858 * 2 ^ 59
def prefixEnd_330858 : Nat := 4983230072969 + 3 ^ 40 * 330858 * 2
def baseEnd_330858 : Nat := 151012606564774889114149

theorem tailTrace_330858 : CollatzResearch.WordTrace tailWord_330858 prefixEnd_330858 151012606564774889114149 := by
  unfold tailWord_330858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016845658841361723208307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8044921756910297928555485 3016845658841361723208307)
  ·
    refine ⟨4525268488262042584812461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3016845658841361723208307 4525268488262042584812461)
    ·
      refine ⟨1696975683098265969304673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4525268488262042584812461 1696975683098265969304673)
      ·
        refine ⟨1272731762323699476978505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1696975683098265969304673 1272731762323699476978505)
        ·
          refine ⟨954548821742774607733879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272731762323699476978505 954548821742774607733879)
          ·
            refine ⟨1431823232614161911600819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954548821742774607733879 1431823232614161911600819)
            ·
              refine ⟨2147734848921242867401229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1431823232614161911600819 2147734848921242867401229)
              ·
                refine ⟨805400568345466075275461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2147734848921242867401229 805400568345466075275461)
                ·
                  refine ⟨151012606564774889114149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805400568345466075275461 151012606564774889114149)
                  ·
                    rfl

theorem cell20_330858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_330858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330858 prefixEnd_330858 := by exact prefixLift 330858
  have htrace : WordTrace (prefixWord ++ tailWord_330858) baseStart_330858 baseEnd_330858 := by
    simpa [prefixWord, tailWord_330858, baseEnd_330858] using wordTrace_append hprefix tailTrace_330858
  have hstable : (prefixWord ++ tailWord_330858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330858).length < 2 ^ (prefixWord ++ tailWord_330858).sum := by decide
  have hdescent : baseEnd_330858 < baseStart_330858 := by decide
  rcases family_descends (prefixWord ++ tailWord_330858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330872 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_330872 : Nat := 118140960795 + 330872 * 2 ^ 59
def prefixEnd_330872 : Nat := 4983230072969 + 3 ^ 40 * 330872 * 2
def baseEnd_330872 : Nat := 151018996546253062647425

theorem tailTrace_330872 : CollatzResearch.WordTrace tailWord_330872 prefixEnd_330872 151018996546253062647425 := by
  unfold tailWord_330872
  simp only [CollatzResearch.WordTrace]
  refine ⟨6033946628657363641921435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8045262171543151522561913 6033946628657363641921435)
  ·
    refine ⟨9050919942986045462882153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6033946628657363641921435 9050919942986045462882153)
    ·
      refine ⟨6788189957239534097161615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9050919942986045462882153 6788189957239534097161615)
      ·
        refine ⟨10182284935859301145742423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6788189957239534097161615 10182284935859301145742423)
        ·
          refine ⟨15273427403788951718613635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10182284935859301145742423 15273427403788951718613635)
          ·
            refine ⟨22910141105683427577920453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15273427403788951718613635 22910141105683427577920453)
            ·
              refine ⟨4295651457315642670860085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22910141105683427577920453 4295651457315642670860085)
              ·
                refine ⟨402717324123341500393133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4295651457315642670860085 402717324123341500393133)
                ·
                  refine ⟨151018996546253062647425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402717324123341500393133 151018996546253062647425)
                  ·
                    rfl

theorem cell20_330872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_330872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330872 prefixEnd_330872 := by exact prefixLift 330872
  have htrace : WordTrace (prefixWord ++ tailWord_330872) baseStart_330872 baseEnd_330872 := by
    simpa [prefixWord, tailWord_330872, baseEnd_330872] using wordTrace_append hprefix tailTrace_330872
  have hstable : (prefixWord ++ tailWord_330872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330872).length < 2 ^ (prefixWord ++ tailWord_330872).sum := by decide
  have hdescent : baseEnd_330872 < baseStart_330872 := by decide
  rcases family_descends (prefixWord ++ tailWord_330872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330878 : List Nat := [4, 2, 4, 1, 1, 1, 1, 6]
def baseStart_330878 : Nat := 118140960795 + 330878 * 2 ^ 59
def prefixEnd_330878 : Nat := 4983230072969 + 3 ^ 40 * 330878 * 2
def baseEnd_330878 : Nat := 50340578369914569482467

theorem tailTrace_330878 : CollatzResearch.WordTrace tailWord_330878 prefixEnd_330878 50340578369914569482467 := by
  unfold tailWord_330878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508514011911623788570161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8045408063528660205707525 1508514011911623788570161)
  ·
    refine ⟨1131385508933717841427621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1508514011911623788570161 1131385508933717841427621)
    ·
      refine ⟨212134782925072095267679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1131385508933717841427621 212134782925072095267679)
      ·
        refine ⟨318202174387608142901519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212134782925072095267679 318202174387608142901519)
        ·
          refine ⟨477303261581412214352279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318202174387608142901519 477303261581412214352279)
          ·
            refine ⟨715954892372118321528419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477303261581412214352279 715954892372118321528419)
            ·
              refine ⟨1073932338558177482292629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715954892372118321528419 1073932338558177482292629)
              ·
                refine ⟨50340578369914569482467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1073932338558177482292629 50340578369914569482467)
                ·
                  rfl

theorem cell20_330878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_330878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330878 prefixEnd_330878 := by exact prefixLift 330878
  have htrace : WordTrace (prefixWord ++ tailWord_330878) baseStart_330878 baseEnd_330878 := by
    simpa [prefixWord, tailWord_330878, baseEnd_330878] using wordTrace_append hprefix tailTrace_330878
  have hstable : (prefixWord ++ tailWord_330878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330878).length < 2 ^ (prefixWord ++ tailWord_330878).sum := by decide
  have hdescent : baseEnd_330878 < baseStart_330878 := by decide
  rcases family_descends (prefixWord ++ tailWord_330878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330896 : List Nat := [2, 1, 1, 1, 1, 1, 4, 7, 2]
def baseStart_330896 : Nat := 118140960795 + 330896 * 2 ^ 59
def prefixEnd_330896 : Nat := 4983230072969 + 3 ^ 40 * 330896 * 2
def baseEnd_330896 : Nat := 151029950800215645847327

theorem tailTrace_330896 : CollatzResearch.WordTrace tailWord_330896 prefixEnd_330896 151029950800215645847327 := by
  unfold tailWord_330896
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034384304613889691358271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8045845739485186255144361 6034384304613889691358271)
  ·
    refine ⟨9051576456920834537037407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6034384304613889691358271 9051576456920834537037407)
    ·
      refine ⟨13577364685381251805556111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9051576456920834537037407 13577364685381251805556111)
      ·
        refine ⟨20366047028071877708334167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13577364685381251805556111 20366047028071877708334167)
        ·
          refine ⟨30549070542107816562501251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20366047028071877708334167 30549070542107816562501251)
          ·
            refine ⟨45823605813161724843751877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30549070542107816562501251 45823605813161724843751877)
            ·
              refine ⟨8591926089967823408203477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45823605813161724843751877 8591926089967823408203477)
              ·
                refine ⟨201373267733620861129769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8591926089967823408203477 201373267733620861129769)
                ·
                  refine ⟨151029950800215645847327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201373267733620861129769 151029950800215645847327)
                  ·
                    rfl

theorem cell20_330896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_330896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330896 prefixEnd_330896 := by exact prefixLift 330896
  have htrace : WordTrace (prefixWord ++ tailWord_330896) baseStart_330896 baseEnd_330896 := by
    simpa [prefixWord, tailWord_330896, baseEnd_330896] using wordTrace_append hprefix tailTrace_330896
  have hstable : (prefixWord ++ tailWord_330896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330896).length < 2 ^ (prefixWord ++ tailWord_330896).sum := by decide
  have hdescent : baseEnd_330896 < baseStart_330896 := by decide
  rcases family_descends (prefixWord ++ tailWord_330896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330903 : List Nat := [1, 1, 3, 3, 3, 3, 6]
def baseStart_330903 : Nat := 118140960795 + 330903 * 2 ^ 59
def prefixEnd_330903 : Nat := 4983230072969 + 3 ^ 40 * 330903 * 2
def baseEnd_330903 : Nat := 16781460643439414734885

theorem tailTrace_330903 : CollatzResearch.WordTrace tailWord_330903 prefixEnd_330903 16781460643439414734885 := by
  unfold tailWord_330903
  simp only [CollatzResearch.WordTrace]
  refine ⟨12069023920202419578221363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8046015946801613052147575 12069023920202419578221363)
  ·
    refine ⟨18103535880303629367332045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12069023920202419578221363 18103535880303629367332045)
    ·
      refine ⟨6788825955113861012749517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18103535880303629367332045 6788825955113861012749517)
      ·
        refine ⟨2545809733167697879781069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6788825955113861012749517 2545809733167697879781069)
        ·
          refine ⟨954678649937886704917901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2545809733167697879781069 954678649937886704917901)
          ·
            refine ⟨358004493726707514344213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 954678649937886704917901 358004493726707514344213)
            ·
              refine ⟨16781460643439414734885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 358004493726707514344213 16781460643439414734885)
              ·
                rfl

theorem cell20_330903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 6].length) (baseStart_330903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330903 prefixEnd_330903 := by exact prefixLift 330903
  have htrace : WordTrace (prefixWord ++ tailWord_330903) baseStart_330903 baseEnd_330903 := by
    simpa [prefixWord, tailWord_330903, baseEnd_330903] using wordTrace_append hprefix tailTrace_330903
  have hstable : (prefixWord ++ tailWord_330903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330903).length < 2 ^ (prefixWord ++ tailWord_330903).sum := by decide
  have hdescent : baseEnd_330903 < baseStart_330903 := by decide
  rcases family_descends (prefixWord ++ tailWord_330903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330927 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 3]
def baseStart_330927 : Nat := 118140960795 + 330927 * 2 ^ 59
def prefixEnd_330927 : Nat := 4983230072969 + 3 ^ 40 * 330927 * 2
def baseEnd_330927 : Nat := 151044100044917315813867

theorem tailTrace_330927 : CollatzResearch.WordTrace tailWord_330927 prefixEnd_330927 151044100044917315813867 := by
  unfold tailWord_330927
  simp only [CollatzResearch.WordTrace]
  refine ⟨12069899272115471677095035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8046599514743647784730023 12069899272115471677095035)
  ·
    refine ⟨18104848908173207515642553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12069899272115471677095035 18104848908173207515642553)
    ·
      refine ⟨13578636681129905636731915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18104848908173207515642553 13578636681129905636731915)
      ·
        refine ⟨20367955021694858455097873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13578636681129905636731915 20367955021694858455097873)
        ·
          refine ⟨15275966266271143841323405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20367955021694858455097873 15275966266271143841323405)
          ·
            refine ⟨5728487349851678940496277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15275966266271143841323405 5728487349851678940496277)
            ·
              refine ⟨268522844524297450335763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5728487349851678940496277 268522844524297450335763)
              ·
                refine ⟨402784266786446175503645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268522844524297450335763 402784266786446175503645)
                ·
                  refine ⟨151044100044917315813867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402784266786446175503645 151044100044917315813867)
                  ·
                    rfl

theorem cell20_330927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 3].length) (baseStart_330927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330927 prefixEnd_330927 := by exact prefixLift 330927
  have htrace : WordTrace (prefixWord ++ tailWord_330927) baseStart_330927 baseEnd_330927 := by
    simpa [prefixWord, tailWord_330927, baseEnd_330927] using wordTrace_append hprefix tailTrace_330927
  have hstable : (prefixWord ++ tailWord_330927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330927).length < 2 ^ (prefixWord ++ tailWord_330927).sum := by decide
  have hdescent : baseEnd_330927 < baseStart_330927 := by decide
  rcases family_descends (prefixWord ++ tailWord_330927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330964 : List Nat := [2, 4, 1, 4, 1, 2, 2, 2, 2]
def baseStart_330964 : Nat := 118140960795 + 330964 * 2 ^ 59
def prefixEnd_330964 : Nat := 4983230072969 + 3 ^ 40 * 330964 * 2
def baseEnd_330964 : Nat := 151060987853109631580383

theorem tailTrace_330964 : CollatzResearch.WordTrace tailWord_330964 prefixEnd_330964 151060987853109631580383 := by
  unfold tailWord_330964
  simp only [CollatzResearch.WordTrace]
  refine ⟨6035624386490713498095973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8047499181987617997461297 6035624386490713498095973)
  ·
    refine ⟨1131679572467008780892995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6035624386490713498095973 1131679572467008780892995)
    ·
      refine ⟨1697519358700513171339493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1131679572467008780892995 1697519358700513171339493)
      ·
        refine ⟨318284879756346219626155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1697519358700513171339493 318284879756346219626155)
        ·
          refine ⟨477427319634519329439233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318284879756346219626155 477427319634519329439233)
          ·
            refine ⟨358070489725889497079425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477427319634519329439233 358070489725889497079425)
            ·
              refine ⟨268552867294417122809569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358070489725889497079425 268552867294417122809569)
              ·
                refine ⟨201414650470812842107177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268552867294417122809569 201414650470812842107177)
                ·
                  refine ⟨151060987853109631580383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201414650470812842107177 151060987853109631580383)
                  ·
                    rfl

theorem cell20_330964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_330964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330964 prefixEnd_330964 := by exact prefixLift 330964
  have htrace : WordTrace (prefixWord ++ tailWord_330964) baseStart_330964 baseEnd_330964 := by
    simpa [prefixWord, tailWord_330964, baseEnd_330964] using wordTrace_append hprefix tailTrace_330964
  have hstable : (prefixWord ++ tailWord_330964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330964).length < 2 ^ (prefixWord ++ tailWord_330964).sum := by decide
  have hdescent : baseEnd_330964 < baseStart_330964 := by decide
  rcases family_descends (prefixWord ++ tailWord_330964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330965 : List Nat := [1, 3, 2, 4, 1, 1, 1, 4, 3]
def baseStart_330965 : Nat := 118140960795 + 330965 * 2 ^ 59
def prefixEnd_330965 : Nat := 4983230072969 + 3 ^ 40 * 330965 * 2
def baseEnd_330965 : Nat := 151061444280358072547045

theorem tailTrace_330965 : CollatzResearch.WordTrace tailWord_330965 prefixEnd_330965 151061444280358072547045 := by
  unfold tailWord_330965
  simp only [CollatzResearch.WordTrace]
  refine ⟨12071285245977804166978349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8047523497318536111318899 12071285245977804166978349)
  ·
    refine ⟨4526731967241676562616881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12071285245977804166978349 4526731967241676562616881)
    ·
      refine ⟨3395048975431257421962661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4526731967241676562616881 3395048975431257421962661)
      ·
        refine ⟨636571682893360766617999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3395048975431257421962661 636571682893360766617999)
        ·
          refine ⟨954857524340041149926999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636571682893360766617999 954857524340041149926999)
          ·
            refine ⟨1432286286510061724890499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954857524340041149926999 1432286286510061724890499)
            ·
              refine ⟨2148429429765092587335749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432286286510061724890499 2148429429765092587335749)
              ·
                refine ⟨402830518080954860125453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2148429429765092587335749 402830518080954860125453)
                ·
                  refine ⟨151061444280358072547045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402830518080954860125453 151061444280358072547045)
                  ·
                    rfl

theorem cell20_330965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_330965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_330965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_330965 prefixEnd_330965 := by exact prefixLift 330965
  have htrace : WordTrace (prefixWord ++ tailWord_330965) baseStart_330965 baseEnd_330965 := by
    simpa [prefixWord, tailWord_330965, baseEnd_330965] using wordTrace_append hprefix tailTrace_330965
  have hstable : (prefixWord ++ tailWord_330965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330965).length < 2 ^ (prefixWord ++ tailWord_330965).sum := by decide
  have hdescent : baseEnd_330965 < baseStart_330965 := by decide
  rcases family_descends (prefixWord ++ tailWord_330965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331006 : List Nat := [4, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_331006 : Nat := 118140960795 + 331006 * 2 ^ 59
def prefixEnd_331006 : Nat := 4983230072969 + 3 ^ 40 * 331006 * 2
def baseEnd_331006 : Nat := 151080157797544152180211

theorem tailTrace_331006 : CollatzResearch.WordTrace tailWord_331006 prefixEnd_331006 151080157797544152180211 := by
  unfold tailWord_331006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509097579853658521152609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8048520425886178779480581 1509097579853658521152609)
  ·
    refine ⟨1131823184890243890864457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1509097579853658521152609 1131823184890243890864457)
    ·
      refine ⟨848867388667682918148343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1131823184890243890864457 848867388667682918148343)
      ·
        refine ⟨1273301083001524377222515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848867388667682918148343 1273301083001524377222515)
        ·
          refine ⟨1909951624502286565833773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273301083001524377222515 1909951624502286565833773)
          ·
            refine ⟨716231859188357462187665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1909951624502286565833773 716231859188357462187665)
            ·
              refine ⟨537173894391268096640749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716231859188357462187665 537173894391268096640749)
              ·
                refine ⟨201440210396725536240281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 537173894391268096640749 201440210396725536240281)
                ·
                  refine ⟨151080157797544152180211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201440210396725536240281 151080157797544152180211)
                  ·
                    rfl

theorem cell20_331006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_331006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331006 prefixEnd_331006 := by exact prefixLift 331006
  have htrace : WordTrace (prefixWord ++ tailWord_331006) baseStart_331006 baseEnd_331006 := by
    simpa [prefixWord, tailWord_331006, baseEnd_331006] using wordTrace_append hprefix tailTrace_331006
  have hstable : (prefixWord ++ tailWord_331006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331006).length < 2 ^ (prefixWord ++ tailWord_331006).sum := by decide
  have hdescent : baseEnd_331006 < baseStart_331006 := by decide
  rcases family_descends (prefixWord ++ tailWord_331006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331048 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_331048 : Nat := 118140960795 + 331048 * 2 ^ 59
def prefixEnd_331048 : Nat := 4983230072969 + 3 ^ 40 * 331048 * 2
def baseEnd_331048 : Nat := 151099327741978672780039

theorem tailTrace_331048 : CollatzResearch.WordTrace tailWord_331048 prefixEnd_331048 151099327741978672780039 := by
  unfold tailWord_331048
  simp only [CollatzResearch.WordTrace]
  refine ⟨6037156252338554671124899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8049541669784739561499865 6037156252338554671124899)
  ·
    refine ⟨9055734378507832006687349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6037156252338554671124899 9055734378507832006687349)
    ·
      refine ⟨848975097985109250626939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9055734378507832006687349 848975097985109250626939)
      ·
        refine ⟨1273462646977663875940409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848975097985109250626939 1273462646977663875940409)
        ·
          refine ⟨955096985233247906955307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1273462646977663875940409 955096985233247906955307)
          ·
            refine ⟨1432645477849871860432961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955096985233247906955307 1432645477849871860432961)
            ·
              refine ⟨1074484108387403895324721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432645477849871860432961 1074484108387403895324721)
              ·
                refine ⟨805863081290552921493541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074484108387403895324721 805863081290552921493541)
                ·
                  refine ⟨151099327741978672780039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805863081290552921493541 151099327741978672780039)
                  ·
                    rfl

theorem cell20_331048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_331048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331048 prefixEnd_331048 := by exact prefixLift 331048
  have htrace : WordTrace (prefixWord ++ tailWord_331048) baseStart_331048 baseEnd_331048 := by
    simpa [prefixWord, tailWord_331048, baseEnd_331048] using wordTrace_append hprefix tailTrace_331048
  have hstable : (prefixWord ++ tailWord_331048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331048).length < 2 ^ (prefixWord ++ tailWord_331048).sum := by decide
  have hdescent : baseEnd_331048 < baseStart_331048 := by decide
  rcases family_descends (prefixWord ++ tailWord_331048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331078 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_331078 : Nat := 118140960795 + 331078 * 2 ^ 59
def prefixEnd_331078 : Nat := 4983230072969 + 3 ^ 40 * 331078 * 2
def baseEnd_331078 : Nat := 151113020559431901779917

theorem tailTrace_331078 : CollatzResearch.WordTrace tailWord_331078 prefixEnd_331078 151113020559431901779917 := by
  unfold tailWord_331078
  simp only [CollatzResearch.WordTrace]
  refine ⟨377356459205263264557559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8050271129712282977227925 377356459205263264557559)
  ·
    refine ⟨566034688807894896836339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 377356459205263264557559 566034688807894896836339)
    ·
      refine ⟨849052033211842345254509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566034688807894896836339 849052033211842345254509)
      ·
        refine ⟨318394512454440879470441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 849052033211842345254509 318394512454440879470441)
        ·
          refine ⟨238795884340830659602831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318394512454440879470441 238795884340830659602831)
          ·
            refine ⟨358193826511245989404247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238795884340830659602831 358193826511245989404247)
            ·
              refine ⟨537290739766868984106371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358193826511245989404247 537290739766868984106371)
              ·
                refine ⟨805936109650303476159557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537290739766868984106371 805936109650303476159557)
                ·
                  refine ⟨151113020559431901779917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 805936109650303476159557 151113020559431901779917)
                  ·
                    rfl

theorem cell20_331078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_331078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331078 prefixEnd_331078 := by exact prefixLift 331078
  have htrace : WordTrace (prefixWord ++ tailWord_331078) baseStart_331078 baseEnd_331078 := by
    simpa [prefixWord, tailWord_331078, baseEnd_331078] using wordTrace_append hprefix tailTrace_331078
  have hstable : (prefixWord ++ tailWord_331078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331078).length < 2 ^ (prefixWord ++ tailWord_331078).sum := by decide
  have hdescent : baseEnd_331078 < baseStart_331078 := by decide
  rcases family_descends (prefixWord ++ tailWord_331078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331093 : List Nat := [1, 3, 2, 2, 3, 2, 2, 5]
def baseStart_331093 : Nat := 118140960795 + 331093 * 2 ^ 59
def prefixEnd_331093 : Nat := 4983230072969 + 3 ^ 40 * 331093 * 2
def baseEnd_331093 : Nat := 50373288989386172093285

theorem tailTrace_331093 : CollatzResearch.WordTrace tailWord_331093 prefixEnd_331093 50373288989386172093285 := by
  unfold tailWord_331093
  simp only [CollatzResearch.WordTrace]
  refine ⟨12075953789514082027637933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8050635859676054685091955 12075953789514082027637933)
  ·
    refine ⟨4528482671067780760364225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12075953789514082027637933 4528482671067780760364225)
    ·
      refine ⟨3396362003300835570273169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4528482671067780760364225 3396362003300835570273169)
      ·
        refine ⟨2547271502475626677704877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3396362003300835570273169 2547271502475626677704877)
        ·
          refine ⟨955226813428360004139329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2547271502475626677704877 955226813428360004139329)
          ·
            refine ⟨716420110071270003104497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 955226813428360004139329 716420110071270003104497)
            ·
              refine ⟨537315082553452502328373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716420110071270003104497 537315082553452502328373)
              ·
                refine ⟨50373288989386172093285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 537315082553452502328373 50373288989386172093285)
                ·
                  rfl

theorem cell20_331093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_331093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331093 prefixEnd_331093 := by exact prefixLift 331093
  have htrace : WordTrace (prefixWord ++ tailWord_331093) baseStart_331093 baseEnd_331093 := by
    simpa [prefixWord, tailWord_331093, baseEnd_331093] using wordTrace_append hprefix tailTrace_331093
  have hstable : (prefixWord ++ tailWord_331093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331093).length < 2 ^ (prefixWord ++ tailWord_331093).sum := by decide
  have hdescent : baseEnd_331093 < baseStart_331093 := by decide
  rcases family_descends (prefixWord ++ tailWord_331093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331121 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_331121 : Nat := 118140960795 + 331121 * 2 ^ 59
def prefixEnd_331121 : Nat := 4983230072969 + 3 ^ 40 * 331121 * 2
def baseEnd_331121 : Nat := 151132646931114863346407

theorem tailTrace_331121 : CollatzResearch.WordTrace tailWord_331121 prefixEnd_331121 151132646931114863346407 := by
  unfold tailWord_331121
  simp only [CollatzResearch.WordTrace]
  refine ⟨12076975033412642809657217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8051316688941761873104811 12076975033412642809657217)
  ·
    refine ⟨9057731275059482107242913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12076975033412642809657217 9057731275059482107242913)
    ·
      refine ⟨6793298456294611580432185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9057731275059482107242913 6793298456294611580432185)
      ·
        refine ⟨5094973842220958685324139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6793298456294611580432185 5094973842220958685324139)
        ·
          refine ⟨7642460763331438027986209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5094973842220958685324139 7642460763331438027986209)
          ·
            refine ⟨5731845572498578520989657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7642460763331438027986209 5731845572498578520989657)
            ·
              refine ⟨4298884179373933890742243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5731845572498578520989657 4298884179373933890742243)
              ·
                refine ⟨6448326269060900836113365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4298884179373933890742243 6448326269060900836113365)
                ·
                  refine ⟨151132646931114863346407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6448326269060900836113365 151132646931114863346407)
                  ·
                    rfl

theorem cell20_331121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_331121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331121 prefixEnd_331121 := by exact prefixLift 331121
  have htrace : WordTrace (prefixWord ++ tailWord_331121) baseStart_331121 baseEnd_331121 := by
    simpa [prefixWord, tailWord_331121, baseEnd_331121] using wordTrace_append hprefix tailTrace_331121
  have hstable : (prefixWord ++ tailWord_331121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331121).length < 2 ^ (prefixWord ++ tailWord_331121).sum := by decide
  have hdescent : baseEnd_331121 < baseStart_331121 := by decide
  rcases family_descends (prefixWord ++ tailWord_331121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331137 : List Nat := [1, 2, 4, 3, 2, 2, 2, 2, 2]
def baseStart_331137 : Nat := 118140960795 + 331137 * 2 ^ 59
def prefixEnd_331137 : Nat := 4983230072969 + 3 ^ 40 * 331137 * 2
def baseEnd_331137 : Nat := 151139949767089918813009

theorem tailTrace_331137 : CollatzResearch.WordTrace tailWord_331137 prefixEnd_331137 151139949767089918813009 := by
  unfold tailWord_331137
  simp only [CollatzResearch.WordTrace]
  refine ⟨12077558601354677542239665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8051705734236451694826443 12077558601354677542239665)
  ·
    refine ⟨9058168951016008156679749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12077558601354677542239665 9058168951016008156679749)
    ·
      refine ⟨1698406678315501529377453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9058168951016008156679749 1698406678315501529377453)
      ·
        refine ⟨636902504368313073516545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1698406678315501529377453 636902504368313073516545)
        ·
          refine ⟨477676878276234805137409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636902504368313073516545 477676878276234805137409)
          ·
            refine ⟨358257658707176103853057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477676878276234805137409 358257658707176103853057)
            ·
              refine ⟨268693244030382077889793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358257658707176103853057 268693244030382077889793)
              ·
                refine ⟨201519933022786558417345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268693244030382077889793 201519933022786558417345)
                ·
                  refine ⟨151139949767089918813009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201519933022786558417345 151139949767089918813009)
                  ·
                    rfl

theorem cell20_331137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_331137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331137 prefixEnd_331137 := by exact prefixLift 331137
  have htrace : WordTrace (prefixWord ++ tailWord_331137) baseStart_331137 baseEnd_331137 := by
    simpa [prefixWord, tailWord_331137, baseEnd_331137] using wordTrace_append hprefix tailTrace_331137
  have hstable : (prefixWord ++ tailWord_331137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331137).length < 2 ^ (prefixWord ++ tailWord_331137).sum := by decide
  have hdescent : baseEnd_331137 < baseStart_331137 := by decide
  rcases family_descends (prefixWord ++ tailWord_331137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331141 : List Nat := [1, 3, 1, 1, 3, 1, 6, 2, 2]
def baseStart_331141 : Nat := 118140960795 + 331141 * 2 ^ 59
def prefixEnd_331141 : Nat := 4983230072969 + 3 ^ 40 * 331141 * 2
def baseEnd_331141 : Nat := 151141775476083682679659

theorem tailTrace_331141 : CollatzResearch.WordTrace tailWord_331141 prefixEnd_331141 151141775476083682679659 := by
  unfold tailWord_331141
  simp only [CollatzResearch.WordTrace]
  refine ⟨12077704493340186225385277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8051802995560124150256851 12077704493340186225385277)
  ·
    refine ⟨4529139185002569834519479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12077704493340186225385277 4529139185002569834519479)
    ·
      refine ⟨6793708777503854751779219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4529139185002569834519479 6793708777503854751779219)
      ·
        refine ⟨10190563166255782127668829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6793708777503854751779219 10190563166255782127668829)
        ·
          refine ⟨3821461187345918297875811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10190563166255782127668829 3821461187345918297875811)
          ·
            refine ⟨5732191781018877446813717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821461187345918297875811 5732191781018877446813717)
            ·
              refine ⟨268696489735259880319393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5732191781018877446813717 268696489735259880319393)
              ·
                refine ⟨201522367301444910239545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268696489735259880319393 201522367301444910239545)
                ·
                  refine ⟨151141775476083682679659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201522367301444910239545 151141775476083682679659)
                  ·
                    rfl

theorem cell20_331141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_331141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331141 prefixEnd_331141 := by exact prefixLift 331141
  have htrace : WordTrace (prefixWord ++ tailWord_331141) baseStart_331141 baseEnd_331141 := by
    simpa [prefixWord, tailWord_331141, baseEnd_331141] using wordTrace_append hprefix tailTrace_331141
  have hstable : (prefixWord ++ tailWord_331141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331141).length < 2 ^ (prefixWord ++ tailWord_331141).sum := by decide
  have hdescent : baseEnd_331141 < baseStart_331141 := by decide
  rcases family_descends (prefixWord ++ tailWord_331141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331159 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_331159 : Nat := 118140960795 + 331159 * 2 ^ 59
def prefixEnd_331159 : Nat := 4983230072969 + 3 ^ 40 * 331159 * 2
def baseEnd_331159 : Nat := 151149991166555620079585

theorem tailTrace_331159 : CollatzResearch.WordTrace tailWord_331159 prefixEnd_331159 151149991166555620079585 := by
  unfold tailWord_331159
  simp only [CollatzResearch.WordTrace]
  refine ⟨12078361007274975299540531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8052240671516650199693687 12078361007274975299540531)
  ·
    refine ⟨18117541510912462949310797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12078361007274975299540531 18117541510912462949310797)
    ·
      refine ⟨6794078066592173605991549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18117541510912462949310797 6794078066592173605991549)
      ·
        refine ⟨2547779274972065102246831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6794078066592173605991549 2547779274972065102246831)
        ·
          refine ⟨3821668912458097653370247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547779274972065102246831 3821668912458097653370247)
          ·
            refine ⟨5732503368687146480055371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821668912458097653370247 5732503368687146480055371)
            ·
              refine ⟨8598755053030719720083057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5732503368687146480055371 8598755053030719720083057)
              ·
                refine ⟨6449066289773039790062293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8598755053030719720083057 6449066289773039790062293)
                ·
                  refine ⟨151149991166555620079585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6449066289773039790062293 151149991166555620079585)
                  ·
                    rfl

theorem cell20_331159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_331159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331159 prefixEnd_331159 := by exact prefixLift 331159
  have htrace : WordTrace (prefixWord ++ tailWord_331159) baseStart_331159 baseEnd_331159 := by
    simpa [prefixWord, tailWord_331159, baseEnd_331159] using wordTrace_append hprefix tailTrace_331159
  have hstable : (prefixWord ++ tailWord_331159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331159).length < 2 ^ (prefixWord ++ tailWord_331159).sum := by decide
  have hdescent : baseEnd_331159 < baseStart_331159 := by decide
  rcases family_descends (prefixWord ++ tailWord_331159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331200 : List Nat := [2, 1, 1, 2, 3, 1, 4, 4, 2]
def baseStart_331200 : Nat := 118140960795 + 331200 * 2 ^ 59
def prefixEnd_331200 : Nat := 4983230072969 + 3 ^ 40 * 331200 * 2
def baseEnd_331200 : Nat := 151168704683741699712751

theorem tailTrace_331200 : CollatzResearch.WordTrace tailWord_331200 prefixEnd_331200 151168704683741699712751 := by
  unfold tailWord_331200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6039928200063219650891527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8053237600084292867855369 6039928200063219650891527)
  ·
    refine ⟨9059892300094829476337291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6039928200063219650891527 9059892300094829476337291)
    ·
      refine ⟨13589838450142244214505937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9059892300094829476337291 13589838450142244214505937)
      ·
        refine ⟨10192378837606683160879453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13589838450142244214505937 10192378837606683160879453)
        ·
          refine ⟨3822142064102506185329795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10192378837606683160879453 3822142064102506185329795)
          ·
            refine ⟨5733213096153759277994693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822142064102506185329795 5733213096153759277994693)
            ·
              refine ⟨1074977455528829864624005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5733213096153759277994693 1074977455528829864624005)
              ·
                refine ⟨201558272911655599617001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1074977455528829864624005 201558272911655599617001)
                ·
                  refine ⟨151168704683741699712751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201558272911655599617001 151168704683741699712751)
                  ·
                    rfl

theorem cell20_331200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_331200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331200 prefixEnd_331200 := by exact prefixLift 331200
  have htrace : WordTrace (prefixWord ++ tailWord_331200) baseStart_331200 baseEnd_331200 := by
    simpa [prefixWord, tailWord_331200, baseEnd_331200] using wordTrace_append hprefix tailTrace_331200
  have hstable : (prefixWord ++ tailWord_331200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331200).length < 2 ^ (prefixWord ++ tailWord_331200).sum := by decide
  have hdescent : baseEnd_331200 < baseStart_331200 := by decide
  rcases family_descends (prefixWord ++ tailWord_331200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331214 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_331214 : Nat := 118140960795 + 331214 * 2 ^ 59
def prefixEnd_331214 : Nat := 4983230072969 + 3 ^ 40 * 331214 * 2
def baseEnd_331214 : Nat := 151175094665219873246027

theorem tailTrace_331214 : CollatzResearch.WordTrace tailWord_331214 prefixEnd_331214 151175094665219873246027 := by
  unfold tailWord_331214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1510045877759464961599087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8053578014717146461861797 1510045877759464961599087)
  ·
    refine ⟨2265068816639197442398631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1510045877759464961599087 2265068816639197442398631)
    ·
      refine ⟨3397603224958796163597947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2265068816639197442398631 3397603224958796163597947)
      ·
        refine ⟨5096404837438194245396921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397603224958796163597947 5096404837438194245396921)
        ·
          refine ⟨3822303628078645684047691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5096404837438194245396921 3822303628078645684047691)
          ·
            refine ⟨5733455442117968526071537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3822303628078645684047691 5733455442117968526071537)
            ·
              refine ⟨4300091581588476394553653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5733455442117968526071537 4300091581588476394553653)
              ·
                refine ⟨403133585773919661989405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4300091581588476394553653 403133585773919661989405)
                ·
                  refine ⟨151175094665219873246027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403133585773919661989405 151175094665219873246027)
                  ·
                    rfl

theorem cell20_331214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_331214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331214 prefixEnd_331214 := by exact prefixLift 331214
  have htrace : WordTrace (prefixWord ++ tailWord_331214) baseStart_331214 baseEnd_331214 := by
    simpa [prefixWord, tailWord_331214, baseEnd_331214] using wordTrace_append hprefix tailTrace_331214
  have hstable : (prefixWord ++ tailWord_331214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331214).length < 2 ^ (prefixWord ++ tailWord_331214).sum := by decide
  have hdescent : baseEnd_331214 < baseStart_331214 := by decide
  rcases family_descends (prefixWord ++ tailWord_331214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331221 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_331221 : Nat := 118140960795 + 331221 * 2 ^ 59
def prefixEnd_331221 : Nat := 4983230072969 + 3 ^ 40 * 331221 * 2
def baseEnd_331221 : Nat := 151178289655958960012665

theorem tailTrace_331221 : CollatzResearch.WordTrace tailWord_331221 prefixEnd_331221 151178289655958960012665 := by
  unfold tailWord_331221
  simp only [CollatzResearch.WordTrace]
  refine ⟨12080622333050359888297517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8053748222033573258865011 12080622333050359888297517)
  ·
    refine ⟨4530233374893884958111569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12080622333050359888297517 4530233374893884958111569)
    ·
      refine ⟨3397675031170413718583677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4530233374893884958111569 3397675031170413718583677)
      ·
        refine ⟨1274128136688905144468879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3397675031170413718583677 1274128136688905144468879)
        ·
          refine ⟨1911192205033357716703319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274128136688905144468879 1911192205033357716703319)
          ·
            refine ⟨2866788307550036575054979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911192205033357716703319 2866788307550036575054979)
            ·
              refine ⟨4300182461325054862582469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866788307550036575054979 4300182461325054862582469)
              ·
                refine ⟨806284211498447786734213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4300182461325054862582469 806284211498447786734213)
                ·
                  refine ⟨151178289655958960012665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806284211498447786734213 151178289655958960012665)
                  ·
                    rfl

theorem cell20_331221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_331221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331221 prefixEnd_331221 := by exact prefixLift 331221
  have htrace : WordTrace (prefixWord ++ tailWord_331221) baseStart_331221 baseEnd_331221 := by
    simpa [prefixWord, tailWord_331221, baseEnd_331221] using wordTrace_append hprefix tailTrace_331221
  have hstable : (prefixWord ++ tailWord_331221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331221).length < 2 ^ (prefixWord ++ tailWord_331221).sum := by decide
  have hdescent : baseEnd_331221 < baseStart_331221 := by decide
  rcases family_descends (prefixWord ++ tailWord_331221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331265 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 3]
def baseStart_331265 : Nat := 118140960795 + 331265 * 2 ^ 59
def prefixEnd_331265 : Nat := 4983230072969 + 3 ^ 40 * 331265 * 2
def baseEnd_331265 : Nat := 151198372454890362545819

theorem tailTrace_331265 : CollatzResearch.WordTrace tailWord_331265 prefixEnd_331265 151198372454890362545819 := by
  unfold tailWord_331265
  simp only [CollatzResearch.WordTrace]
  refine ⟨12082227144890955402899249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8054818096593970268599499 12082227144890955402899249)
  ·
    refine ⟨9061670358668216552174437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12082227144890955402899249 9061670358668216552174437)
    ·
      refine ⟨1699063192250290603532707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9061670358668216552174437 1699063192250290603532707)
      ·
        refine ⟨2548594788375435905299061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1699063192250290603532707 2548594788375435905299061)
        ·
          refine ⟨238930761410197116121787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2548594788375435905299061 238930761410197116121787)
          ·
            refine ⟨358396142115295674182681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238930761410197116121787 358396142115295674182681)
            ·
              refine ⟨268797106586471755637011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358396142115295674182681 268797106586471755637011)
              ·
                refine ⟨403195659879707633455517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268797106586471755637011 403195659879707633455517)
                ·
                  refine ⟨151198372454890362545819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403195659879707633455517 151198372454890362545819)
                  ·
                    rfl

theorem cell20_331265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_331265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331265 prefixEnd_331265 := by exact prefixLift 331265
  have htrace : WordTrace (prefixWord ++ tailWord_331265) baseStart_331265 baseEnd_331265 := by
    simpa [prefixWord, tailWord_331265, baseEnd_331265] using wordTrace_append hprefix tailTrace_331265
  have hstable : (prefixWord ++ tailWord_331265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331265).length < 2 ^ (prefixWord ++ tailWord_331265).sum := by decide
  have hdescent : baseEnd_331265 < baseStart_331265 := by decide
  rcases family_descends (prefixWord ++ tailWord_331265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331304 : List Nat := [2, 1, 5, 2, 10]
def baseStart_331304 : Nat := 118140960795 + 331304 * 2 ^ 59
def prefixEnd_331304 : Nat := 4983230072969 + 3 ^ 40 * 331304 * 2
def baseEnd_331304 : Nat := 1866866334784932842539

theorem tailTrace_331304 : CollatzResearch.WordTrace tailWord_331304 prefixEnd_331304 1866866334784932842539 := by
  unfold tailWord_331304
  simp only [CollatzResearch.WordTrace]
  refine ⟨6041824795874832531784483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8055766394499776709045977 6041824795874832531784483)
  ·
    refine ⟨9062737193812248797676725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6041824795874832531784483 9062737193812248797676725)
    ·
      refine ⟨849631611919898324782193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9062737193812248797676725 849631611919898324782193)
      ·
        refine ⟨637223708939923743586645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 849631611919898324782193 637223708939923743586645)
        ·
          refine ⟨1866866334784932842539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 637223708939923743586645 1866866334784932842539)
          ·
            rfl

theorem cell20_331304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 10].length) (baseStart_331304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331304 prefixEnd_331304 := by exact prefixLift 331304
  have htrace : WordTrace (prefixWord ++ tailWord_331304) baseStart_331304 baseEnd_331304 := by
    simpa [prefixWord, tailWord_331304, baseEnd_331304] using wordTrace_append hprefix tailTrace_331304
  have hstable : (prefixWord ++ tailWord_331304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331304).length < 2 ^ (prefixWord ++ tailWord_331304).sum := by decide
  have hdescent : baseEnd_331304 < baseStart_331304 := by decide
  rcases family_descends (prefixWord ++ tailWord_331304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331310 : List Nat := [4, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_331310 : Nat := 118140960795 + 331310 * 2 ^ 59
def prefixEnd_331310 : Nat := 4983230072969 + 3 ^ 40 * 331310 * 2
def baseEnd_331310 : Nat := 151218911681070206045635

theorem tailTrace_331310 : CollatzResearch.WordTrace tailWord_331310 prefixEnd_331310 151218911681070206045635 := by
  unfold tailWord_331310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1510483553715991011035923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8055912286485285392191589 1510483553715991011035923)
  ·
    refine ⟨2265725330573986516553885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1510483553715991011035923 2265725330573986516553885)
    ·
      refine ⟨849646998965244943707707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2265725330573986516553885 849646998965244943707707)
      ·
        refine ⟨1274470498447867415561561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849646998965244943707707 1274470498447867415561561)
        ·
          refine ⟨955852873835900561671171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274470498447867415561561 955852873835900561671171)
          ·
            refine ⟨1433779310753850842506757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955852873835900561671171 1433779310753850842506757)
            ·
              refine ⟨268833620766347032970017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1433779310753850842506757 268833620766347032970017)
              ·
                refine ⟨201625215574760274727513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268833620766347032970017 201625215574760274727513)
                ·
                  refine ⟨151218911681070206045635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201625215574760274727513 151218911681070206045635)
                  ·
                    rfl

theorem cell20_331310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_331310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331310 prefixEnd_331310 := by exact prefixLift 331310
  have htrace : WordTrace (prefixWord ++ tailWord_331310) baseStart_331310 baseEnd_331310 := by
    simpa [prefixWord, tailWord_331310, baseEnd_331310] using wordTrace_append hprefix tailTrace_331310
  have hstable : (prefixWord ++ tailWord_331310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331310).length < 2 ^ (prefixWord ++ tailWord_331310).sum := by decide
  have hdescent : baseEnd_331310 < baseStart_331310 := by decide
  rcases family_descends (prefixWord ++ tailWord_331310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331321 : List Nat := [1, 2, 1, 5, 1, 4, 1, 5]
def baseStart_331321 : Nat := 118140960795 + 331321 * 2 ^ 59
def prefixEnd_331321 : Nat := 4983230072969 + 3 ^ 40 * 331321 * 2
def baseEnd_331321 : Nat := 50407977460267685559641

theorem tailTrace_331321 : CollatzResearch.WordTrace tailWord_331321 prefixEnd_331321 50407977460267685559641 := by
  unfold tailWord_331321
  simp only [CollatzResearch.WordTrace]
  refine ⟨12084269632688076966937817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8056179755125384644625211 12084269632688076966937817)
  ·
    refine ⟨9063202224516057725203363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12084269632688076966937817 9063202224516057725203363)
    ·
      refine ⟨13594803336774086587805045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9063202224516057725203363 13594803336774086587805045)
      ·
        refine ⟨1274512812822570617606723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13594803336774086587805045 1274512812822570617606723)
        ·
          refine ⟨1911769219233855926410085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274512812822570617606723 1911769219233855926410085)
          ·
            refine ⟨358456728606347986201891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1911769219233855926410085 358456728606347986201891)
            ·
              refine ⟨537685092909521979302837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358456728606347986201891 537685092909521979302837)
              ·
                refine ⟨50407977460267685559641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 537685092909521979302837 50407977460267685559641)
                ·
                  rfl

theorem cell20_331321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 5].length) (baseStart_331321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331321 prefixEnd_331321 := by exact prefixLift 331321
  have htrace : WordTrace (prefixWord ++ tailWord_331321) baseStart_331321 baseEnd_331321 := by
    simpa [prefixWord, tailWord_331321, baseEnd_331321] using wordTrace_append hprefix tailTrace_331321
  have hstable : (prefixWord ++ tailWord_331321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331321).length < 2 ^ (prefixWord ++ tailWord_331321).sum := by decide
  have hdescent : baseEnd_331321 < baseStart_331321 := by decide
  rcases family_descends (prefixWord ++ tailWord_331321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331349 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_331349 : Nat := 118140960795 + 331349 * 2 ^ 59
def prefixEnd_331349 : Nat := 4983230072969 + 3 ^ 40 * 331349 * 2
def baseEnd_331349 : Nat := 151236712343759403745475

theorem tailTrace_331349 : CollatzResearch.WordTrace tailWord_331349 prefixEnd_331349 151236712343759403745475 := by
  unfold tailWord_331349
  simp only [CollatzResearch.WordTrace]
  refine ⟨12085290876586637748957101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8056860584391091832638067 12085290876586637748957101)
  ·
    refine ⟨4531984078719989155858913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12085290876586637748957101 4531984078719989155858913)
    ·
      refine ⟨3398988059039991866894185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4531984078719989155858913 3398988059039991866894185)
      ·
        refine ⟨2549241044279993900170639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3398988059039991866894185 2549241044279993900170639)
        ·
          refine ⟨3823861566419990850255959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549241044279993900170639 3823861566419990850255959)
          ·
            refine ⟨5735792349629986275383939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3823861566419990850255959 5735792349629986275383939)
            ·
              refine ⟨8603688524444979413075909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5735792349629986275383939 8603688524444979413075909)
              ·
                refine ⟨1613191598333433639951733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8603688524444979413075909 1613191598333433639951733)
                ·
                  refine ⟨151236712343759403745475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1613191598333433639951733 151236712343759403745475)
                  ·
                    rfl

theorem cell20_331349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_331349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331349 prefixEnd_331349 := by exact prefixLift 331349
  have htrace : WordTrace (prefixWord ++ tailWord_331349) baseStart_331349 baseEnd_331349 := by
    simpa [prefixWord, tailWord_331349, baseEnd_331349] using wordTrace_append hprefix tailTrace_331349
  have hstable : (prefixWord ++ tailWord_331349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331349).length < 2 ^ (prefixWord ++ tailWord_331349).sum := by decide
  have hdescent : baseEnd_331349 < baseStart_331349 := by decide
  rcases family_descends (prefixWord ++ tailWord_331349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331428 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 4]
def baseStart_331428 : Nat := 118140960795 + 331428 * 2 ^ 59
def prefixEnd_331428 : Nat := 4983230072969 + 3 ^ 40 * 331428 * 2
def baseEnd_331428 : Nat := 151272770096386240111819

theorem tailTrace_331428 : CollatzResearch.WordTrace tailWord_331428 prefixEnd_331428 151272770096386240111819 := by
  unfold tailWord_331428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044086121650217120541469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8058781495533622827388625 6044086121650217120541469)
  ·
    refine ⟨2266532295618831420203051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6044086121650217120541469 2266532295618831420203051)
    ·
      refine ⟨3399798443428247130304577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266532295618831420203051 3399798443428247130304577)
      ·
        refine ⟨2549848832571185347728433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3399798443428247130304577 2549848832571185347728433)
        ·
          refine ⟨1912386624428389010796325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2549848832571185347728433 1912386624428389010796325)
          ·
            refine ⟨358572492080322939524311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1912386624428389010796325 358572492080322939524311)
            ·
              refine ⟨537858738120484409286467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358572492080322939524311 537858738120484409286467)
              ·
                refine ⟨806788107180726613929701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537858738120484409286467 806788107180726613929701)
                ·
                  refine ⟨151272770096386240111819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 806788107180726613929701 151272770096386240111819)
                  ·
                    rfl

theorem cell20_331428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_331428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331428 prefixEnd_331428 := by exact prefixLift 331428
  have htrace : WordTrace (prefixWord ++ tailWord_331428) baseStart_331428 baseEnd_331428 := by
    simpa [prefixWord, tailWord_331428, baseEnd_331428] using wordTrace_append hprefix tailTrace_331428
  have hstable : (prefixWord ++ tailWord_331428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331428).length < 2 ^ (prefixWord ++ tailWord_331428).sum := by decide
  have hdescent : baseEnd_331428 < baseStart_331428 := by decide
  rcases family_descends (prefixWord ++ tailWord_331428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331438 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_331438 : Nat := 118140960795 + 331438 * 2 ^ 59
def prefixEnd_331438 : Nat := 4983230072969 + 3 ^ 40 * 331438 * 2
def baseEnd_331438 : Nat := 151277334368870649778445

theorem tailTrace_331438 : CollatzResearch.WordTrace tailWord_331438 prefixEnd_331438 151277334368870649778445 := by
  unfold tailWord_331438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511067121658025743618371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8059024648842803965964645 1511067121658025743618371)
  ·
    refine ⟨2266600682487038615427557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511067121658025743618371 2266600682487038615427557)
    ·
      refine ⟨424987627966319740392667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2266600682487038615427557 424987627966319740392667)
      ·
        refine ⟨637481441949479610589001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424987627966319740392667 637481441949479610589001)
        ·
          refine ⟨478111081462109707941751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637481441949479610589001 478111081462109707941751)
          ·
            refine ⟨717166622193164561912627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478111081462109707941751 717166622193164561912627)
            ·
              refine ⟨1075749933289746842868941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717166622193164561912627 1075749933289746842868941)
              ·
                refine ⟨403406224983655066075853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1075749933289746842868941 403406224983655066075853)
                ·
                  refine ⟨151277334368870649778445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403406224983655066075853 151277334368870649778445)
                  ·
                    rfl

theorem cell20_331438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_331438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331438 prefixEnd_331438 := by exact prefixLift 331438
  have htrace : WordTrace (prefixWord ++ tailWord_331438) baseStart_331438 baseEnd_331438 := by
    simpa [prefixWord, tailWord_331438, baseEnd_331438] using wordTrace_append hprefix tailTrace_331438
  have hstable : (prefixWord ++ tailWord_331438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331438).length < 2 ^ (prefixWord ++ tailWord_331438).sum := by decide
  have hdescent : baseEnd_331438 < baseStart_331438 := by decide
  rcases family_descends (prefixWord ++ tailWord_331438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331477 : List Nat := [1, 3, 2, 14]
def baseStart_331477 : Nat := 118140960795 + 331477 * 2 ^ 59
def prefixEnd_331477 : Nat := 4983230072969 + 3 ^ 40 * 331477 * 2
def baseEnd_331477 : Nat := 622613724409711306495

theorem tailTrace_331477 : CollatzResearch.WordTrace tailWord_331477 prefixEnd_331477 622613724409711306495 := by
  unfold tailWord_331477
  simp only [CollatzResearch.WordTrace]
  refine ⟨12089959420122915609616685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8059972946748610406411123 12089959420122915609616685)
  ·
    refine ⟨4533734782546093353606257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12089959420122915609616685 4533734782546093353606257)
    ·
      refine ⟨3400301086909570015204693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4533734782546093353606257 3400301086909570015204693)
      ·
        refine ⟨622613724409711306495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 3400301086909570015204693 622613724409711306495)
        ·
          rfl

theorem cell20_331477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 14].length) (baseStart_331477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331477 prefixEnd_331477 := by exact prefixLift 331477
  have htrace : WordTrace (prefixWord ++ tailWord_331477) baseStart_331477 baseEnd_331477 := by
    simpa [prefixWord, tailWord_331477, baseEnd_331477] using wordTrace_append hprefix tailTrace_331477
  have hstable : (prefixWord ++ tailWord_331477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331477).length < 2 ^ (prefixWord ++ tailWord_331477).sum := by decide
  have hdescent : baseEnd_331477 < baseStart_331477 := by decide
  rcases family_descends (prefixWord ++ tailWord_331477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331480 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_331480 : Nat := 118140960795 + 331480 * 2 ^ 59
def prefixEnd_331480 : Nat := 4983230072969 + 3 ^ 40 * 331480 * 2
def baseEnd_331480 : Nat := 151296504313305170378273

theorem tailTrace_331480 : CollatzResearch.WordTrace tailWord_331480 prefixEnd_331480 151296504313305170378273 := by
  unfold tailWord_331480
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045034419556023560987947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8060045892741364747983929 6045034419556023560987947)
  ·
    refine ⟨9067551629334035341481921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6045034419556023560987947 9067551629334035341481921)
    ·
      refine ⟨6800663722000526506111441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9067551629334035341481921 6800663722000526506111441)
      ·
        refine ⟨5100497791500394879583581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6800663722000526506111441 5100497791500394879583581)
        ·
          refine ⟨1912686671812648079843843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5100497791500394879583581 1912686671812648079843843)
          ·
            refine ⟨2869030007718972119765765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912686671812648079843843 2869030007718972119765765)
            ·
              refine ⟨537943126447307272456081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2869030007718972119765765 537943126447307272456081)
              ·
                refine ⟨403457344835480454342061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537943126447307272456081 403457344835480454342061)
                ·
                  refine ⟨151296504313305170378273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403457344835480454342061 151296504313305170378273)
                  ·
                    rfl

theorem cell20_331480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_331480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331480 prefixEnd_331480 := by exact prefixLift 331480
  have htrace : WordTrace (prefixWord ++ tailWord_331480) baseStart_331480 baseEnd_331480 := by
    simpa [prefixWord, tailWord_331480, baseEnd_331480] using wordTrace_append hprefix tailTrace_331480
  have hstable : (prefixWord ++ tailWord_331480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331480).length < 2 ^ (prefixWord ++ tailWord_331480).sum := by decide
  have hdescent : baseEnd_331480 < baseStart_331480 := by decide
  rcases family_descends (prefixWord ++ tailWord_331480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331539 : List Nat := [1, 1, 1, 2, 1, 3, 2, 6, 3]
def baseStart_331539 : Nat := 118140960795 + 331539 * 2 ^ 59
def prefixEnd_331539 : Nat := 4983230072969 + 3 ^ 40 * 331539 * 2
def baseEnd_331539 : Nat := 151323433520963187411365

theorem tailTrace_331539 : CollatzResearch.WordTrace tailWord_331539 prefixEnd_331539 151323433520963187411365 := by
  unfold tailWord_331539
  simp only [CollatzResearch.WordTrace]
  refine ⟨12092220745898300198373671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8061480497265533465582447 12092220745898300198373671)
  ·
    refine ⟨18138331118847450297560507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12092220745898300198373671 18138331118847450297560507)
    ·
      refine ⟨27207496678271175446340761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18138331118847450297560507 27207496678271175446340761)
      ·
        refine ⟨20405622508703381584755571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27207496678271175446340761 20405622508703381584755571)
        ·
          refine ⟨30608433763055072377133357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20405622508703381584755571 30608433763055072377133357)
          ·
            refine ⟨11478162661145652141425009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30608433763055072377133357 11478162661145652141425009)
            ·
              refine ⟨8608621995859239106068757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11478162661145652141425009 8608621995859239106068757)
              ·
                refine ⟨403529156055901833096973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8608621995859239106068757 403529156055901833096973)
                ·
                  refine ⟨151323433520963187411365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403529156055901833096973 151323433520963187411365)
                  ·
                    rfl

theorem cell20_331539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_331539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331539 prefixEnd_331539 := by exact prefixLift 331539
  have htrace : WordTrace (prefixWord ++ tailWord_331539) baseStart_331539 baseEnd_331539 := by
    simpa [prefixWord, tailWord_331539, baseEnd_331539] using wordTrace_append hprefix tailTrace_331539
  have hstable : (prefixWord ++ tailWord_331539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331539).length < 2 ^ (prefixWord ++ tailWord_331539).sum := by decide
  have hdescent : baseEnd_331539 < baseStart_331539 := by decide
  rcases family_descends (prefixWord ++ tailWord_331539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331570 : List Nat := [3, 2, 1, 1, 3, 3, 1, 6]
def baseStart_331570 : Nat := 118140960795 + 331570 * 2 ^ 59
def prefixEnd_331570 : Nat := 4983230072969 + 3 ^ 40 * 331570 * 2
def baseEnd_331570 : Nat := 50445860921888285792635

theorem tailTrace_331570 : CollatzResearch.WordTrace tailWord_331570 prefixEnd_331570 50445860921888285792635 := by
  unfold tailWord_331570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023337852196498123188041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8062234272523994995168109 3023337852196498123188041)
  ·
    refine ⟨2267503389147373592391031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3023337852196498123188041 2267503389147373592391031)
    ·
      refine ⟨3401255083721060388586547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267503389147373592391031 3401255083721060388586547)
      ·
        refine ⟨5101882625581590582879821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401255083721060388586547 5101882625581590582879821)
        ·
          refine ⟨1913205984593096468579933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5101882625581590582879821 1913205984593096468579933)
          ·
            refine ⟨717452244222411175717475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1913205984593096468579933 717452244222411175717475)
            ·
              refine ⟨1076178366333616763576213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717452244222411175717475 1076178366333616763576213)
              ·
                refine ⟨50445860921888285792635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1076178366333616763576213 50445860921888285792635)
                ·
                  rfl

theorem cell20_331570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_331570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331570 prefixEnd_331570 := by exact prefixLift 331570
  have htrace : WordTrace (prefixWord ++ tailWord_331570) baseStart_331570 baseEnd_331570 := by
    simpa [prefixWord, tailWord_331570, baseEnd_331570] using wordTrace_append hprefix tailTrace_331570
  have hstable : (prefixWord ++ tailWord_331570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331570).length < 2 ^ (prefixWord ++ tailWord_331570).sum := by decide
  have hdescent : baseEnd_331570 < baseStart_331570 := by decide
  rcases family_descends (prefixWord ++ tailWord_331570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331580 : List Nat := [2, 2, 2, 2, 1, 1, 5, 3, 2]
def baseStart_331580 : Nat := 118140960795 + 331580 * 2 ^ 59
def prefixEnd_331580 : Nat := 4983230072969 + 3 ^ 40 * 331580 * 2
def baseEnd_331580 : Nat := 151342147038149267044531

theorem tailTrace_331580 : CollatzResearch.WordTrace tailWord_331580 prefixEnd_331580 151342147038149267044531 := by
  unfold tailWord_331580
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046858069374882100308097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8062477425833176133744129 6046858069374882100308097)
  ·
    refine ⟨4535143552031161575231073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6046858069374882100308097 4535143552031161575231073)
    ·
      refine ⟨3401357664023371181423305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4535143552031161575231073 3401357664023371181423305)
      ·
        refine ⟨2551018248017528386067479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3401357664023371181423305 2551018248017528386067479)
        ·
          refine ⟨3826527372026292579101219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551018248017528386067479 3826527372026292579101219)
          ·
            refine ⟨5739791058039438868651829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826527372026292579101219 5739791058039438868651829)
            ·
              refine ⟨538105411691197393936109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5739791058039438868651829 538105411691197393936109)
              ·
                refine ⟨201789529384199022726041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 538105411691197393936109 201789529384199022726041)
                ·
                  refine ⟨151342147038149267044531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201789529384199022726041 151342147038149267044531)
                  ·
                    rfl

theorem cell20_331580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_331580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331580 prefixEnd_331580 := by exact prefixLift 331580
  have htrace : WordTrace (prefixWord ++ tailWord_331580) baseStart_331580 baseEnd_331580 := by
    simpa [prefixWord, tailWord_331580, baseEnd_331580] using wordTrace_append hprefix tailTrace_331580
  have hstable : (prefixWord ++ tailWord_331580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331580).length < 2 ^ (prefixWord ++ tailWord_331580).sum := by decide
  have hdescent : baseEnd_331580 < baseStart_331580 := by decide
  rcases family_descends (prefixWord ++ tailWord_331580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331591 : List Nat := [1, 1, 4, 1, 2, 1, 10]
def baseStart_331591 : Nat := 118140960795 + 331591 * 2 ^ 59
def prefixEnd_331591 : Nat := 4983230072969 + 3 ^ 40 * 331591 * 2
def baseEnd_331591 : Nat := 16816351970875790853091

theorem tailTrace_331591 : CollatzResearch.WordTrace tailWord_331591 prefixEnd_331591 16816351970875790853091 := by
  unfold tailWord_331591
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094117341709913079266627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8062744894473275386177751 12094117341709913079266627)
  ·
    refine ⟨18141176012564869618899941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12094117341709913079266627 18141176012564869618899941)
    ·
      refine ⟨3401470502355913053543739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18141176012564869618899941 3401470502355913053543739)
      ·
        refine ⟨5102205753533869580315609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401470502355913053543739 5102205753533869580315609)
        ·
          refine ⟨3826654315150402185236707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5102205753533869580315609 3826654315150402185236707)
          ·
            refine ⟨5739981472725603277855061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826654315150402185236707 5739981472725603277855061)
            ·
              refine ⟨16816351970875790853091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5739981472725603277855061 16816351970875790853091)
              ·
                rfl

theorem cell20_331591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 10].length) (baseStart_331591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331591 prefixEnd_331591 := by exact prefixLift 331591
  have htrace : WordTrace (prefixWord ++ tailWord_331591) baseStart_331591 baseEnd_331591 := by
    simpa [prefixWord, tailWord_331591, baseEnd_331591] using wordTrace_append hprefix tailTrace_331591
  have hstable : (prefixWord ++ tailWord_331591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331591).length < 2 ^ (prefixWord ++ tailWord_331591).sum := by decide
  have hdescent : baseEnd_331591 < baseStart_331591 := by decide
  rcases family_descends (prefixWord ++ tailWord_331591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331597 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 4]
def baseStart_331597 : Nat := 118140960795 + 331597 * 2 ^ 59
def prefixEnd_331597 : Nat := 4983230072969 + 3 ^ 40 * 331597 * 2
def baseEnd_331597 : Nat := 151349906301372763477795

theorem tailTrace_331597 : CollatzResearch.WordTrace tailWord_331597 prefixEnd_331597 151349906301372763477795 := by
  unfold tailWord_331597
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094336179688176103985045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8062890786458784069323363 12094336179688176103985045)
  ·
    refine ⟨566922008422883254874299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12094336179688176103985045 566922008422883254874299)
    ·
      refine ⟨850383012634324882311449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566922008422883254874299 850383012634324882311449)
      ·
        refine ⟨637787259475743661733587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 850383012634324882311449 637787259475743661733587)
        ·
          refine ⟨956680889213615492600381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637787259475743661733587 956680889213615492600381)
          ·
            refine ⟨358755333455105809725143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 956680889213615492600381 358755333455105809725143)
            ·
              refine ⟨538133000182658714587715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358755333455105809725143 538133000182658714587715)
              ·
                refine ⟨807199500273988071881573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538133000182658714587715 807199500273988071881573)
                ·
                  refine ⟨151349906301372763477795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807199500273988071881573 151349906301372763477795)
                  ·
                    rfl

theorem cell20_331597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_331597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331597 prefixEnd_331597 := by exact prefixLift 331597
  have htrace : WordTrace (prefixWord ++ tailWord_331597) baseStart_331597 baseEnd_331597 := by
    simpa [prefixWord, tailWord_331597, baseEnd_331597] using wordTrace_append hprefix tailTrace_331597
  have hstable : (prefixWord ++ tailWord_331597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331597).length < 2 ^ (prefixWord ++ tailWord_331597).sum := by decide
  have hdescent : baseEnd_331597 < baseStart_331597 := by decide
  rcases family_descends (prefixWord ++ tailWord_331597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331601 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_331601 : Nat := 118140960795 + 331601 * 2 ^ 59
def prefixEnd_331601 : Nat := 4983230072969 + 3 ^ 40 * 331601 * 2
def baseEnd_331601 : Nat := 151351732010366527344445

theorem tailTrace_331601 : CollatzResearch.WordTrace tailWord_331601 prefixEnd_331601 151351732010366527344445 := by
  unfold tailWord_331601
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094482071673684787130657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8062988047782456524753771 12094482071673684787130657)
  ·
    refine ⟨9070861553755263590347993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12094482071673684787130657 9070861553755263590347993)
    ·
      refine ⟨6803146165316447692760995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9070861553755263590347993 6803146165316447692760995)
      ·
        refine ⟨10204719247974671539141493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6803146165316447692760995 10204719247974671539141493)
        ·
          refine ⟨956692429497625456794515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10204719247974671539141493 956692429497625456794515)
          ·
            refine ⟨1435038644246438185191773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956692429497625456794515 1435038644246438185191773)
            ·
              refine ⟨538139491592414319446915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1435038644246438185191773 538139491592414319446915)
              ·
                refine ⟨807209237388621479170373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538139491592414319446915 807209237388621479170373)
                ·
                  refine ⟨151351732010366527344445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807209237388621479170373 151351732010366527344445)
                  ·
                    rfl

theorem cell20_331601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_331601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331601 prefixEnd_331601 := by exact prefixLift 331601
  have htrace : WordTrace (prefixWord ++ tailWord_331601) baseStart_331601 baseEnd_331601 := by
    simpa [prefixWord, tailWord_331601, baseEnd_331601] using wordTrace_append hprefix tailTrace_331601
  have hstable : (prefixWord ++ tailWord_331601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331601).length < 2 ^ (prefixWord ++ tailWord_331601).sum := by decide
  have hdescent : baseEnd_331601 < baseStart_331601 := by decide
  rcases family_descends (prefixWord ++ tailWord_331601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331660 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_331660 : Nat := 118140960795 + 331660 * 2 ^ 59
def prefixEnd_331660 : Nat := 4983230072969 + 3 ^ 40 * 331660 * 2
def baseEnd_331660 : Nat := 151378661218024544377537

theorem tailTrace_331660 : CollatzResearch.WordTrace tailWord_331660 prefixEnd_331660 151378661218024544377537 := by
  unfold tailWord_331660
  simp only [CollatzResearch.WordTrace]
  refine ⟨6048316989229968931764217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8064422652306625242352289 6048316989229968931764217)
  ·
    refine ⟨4536237741922476698823163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6048316989229968931764217 4536237741922476698823163)
    ·
      refine ⟨6804356612883715048234745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4536237741922476698823163 6804356612883715048234745)
      ·
        refine ⟨5103267459662786286176059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6804356612883715048234745 5103267459662786286176059)
        ·
          refine ⟨7654901189494179429264089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5103267459662786286176059 7654901189494179429264089)
          ·
            refine ⟨5741175892120634571948067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7654901189494179429264089 5741175892120634571948067)
            ·
              refine ⟨8611763838180951857922101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5741175892120634571948067 8611763838180951857922101)
              ·
                refine ⟨807352859829464236680197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8611763838180951857922101 807352859829464236680197)
                ·
                  refine ⟨151378661218024544377537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807352859829464236680197 151378661218024544377537)
                  ·
                    rfl

theorem cell20_331660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_331660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331660 prefixEnd_331660 := by exact prefixLift 331660
  have htrace : WordTrace (prefixWord ++ tailWord_331660) baseStart_331660 baseEnd_331660 := by
    simpa [prefixWord, tailWord_331660, baseEnd_331660] using wordTrace_append hprefix tailTrace_331660
  have hstable : (prefixWord ++ tailWord_331660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331660).length < 2 ^ (prefixWord ++ tailWord_331660).sum := by decide
  have hdescent : baseEnd_331660 < baseStart_331660 := by decide
  rcases family_descends (prefixWord ++ tailWord_331660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331677 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_331677 : Nat := 118140960795 + 331677 * 2 ^ 59
def prefixEnd_331677 : Nat := 4983230072969 + 3 ^ 40 * 331677 * 2
def baseEnd_331677 : Nat := 151386420481248040810801

theorem tailTrace_331677 : CollatzResearch.WordTrace tailWord_331677 prefixEnd_331677 151386420481248040810801 := by
  unfold tailWord_331677
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097254019398349766897285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8064836012932233177931523 12097254019398349766897285)
  ·
    refine ⟨2268235128637190581293241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12097254019398349766897285 2268235128637190581293241)
    ·
      refine ⟨1701176346477892935969931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2268235128637190581293241 1701176346477892935969931)
      ·
        refine ⟨2551764519716839403954897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1701176346477892935969931 2551764519716839403954897)
        ·
          refine ⟨1913823389787629552966173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551764519716839403954897 1913823389787629552966173)
          ·
            refine ⟨717683771170361082362315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1913823389787629552966173 717683771170361082362315)
            ·
              refine ⟨1076525656755541623543473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717683771170361082362315 1076525656755541623543473)
              ·
                refine ⟨807394242566656217657605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076525656755541623543473 807394242566656217657605)
                ·
                  refine ⟨151386420481248040810801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807394242566656217657605 151386420481248040810801)
                  ·
                    rfl

theorem cell20_331677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_331677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331677 prefixEnd_331677 := by exact prefixLift 331677
  have htrace : WordTrace (prefixWord ++ tailWord_331677) baseStart_331677 baseEnd_331677 := by
    simpa [prefixWord, tailWord_331677, baseEnd_331677] using wordTrace_append hprefix tailTrace_331677
  have hstable : (prefixWord ++ tailWord_331677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331677).length < 2 ^ (prefixWord ++ tailWord_331677).sum := by decide
  have hdescent : baseEnd_331677 < baseStart_331677 := by decide
  rcases family_descends (prefixWord ++ tailWord_331677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331705 : List Nat := [1, 2, 1, 4, 2, 1, 9]
def baseStart_331705 : Nat := 118140960795 + 331705 * 2 ^ 59
def prefixEnd_331705 : Nat := 4983230072969 + 3 ^ 40 * 331705 * 2
def baseEnd_331705 : Nat := 16822133382689376430817

theorem tailTrace_331705 : CollatzResearch.WordTrace tailWord_331705 prefixEnd_331705 16822133382689376430817 := by
  unfold tailWord_331705
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098275263296910548916569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8065516842197940365944379 12098275263296910548916569)
  ·
    refine ⟨9073706447472682911687427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12098275263296910548916569 9073706447472682911687427)
    ·
      refine ⟨13610559671209024367531141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9073706447472682911687427 13610559671209024367531141)
      ·
        refine ⟨2551979938351692068912089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13610559671209024367531141 2551979938351692068912089)
        ·
          refine ⟨1913984953763769051684067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551979938351692068912089 1913984953763769051684067)
          ·
            refine ⟨2870977430645653577526101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913984953763769051684067 2870977430645653577526101)
            ·
              refine ⟨16822133382689376430817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2870977430645653577526101 16822133382689376430817)
              ·
                rfl

theorem cell20_331705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 9].length) (baseStart_331705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331705 prefixEnd_331705 := by exact prefixLift 331705
  have htrace : WordTrace (prefixWord ++ tailWord_331705) baseStart_331705 baseEnd_331705 := by
    simpa [prefixWord, tailWord_331705, baseEnd_331705] using wordTrace_append hprefix tailTrace_331705
  have hstable : (prefixWord ++ tailWord_331705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331705).length < 2 ^ (prefixWord ++ tailWord_331705).sum := by decide
  have hdescent : baseEnd_331705 < baseStart_331705 := by decide
  rcases family_descends (prefixWord ++ tailWord_331705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331736 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_331736 : Nat := 118140960795 + 331736 * 2 ^ 59
def prefixEnd_331736 : Nat := 4983230072969 + 3 ^ 40 * 331736 * 2
def baseEnd_331736 : Nat := 151413349688906057843893

theorem tailTrace_331736 : CollatzResearch.WordTrace tailWord_331736 prefixEnd_331736 151413349688906057843893 := by
  unfold tailWord_331736
  simp only [CollatzResearch.WordTrace]
  refine ⟨6049702963092301421647531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8066270617456401895530041 6049702963092301421647531)
  ·
    refine ⟨9074554444638452132471297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6049702963092301421647531 9074554444638452132471297)
    ·
      refine ⟨6805915833478839099353473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9074554444638452132471297 6805915833478839099353473)
      ·
        refine ⟨5104436875109129324515105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6805915833478839099353473 5104436875109129324515105)
        ·
          refine ⟨3828327656331846993386329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5104436875109129324515105 3828327656331846993386329)
          ·
            refine ⟨2871245742248885245039747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3828327656331846993386329 2871245742248885245039747)
            ·
              refine ⟨4306868613373327867559621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871245742248885245039747 4306868613373327867559621)
              ·
                refine ⟨807537865007498975167429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4306868613373327867559621 807537865007498975167429)
                ·
                  refine ⟨151413349688906057843893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807537865007498975167429 151413349688906057843893)
                  ·
                    rfl

theorem cell20_331736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_331736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331736 prefixEnd_331736 := by exact prefixLift 331736
  have htrace : WordTrace (prefixWord ++ tailWord_331736) baseStart_331736 baseEnd_331736 := by
    simpa [prefixWord, tailWord_331736, baseEnd_331736] using wordTrace_append hprefix tailTrace_331736
  have hstable : (prefixWord ++ tailWord_331736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331736).length < 2 ^ (prefixWord ++ tailWord_331736).sum := by decide
  have hdescent : baseEnd_331736 < baseStart_331736 := by decide
  rcases family_descends (prefixWord ++ tailWord_331736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331766 : List Nat := [5, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_331766 : Nat := 118140960795 + 331766 * 2 ^ 59
def prefixEnd_331766 : Nat := 4983230072969 + 3 ^ 40 * 331766 * 2
def baseEnd_331766 : Nat := 151427042506359286843771

theorem tailTrace_331766 : CollatzResearch.WordTrace tailWord_331766 prefixEnd_331766 151427042506359286843771 := by
  unfold tailWord_331766
  simp only [CollatzResearch.WordTrace]
  refine ⟨756281257254744872930447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8067000077383945311258101 756281257254744872930447)
  ·
    refine ⟨1134421885882117309395671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 756281257254744872930447 1134421885882117309395671)
    ·
      refine ⟨1701632828823175964093507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1134421885882117309395671 1701632828823175964093507)
      ·
        refine ⟨2552449243234763946140261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1701632828823175964093507 2552449243234763946140261)
        ·
          refine ⟨478584233106518239901299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2552449243234763946140261 478584233106518239901299)
          ·
            refine ⟨717876349659777359851949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478584233106518239901299 717876349659777359851949)
            ·
              refine ⟨269203631122416509944481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 717876349659777359851949 269203631122416509944481)
              ·
                refine ⟨201902723341812382458361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269203631122416509944481 201902723341812382458361)
                ·
                  refine ⟨151427042506359286843771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201902723341812382458361 151427042506359286843771)
                  ·
                    rfl

theorem cell20_331766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_331766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331766 prefixEnd_331766 := by exact prefixLift 331766
  have htrace : WordTrace (prefixWord ++ tailWord_331766) baseStart_331766 baseEnd_331766 := by
    simpa [prefixWord, tailWord_331766, baseEnd_331766] using wordTrace_append hprefix tailTrace_331766
  have hstable : (prefixWord ++ tailWord_331766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331766).length < 2 ^ (prefixWord ++ tailWord_331766).sum := by decide
  have hdescent : baseEnd_331766 < baseStart_331766 := by decide
  rcases family_descends (prefixWord ++ tailWord_331766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331781 : List Nat := [1, 3, 1, 1, 2, 4, 1, 7]
def baseStart_331781 : Nat := 118140960795 + 331781 * 2 ^ 59
def prefixEnd_331781 : Nat := 4983230072969 + 3 ^ 40 * 331781 * 2
def baseEnd_331781 : Nat := 50477962971695300447903

theorem tailTrace_331781 : CollatzResearch.WordTrace tailWord_331781 prefixEnd_331781 50477962971695300447903 := by
  unfold tailWord_331781
  simp only [CollatzResearch.WordTrace]
  refine ⟨12101047211021575528683197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8067364807347717019122131 12101047211021575528683197)
  ·
    refine ⟨4537892704133090823256199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12101047211021575528683197 4537892704133090823256199)
    ·
      refine ⟨6806839056199636234884299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4537892704133090823256199 6806839056199636234884299)
      ·
        refine ⟨10210258584299454352326449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6806839056199636234884299 10210258584299454352326449)
        ·
          refine ⟨7657693938224590764244837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10210258584299454352326449 7657693938224590764244837)
          ·
            refine ⟨1435817613417110768295907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7657693938224590764244837 1435817613417110768295907)
            ·
              refine ⟨2153726420125666152443861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435817613417110768295907 2153726420125666152443861)
              ·
                refine ⟨50477962971695300447903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2153726420125666152443861 50477962971695300447903)
                ·
                  rfl

theorem cell20_331781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_331781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331781 prefixEnd_331781 := by exact prefixLift 331781
  have htrace : WordTrace (prefixWord ++ tailWord_331781) baseStart_331781 baseEnd_331781 := by
    simpa [prefixWord, tailWord_331781, baseEnd_331781] using wordTrace_append hprefix tailTrace_331781
  have hstable : (prefixWord ++ tailWord_331781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331781).length < 2 ^ (prefixWord ++ tailWord_331781).sum := by decide
  have hdescent : baseEnd_331781 < baseStart_331781 := by decide
  rcases family_descends (prefixWord ++ tailWord_331781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331815 : List Nat := [1, 1, 7, 1, 3, 7]
def baseStart_331815 : Nat := 118140960795 + 331815 * 2 ^ 59
def prefixEnd_331815 : Nat := 4983230072969 + 3 ^ 40 * 331815 * 2
def baseEnd_331815 : Nat := 5609237312649366452231

theorem tailTrace_331815 : CollatzResearch.WordTrace tailWord_331815 prefixEnd_331815 5609237312649366452231 := by
  unfold tailWord_331815
  simp only [CollatzResearch.WordTrace]
  refine ⟨12102287292898399335420899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8068191528598932890280599 12102287292898399335420899)
  ·
    refine ⟨18153430939347599003131349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12102287292898399335420899 18153430939347599003131349)
    ·
      refine ⟨425471037640959351635891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18153430939347599003131349 425471037640959351635891)
      ·
        refine ⟨638206556461439027453837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425471037640959351635891 638206556461439027453837)
        ·
          refine ⟨239327458673039635295189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 638206556461439027453837 239327458673039635295189)
          ·
            refine ⟨5609237312649366452231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 239327458673039635295189 5609237312649366452231)
            ·
              rfl

theorem cell20_331815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 7].length) (baseStart_331815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331815 prefixEnd_331815 := by exact prefixLift 331815
  have htrace : WordTrace (prefixWord ++ tailWord_331815) baseStart_331815 baseEnd_331815 := by
    simpa [prefixWord, tailWord_331815, baseEnd_331815] using wordTrace_append hprefix tailTrace_331815
  have hstable : (prefixWord ++ tailWord_331815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331815).length < 2 ^ (prefixWord ++ tailWord_331815).sum := by decide
  have hdescent : baseEnd_331815 < baseStart_331815 := by decide
  rcases family_descends (prefixWord ++ tailWord_331815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331822 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_331822 : Nat := 118140960795 + 331822 * 2 ^ 59
def prefixEnd_331822 : Nat := 4983230072969 + 3 ^ 40 * 331822 * 2
def baseEnd_331822 : Nat := 151452602432271980976875

theorem tailTrace_331822 : CollatzResearch.WordTrace tailWord_331822 prefixEnd_331822 151452602432271980976875 := by
  unfold tailWord_331822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512817825484129941365715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8068361735915359687283813 1512817825484129941365715)
  ·
    refine ⟨2269226738226194912048573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512817825484129941365715 2269226738226194912048573)
    ·
      refine ⟨850960026834823092018215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2269226738226194912048573 850960026834823092018215)
      ·
        refine ⟨1276440040252234638027323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850960026834823092018215 1276440040252234638027323)
        ·
          refine ⟨1914660060378351957040985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1276440040252234638027323 1914660060378351957040985)
          ·
            refine ⟨1435995045283763967780739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1914660060378351957040985 1435995045283763967780739)
            ·
              refine ⟨2153992567925645951671109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435995045283763967780739 2153992567925645951671109)
              ·
                refine ⟨403873606486058615938333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2153992567925645951671109 403873606486058615938333)
                ·
                  refine ⟨151452602432271980976875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 403873606486058615938333 151452602432271980976875)
                  ·
                    rfl

theorem cell20_331822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_331822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331822 prefixEnd_331822 := by exact prefixLift 331822
  have htrace : WordTrace (prefixWord ++ tailWord_331822) baseStart_331822 baseEnd_331822 := by
    simpa [prefixWord, tailWord_331822, baseEnd_331822] using wordTrace_append hprefix tailTrace_331822
  have hstable : (prefixWord ++ tailWord_331822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331822).length < 2 ^ (prefixWord ++ tailWord_331822).sum := by decide
  have hdescent : baseEnd_331822 < baseStart_331822 := by decide
  rcases family_descends (prefixWord ++ tailWord_331822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331825 : List Nat := [1, 2, 2, 3, 1, 5, 2, 2, 2]
def baseStart_331825 : Nat := 118140960795 + 331825 * 2 ^ 59
def prefixEnd_331825 : Nat := 4983230072969 + 3 ^ 40 * 331825 * 2
def baseEnd_331825 : Nat := 151453971714017303876863

theorem tailTrace_331825 : CollatzResearch.WordTrace tailWord_331825 prefixEnd_331825 151453971714017303876863 := by
  unfold tailWord_331825
  simp only [CollatzResearch.WordTrace]
  refine ⟨12102652022862171043284929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8068434681908114028856619 12102652022862171043284929)
  ·
    refine ⟨9076989017146628282463697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12102652022862171043284929 9076989017146628282463697)
    ·
      refine ⟨6807741762859971211847773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9076989017146628282463697 6807741762859971211847773)
      ·
        refine ⟨2552903161072489204442915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6807741762859971211847773 2552903161072489204442915)
        ·
          refine ⟨3829354741608733806664373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552903161072489204442915 3829354741608733806664373)
          ·
            refine ⟨359002007025818794374785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3829354741608733806664373 359002007025818794374785)
            ·
              refine ⟨269251505269364095781089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359002007025818794374785 269251505269364095781089)
              ·
                refine ⟨201938628952023071835817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269251505269364095781089 201938628952023071835817)
                ·
                  refine ⟨151453971714017303876863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201938628952023071835817 151453971714017303876863)
                  ·
                    rfl

theorem cell20_331825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_331825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331825 prefixEnd_331825 := by exact prefixLift 331825
  have htrace : WordTrace (prefixWord ++ tailWord_331825) baseStart_331825 baseEnd_331825 := by
    simpa [prefixWord, tailWord_331825, baseEnd_331825] using wordTrace_append hprefix tailTrace_331825
  have hstable : (prefixWord ++ tailWord_331825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331825).length < 2 ^ (prefixWord ++ tailWord_331825).sum := by decide
  have hdescent : baseEnd_331825 < baseStart_331825 := by decide
  rcases family_descends (prefixWord ++ tailWord_331825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331846 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_331846 : Nat := 118140960795 + 331846 * 2 ^ 59
def prefixEnd_331846 : Nat := 4983230072969 + 3 ^ 40 * 331846 * 2
def baseEnd_331846 : Nat := 151463556686234564176777

theorem tailTrace_331846 : CollatzResearch.WordTrace tailWord_331846 prefixEnd_331846 151463556686234564176777 := by
  unfold tailWord_331846
  simp only [CollatzResearch.WordTrace]
  refine ⟨378231811118315363431231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8068945303857394419866261 378231811118315363431231)
  ·
    refine ⟨567347716677473045146847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 378231811118315363431231 567347716677473045146847)
    ·
      refine ⟨851021575016209567720271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567347716677473045146847 851021575016209567720271)
      ·
        refine ⟨1276532362524314351580407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851021575016209567720271 1276532362524314351580407)
        ·
          refine ⟨1914798543786471527370611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1276532362524314351580407 1914798543786471527370611)
          ·
            refine ⟨2872197815679707291055917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914798543786471527370611 2872197815679707291055917)
            ·
              refine ⟨1077074180879890234145969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2872197815679707291055917 1077074180879890234145969)
              ·
                refine ⟨807805635659917675609477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077074180879890234145969 807805635659917675609477)
                ·
                  refine ⟨151463556686234564176777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807805635659917675609477 151463556686234564176777)
                  ·
                    rfl

theorem cell20_331846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_331846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331846 prefixEnd_331846 := by exact prefixLift 331846
  have htrace : WordTrace (prefixWord ++ tailWord_331846) baseStart_331846 baseEnd_331846 := by
    simpa [prefixWord, tailWord_331846, baseEnd_331846] using wordTrace_append hprefix tailTrace_331846
  have hstable : (prefixWord ++ tailWord_331846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331846).length < 2 ^ (prefixWord ++ tailWord_331846).sum := by decide
  have hdescent : baseEnd_331846 < baseStart_331846 := by decide
  rcases family_descends (prefixWord ++ tailWord_331846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331853 : List Nat := [1, 6, 1, 1, 1, 1, 5, 4]
def baseStart_331853 : Nat := 118140960795 + 331853 * 2 ^ 59
def prefixEnd_331853 : Nat := 4983230072969 + 3 ^ 40 * 331853 * 2
def baseEnd_331853 : Nat := 50488917225657883647805

theorem tailTrace_331853 : CollatzResearch.WordTrace tailWord_331853 prefixEnd_331853 50488917225657883647805 := by
  unfold tailWord_331853
  simp only [CollatzResearch.WordTrace]
  refine ⟨12103673266760731825304213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8069115511173821216869475 12103673266760731825304213)
  ·
    refine ⟨567359684379409304311135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12103673266760731825304213 567359684379409304311135)
    ·
      refine ⟨851039526569113956466703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567359684379409304311135 851039526569113956466703)
      ·
        refine ⟨1276559289853670934700055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851039526569113956466703 1276559289853670934700055)
        ·
          refine ⟨1914838934780506402050083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1276559289853670934700055 1914838934780506402050083)
          ·
            refine ⟨2872258402170759603075125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914838934780506402050083 2872258402170759603075125)
            ·
              refine ⟨269274225203508712788293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2872258402170759603075125 269274225203508712788293)
              ·
                refine ⟨50488917225657883647805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269274225203508712788293 50488917225657883647805)
                ·
                  rfl

theorem cell20_331853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 4].length) (baseStart_331853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331853 prefixEnd_331853 := by exact prefixLift 331853
  have htrace : WordTrace (prefixWord ++ tailWord_331853) baseStart_331853 baseEnd_331853 := by
    simpa [prefixWord, tailWord_331853, baseEnd_331853] using wordTrace_append hprefix tailTrace_331853
  have hstable : (prefixWord ++ tailWord_331853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331853).length < 2 ^ (prefixWord ++ tailWord_331853).sum := by decide
  have hdescent : baseEnd_331853 < baseStart_331853 := by decide
  rcases family_descends (prefixWord ++ tailWord_331853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331870 : List Nat := [4, 4, 1, 1, 2, 1, 7]
def baseStart_331870 : Nat := 118140960795 + 331870 * 2 ^ 59
def prefixEnd_331870 : Nat := 4983230072969 + 3 ^ 40 * 331870 * 2
def baseEnd_331870 : Nat := 16830501215577460819631

theorem tailTrace_331870 : CollatzResearch.WordTrace tailWord_331870 prefixEnd_331870 16830501215577460819631 := by
  unfold tailWord_331870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513036663462392966084133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8069528871799429152448709 1513036663462392966084133)
  ·
    refine ⟨283694374399198681140775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1513036663462392966084133 283694374399198681140775)
    ·
      refine ⟨425541561598798021711163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283694374399198681140775 425541561598798021711163)
      ·
        refine ⟨638312342398197032566745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425541561598798021711163 638312342398197032566745)
        ·
          refine ⟨478734256798647774425059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638312342398197032566745 478734256798647774425059)
          ·
            refine ⟨718101385197971661637589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478734256798647774425059 718101385197971661637589)
            ·
              refine ⟨16830501215577460819631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 718101385197971661637589 16830501215577460819631)
              ·
                rfl

theorem cell20_331870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 7].length) (baseStart_331870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331870 prefixEnd_331870 := by exact prefixLift 331870
  have htrace : WordTrace (prefixWord ++ tailWord_331870) baseStart_331870 baseEnd_331870 := by
    simpa [prefixWord, tailWord_331870, baseEnd_331870] using wordTrace_append hprefix tailTrace_331870
  have hstable : (prefixWord ++ tailWord_331870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331870).length < 2 ^ (prefixWord ++ tailWord_331870).sum := by decide
  have hdescent : baseEnd_331870 < baseStart_331870 := by decide
  rcases family_descends (prefixWord ++ tailWord_331870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331888 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_331888 : Nat := 118140960795 + 331888 * 2 ^ 59
def prefixEnd_331888 : Nat := 4983230072969 + 3 ^ 40 * 331888 * 2
def baseEnd_331888 : Nat := 151482726630669084776605

theorem tailTrace_331888 : CollatzResearch.WordTrace tailWord_331888 prefixEnd_331888 151482726630669084776605 := by
  unfold tailWord_331888
  simp only [CollatzResearch.WordTrace]
  refine ⟨6052474910816966401414159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8069966547755955201885545 6052474910816966401414159)
  ·
    refine ⟨9078712366225449602121239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6052474910816966401414159 9078712366225449602121239)
    ·
      refine ⟨13618068549338174403181859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9078712366225449602121239 13618068549338174403181859)
      ·
        refine ⟨20427102824007261604772789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13618068549338174403181859 20427102824007261604772789)
        ·
          refine ⟨1915040889750680775447449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20427102824007261604772789 1915040889750680775447449)
          ·
            refine ⟨1436280667313010581585587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1915040889750680775447449 1436280667313010581585587)
            ·
              refine ⟨2154421000969515872378381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436280667313010581585587 2154421000969515872378381)
              ·
                refine ⟨807907875363568452141893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2154421000969515872378381 807907875363568452141893)
                ·
                  refine ⟨151482726630669084776605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 807907875363568452141893 151482726630669084776605)
                  ·
                    rfl

theorem cell20_331888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_331888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331888 prefixEnd_331888 := by exact prefixLift 331888
  have htrace : WordTrace (prefixWord ++ tailWord_331888) baseStart_331888 baseEnd_331888 := by
    simpa [prefixWord, tailWord_331888, baseEnd_331888] using wordTrace_append hprefix tailTrace_331888
  have hstable : (prefixWord ++ tailWord_331888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331888).length < 2 ^ (prefixWord ++ tailWord_331888).sum := by decide
  have hdescent : baseEnd_331888 < baseStart_331888 := by decide
  rcases family_descends (prefixWord ++ tailWord_331888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331912 : List Nat := [2, 1, 3, 4, 1, 2, 1, 6]
def baseStart_331912 : Nat := 118140960795 + 331912 * 2 ^ 59
def prefixEnd_331912 : Nat := 4983230072969 + 3 ^ 40 * 331912 * 2
def baseEnd_331912 : Nat := 50497893628210555992169

theorem tailTrace_331912 : CollatzResearch.WordTrace tailWord_331912 prefixEnd_331912 50497893628210555992169 := by
  unfold tailWord_331912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6052912586773492450850995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8070550115697989934467993 6052912586773492450850995)
  ·
    refine ⟨9079368880160238676276493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6052912586773492450850995 9079368880160238676276493)
    ·
      refine ⟨3404763330060089503603685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9079368880160238676276493 3404763330060089503603685)
      ·
        refine ⟨638393124386266781925691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3404763330060089503603685 638393124386266781925691)
        ·
          refine ⟨957589686579400172888537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638393124386266781925691 957589686579400172888537)
          ·
            refine ⟨718192264934550129666403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957589686579400172888537 718192264934550129666403)
            ·
              refine ⟨1077288397401825194499605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718192264934550129666403 1077288397401825194499605)
              ·
                refine ⟨50497893628210555992169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1077288397401825194499605 50497893628210555992169)
                ·
                  rfl

theorem cell20_331912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_331912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331912 prefixEnd_331912 := by exact prefixLift 331912
  have htrace : WordTrace (prefixWord ++ tailWord_331912) baseStart_331912 baseEnd_331912 := by
    simpa [prefixWord, tailWord_331912, baseEnd_331912] using wordTrace_append hprefix tailTrace_331912
  have hstable : (prefixWord ++ tailWord_331912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331912).length < 2 ^ (prefixWord ++ tailWord_331912).sum := by decide
  have hdescent : baseEnd_331912 < baseStart_331912 := by decide
  rcases family_descends (prefixWord ++ tailWord_331912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331918 : List Nat := [4, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_331918 : Nat := 118140960795 + 331918 * 2 ^ 59
def prefixEnd_331918 : Nat := 4983230072969 + 3 ^ 40 * 331918 * 2
def baseEnd_331918 : Nat := 151496419448122313776483

theorem tailTrace_331918 : CollatzResearch.WordTrace tailWord_331918 prefixEnd_331918 151496419448122313776483 := by
  unfold tailWord_331918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513255501440655990802551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8070696007683498617613605 1513255501440655990802551)
  ·
    refine ⟨2269883252160983986203827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1513255501440655990802551 2269883252160983986203827)
    ·
      refine ⟨3404824878241475979305741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269883252160983986203827 3404824878241475979305741)
      ·
        refine ⟨1276809329340553492239653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3404824878241475979305741 1276809329340553492239653)
        ·
          refine ⟨239401749251353779794935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1276809329340553492239653 239401749251353779794935)
          ·
            refine ⟨359102623877030669692403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239401749251353779794935 359102623877030669692403)
            ·
              refine ⟨538653935815546004538605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359102623877030669692403 538653935815546004538605)
              ·
                refine ⟨201995225930829751701977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 538653935815546004538605 201995225930829751701977)
                ·
                  refine ⟨151496419448122313776483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201995225930829751701977 151496419448122313776483)
                  ·
                    rfl

theorem cell20_331918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_331918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331918 prefixEnd_331918 := by exact prefixLift 331918
  have htrace : WordTrace (prefixWord ++ tailWord_331918) baseStart_331918 baseEnd_331918 := by
    simpa [prefixWord, tailWord_331918, baseEnd_331918] using wordTrace_append hprefix tailTrace_331918
  have hstable : (prefixWord ++ tailWord_331918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331918).length < 2 ^ (prefixWord ++ tailWord_331918).sum := by decide
  have hdescent : baseEnd_331918 < baseStart_331918 := by decide
  rcases family_descends (prefixWord ++ tailWord_331918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_331933 : List Nat := [1, 4, 2, 1, 1, 3, 8]
def baseStart_331933 : Nat := 118140960795 + 331933 * 2 ^ 59
def prefixEnd_331933 : Nat := 4983230072969 + 3 ^ 40 * 331933 * 2
def baseEnd_331933 : Nat := 16833696206316547586269

theorem tailTrace_331933 : CollatzResearch.WordTrace tailWord_331933 prefixEnd_331933 16833696206316547586269 := by
  unfold tailWord_331933
  simp only [CollatzResearch.WordTrace]
  refine ⟨12106591106470905488216453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8071060737647270325477635 12106591106470905488216453)
  ·
    refine ⟨2269985832463294779040585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12106591106470905488216453 2269985832463294779040585)
    ·
      refine ⟨1702489374347471084280439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2269985832463294779040585 1702489374347471084280439)
      ·
        refine ⟨2553734061521206626420659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702489374347471084280439 2553734061521206626420659)
        ·
          refine ⟨3830601092281809939630989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553734061521206626420659 3830601092281809939630989)
          ·
            refine ⟨1436475409605678727361621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3830601092281809939630989 1436475409605678727361621)
            ·
              refine ⟨16833696206316547586269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1436475409605678727361621 16833696206316547586269)
              ·
                rfl

theorem cell20_331933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 8].length) (baseStart_331933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_331933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_331933 prefixEnd_331933 := by exact prefixLift 331933
  have htrace : WordTrace (prefixWord ++ tailWord_331933) baseStart_331933 baseEnd_331933 := by
    simpa [prefixWord, tailWord_331933, baseEnd_331933] using wordTrace_append hprefix tailTrace_331933
  have hstable : (prefixWord ++ tailWord_331933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_331933).length < 2 ^ (prefixWord ++ tailWord_331933).sum := by decide
  have hdescent : baseEnd_331933 < baseStart_331933 := by decide
  rcases family_descends (prefixWord ++ tailWord_331933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332026 : List Nat := [3, 1, 1, 1, 1, 6, 3, 4]
def baseStart_332026 : Nat := 118140960795 + 332026 * 2 ^ 59
def prefixEnd_332026 : Nat := 4983230072969 + 3 ^ 40 * 332026 * 2
def baseEnd_332026 : Nat := 50515237863651312725347

theorem tailTrace_332026 : CollatzResearch.WordTrace tailWord_332026 prefixEnd_332026 50515237863651312725347 := by
  unfold tailWord_332026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3027495773783495592837983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8073322063422654914234621 3027495773783495592837983)
  ·
    refine ⟨4541243660675243389256975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3027495773783495592837983 4541243660675243389256975)
    ·
      refine ⟨6811865491012865083885463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4541243660675243389256975 6811865491012865083885463)
      ·
        refine ⟨10217798236519297625828195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6811865491012865083885463 10217798236519297625828195)
        ·
          refine ⟨15326697354778946438742293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10217798236519297625828195 15326697354778946438742293)
          ·
            refine ⟨718438938505263114316045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15326697354778946438742293 718438938505263114316045)
            ·
              refine ⟨269414601939473667868517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 718438938505263114316045 269414601939473667868517)
              ·
                refine ⟨50515237863651312725347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269414601939473667868517 50515237863651312725347)
                ·
                  rfl

theorem cell20_332026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_332026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332026 prefixEnd_332026 := by exact prefixLift 332026
  have htrace : WordTrace (prefixWord ++ tailWord_332026) baseStart_332026 baseEnd_332026 := by
    simpa [prefixWord, tailWord_332026, baseEnd_332026] using wordTrace_append hprefix tailTrace_332026
  have hstable : (prefixWord ++ tailWord_332026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332026).length < 2 ^ (prefixWord ++ tailWord_332026).sum := by decide
  have hdescent : baseEnd_332026 < baseStart_332026 := by decide
  rcases family_descends (prefixWord ++ tailWord_332026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332077 : List Nat := [1, 5, 3, 1, 3, 1, 2, 4]
def baseStart_332077 : Nat := 118140960795 + 332077 * 2 ^ 59
def prefixEnd_332077 : Nat := 4983230072969 + 3 ^ 40 * 332077 * 2
def baseEnd_332077 : Nat := 50522997126874809158611

theorem tailTrace_332077 : CollatzResearch.WordTrace tailWord_332077 prefixEnd_332077 50522997126874809158611 := by
  unfold tailWord_332077
  simp only [CollatzResearch.WordTrace]
  refine ⟨12111843217949218081458485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8074562145299478720972323 12111843217949218081458485)
  ·
    refine ⟨1135485301682739195136733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12111843217949218081458485 1135485301682739195136733)
    ·
      refine ⟨425806988131027198176275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1135485301682739195136733 425806988131027198176275)
      ·
        refine ⟨638710482196540797264413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425806988131027198176275 638710482196540797264413)
        ·
          refine ⟨239516430823702798974155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 638710482196540797264413 239516430823702798974155)
          ·
            refine ⟨359274646235554198461233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239516430823702798974155 359274646235554198461233)
            ·
              refine ⟨269455984676665648845925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359274646235554198461233 269455984676665648845925)
              ·
                refine ⟨50522997126874809158611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269455984676665648845925 50522997126874809158611)
                ·
                  rfl

theorem cell20_332077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 4].length) (baseStart_332077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332077 prefixEnd_332077 := by exact prefixLift 332077
  have htrace : WordTrace (prefixWord ++ tailWord_332077) baseStart_332077 baseEnd_332077 := by
    simpa [prefixWord, tailWord_332077, baseEnd_332077] using wordTrace_append hprefix tailTrace_332077
  have hstable : (prefixWord ++ tailWord_332077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332077).length < 2 ^ (prefixWord ++ tailWord_332077).sum := by decide
  have hdescent : baseEnd_332077 < baseStart_332077 := by decide
  rcases family_descends (prefixWord ++ tailWord_332077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332081 : List Nat := [1, 2, 2, 3, 4, 2, 2, 4]
def baseStart_332081 : Nat := 118140960795 + 332081 * 2 ^ 59
def prefixEnd_332081 : Nat := 4983230072969 + 3 ^ 40 * 332081 * 2
def baseEnd_332081 : Nat := 50523605696539397114161

theorem tailTrace_332081 : CollatzResearch.WordTrace tailWord_332081 prefixEnd_332081 50523605696539397114161 := by
  unfold tailWord_332081
  simp only [CollatzResearch.WordTrace]
  refine ⟨12111989109934726764604097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8074659406623151176402731 12111989109934726764604097)
  ·
    refine ⟨9083991832451045073453073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12111989109934726764604097 9083991832451045073453073)
    ·
      refine ⟨6812993874338283805089805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9083991832451045073453073 6812993874338283805089805)
      ·
        refine ⟨2554872702876856426908677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6812993874338283805089805 2554872702876856426908677)
        ·
          refine ⟨479038631789410580045377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2554872702876856426908677 479038631789410580045377)
          ·
            refine ⟨359278973842057935034033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479038631789410580045377 359278973842057935034033)
            ·
              refine ⟨269459230381543451275525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359278973842057935034033 269459230381543451275525)
              ·
                refine ⟨50523605696539397114161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269459230381543451275525 50523605696539397114161)
                ·
                  rfl

theorem cell20_332081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 4].length) (baseStart_332081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332081 prefixEnd_332081 := by exact prefixLift 332081
  have htrace : WordTrace (prefixWord ++ tailWord_332081) baseStart_332081 baseEnd_332081 := by
    simpa [prefixWord, tailWord_332081, baseEnd_332081] using wordTrace_append hprefix tailTrace_332081
  have hstable : (prefixWord ++ tailWord_332081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332081).length < 2 ^ (prefixWord ++ tailWord_332081).sum := by decide
  have hdescent : baseEnd_332081 < baseStart_332081 := by decide
  rcases family_descends (prefixWord ++ tailWord_332081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332085 : List Nat := [1, 3, 3, 1, 2, 1, 3, 6]
def baseStart_332085 : Nat := 118140960795 + 332085 * 2 ^ 59
def prefixEnd_332085 : Nat := 4983230072969 + 3 ^ 40 * 332085 * 2
def baseEnd_332085 : Nat := 50524214266203985069711

theorem tailTrace_332085 : CollatzResearch.WordTrace tailWord_332085 prefixEnd_332085 50524214266203985069711 := by
  unfold tailWord_332085
  simp only [CollatzResearch.WordTrace]
  refine ⟨12112135001920235447749709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8074756667946823631833139 12112135001920235447749709)
  ·
    refine ⟨4542050625720088292906141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12112135001920235447749709 4542050625720088292906141)
    ·
      refine ⟨1703268984645033109839803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4542050625720088292906141 1703268984645033109839803)
      ·
        refine ⟨2554903476967549664759705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703268984645033109839803 2554903476967549664759705)
        ·
          refine ⟨1916177607725662248569779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2554903476967549664759705 1916177607725662248569779)
          ·
            refine ⟨2874266411588493372854669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916177607725662248569779 2874266411588493372854669)
            ·
              refine ⟨1077849904345685014820501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2874266411588493372854669 1077849904345685014820501)
              ·
                refine ⟨50524214266203985069711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1077849904345685014820501 50524214266203985069711)
                ·
                  rfl

theorem cell20_332085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_332085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332085 prefixEnd_332085 := by exact prefixLift 332085
  have htrace : WordTrace (prefixWord ++ tailWord_332085) baseStart_332085 baseEnd_332085 := by
    simpa [prefixWord, tailWord_332085, baseEnd_332085] using wordTrace_append hprefix tailTrace_332085
  have hstable : (prefixWord ++ tailWord_332085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332085).length < 2 ^ (prefixWord ++ tailWord_332085).sum := by decide
  have hdescent : baseEnd_332085 < baseStart_332085 := by decide
  rcases family_descends (prefixWord ++ tailWord_332085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332092 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_332092 : Nat := 118140960795 + 332092 * 2 ^ 59
def prefixEnd_332092 : Nat := 4983230072969 + 3 ^ 40 * 332092 * 2
def baseEnd_332092 : Nat := 151575837789351041975771

theorem tailTrace_332092 : CollatzResearch.WordTrace tailWord_332092 prefixEnd_332092 151575837789351041975771 := by
  unfold tailWord_332092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056195156447437821627265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8074926875263250428836353 6056195156447437821627265)
  ·
    refine ⟨4542146367335578366220449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6056195156447437821627265 4542146367335578366220449)
    ·
      refine ⟨3406609775501683774665337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4542146367335578366220449 3406609775501683774665337)
      ·
        refine ⟨2554957331626262830999003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3406609775501683774665337 2554957331626262830999003)
        ·
          refine ⟨3832435997439394246498505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554957331626262830999003 3832435997439394246498505)
          ·
            refine ⟨2874326998079545684873879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3832435997439394246498505 2874326998079545684873879)
            ·
              refine ⟨4311490497119318527310819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2874326998079545684873879 4311490497119318527310819)
              ·
                refine ⟨6467235745678977790966229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4311490497119318527310819 6467235745678977790966229)
                ·
                  refine ⟨151575837789351041975771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6467235745678977790966229 151575837789351041975771)
                  ·
                    rfl

theorem cell20_332092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_332092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332092 prefixEnd_332092 := by exact prefixLift 332092
  have htrace : WordTrace (prefixWord ++ tailWord_332092) baseStart_332092 baseEnd_332092 := by
    simpa [prefixWord, tailWord_332092, baseEnd_332092] using wordTrace_append hprefix tailTrace_332092
  have hstable : (prefixWord ++ tailWord_332092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332092).length < 2 ^ (prefixWord ++ tailWord_332092).sum := by decide
  have hdescent : baseEnd_332092 < baseStart_332092 := by decide
  rcases family_descends (prefixWord ++ tailWord_332092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332099 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_332099 : Nat := 118140960795 + 332099 * 2 ^ 59
def prefixEnd_332099 : Nat := 4983230072969 + 3 ^ 40 * 332099 * 2
def baseEnd_332099 : Nat := 151579032780090128742409

theorem tailTrace_332099 : CollatzResearch.WordTrace tailWord_332099 prefixEnd_332099 151579032780090128742409 := by
  unfold tailWord_332099
  simp only [CollatzResearch.WordTrace]
  refine ⟨12112645623869515838759351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8075097082579677225839567 12112645623869515838759351)
  ·
    refine ⟨18168968435804273758139027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12112645623869515838759351 18168968435804273758139027)
    ·
      refine ⟨27253452653706410637208541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18168968435804273758139027 27253452653706410637208541)
      ·
        refine ⟨10220044745139903988953203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27253452653706410637208541 10220044745139903988953203)
        ·
          refine ⟨15330067117709855983429805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220044745139903988953203 15330067117709855983429805)
          ·
            refine ⟨5748775169141195993786177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15330067117709855983429805 5748775169141195993786177)
            ·
              refine ⟨4311581376855896995339633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5748775169141195993786177 4311581376855896995339633)
              ·
                refine ⟨3233686032641922746504725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4311581376855896995339633 3233686032641922746504725)
                ·
                  refine ⟨151579032780090128742409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3233686032641922746504725 151579032780090128742409)
                  ·
                    rfl

theorem cell20_332099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_332099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332099 prefixEnd_332099 := by exact prefixLift 332099
  have htrace : WordTrace (prefixWord ++ tailWord_332099) baseStart_332099 baseEnd_332099 := by
    simpa [prefixWord, tailWord_332099, baseEnd_332099] using wordTrace_append hprefix tailTrace_332099
  have hstable : (prefixWord ++ tailWord_332099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332099).length < 2 ^ (prefixWord ++ tailWord_332099).sum := by decide
  have hdescent : baseEnd_332099 < baseStart_332099 := by decide
  rcases family_descends (prefixWord ++ tailWord_332099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332112 : List Nat := [2, 1, 1, 1, 1, 7, 3, 2, 2]
def baseStart_332112 : Nat := 118140960795 + 332112 * 2 ^ 59
def prefixEnd_332112 : Nat := 4983230072969 + 3 ^ 40 * 332112 * 2
def baseEnd_332112 : Nat := 151584966334319861309023

theorem tailTrace_332112 : CollatzResearch.WordTrace tailWord_332112 prefixEnd_332112 151584966334319861309023 := by
  unfold tailWord_332112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056559886411209529491295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8075413181881612705988393 6056559886411209529491295)
  ·
    refine ⟨9084839829616814294236943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6056559886411209529491295 9084839829616814294236943)
    ·
      refine ⟨13627259744425221441355415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9084839829616814294236943 13627259744425221441355415)
      ·
        refine ⟨20440889616637832162033123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13627259744425221441355415 20440889616637832162033123)
        ·
          refine ⟨30661334424956748243049685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20440889616637832162033123 30661334424956748243049685)
          ·
            refine ⟨718625025584923786946477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 30661334424956748243049685 718625025584923786946477)
            ·
              refine ⟨269484384594346420104929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 718625025584923786946477 269484384594346420104929)
              ·
                refine ⟨202113288445759815078697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269484384594346420104929 202113288445759815078697)
                ·
                  refine ⟨151584966334319861309023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202113288445759815078697 151584966334319861309023)
                  ·
                    rfl

theorem cell20_332112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_332112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332112 prefixEnd_332112 := by exact prefixLift 332112
  have htrace : WordTrace (prefixWord ++ tailWord_332112) baseStart_332112 baseEnd_332112 := by
    simpa [prefixWord, tailWord_332112, baseEnd_332112] using wordTrace_append hprefix tailTrace_332112
  have hstable : (prefixWord ++ tailWord_332112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332112).length < 2 ^ (prefixWord ++ tailWord_332112).sum := by decide
  have hdescent : baseEnd_332112 < baseStart_332112 := by decide
  rcases family_descends (prefixWord ++ tailWord_332112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332137 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_332137 : Nat := 118140960795 + 332137 * 2 ^ 59
def prefixEnd_332137 : Nat := 4983230072969 + 3 ^ 40 * 332137 * 2
def baseEnd_332137 : Nat := 151596377015530885475587

theorem tailTrace_332137 : CollatzResearch.WordTrace tailWord_332137 prefixEnd_332137 151596377015530885475587 := by
  unfold tailWord_332137
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114031597731848328642665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8076021065154565552428443 12114031597731848328642665)
  ·
    refine ⟨9085523698298886246481999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12114031597731848328642665 9085523698298886246481999)
    ·
      refine ⟨13628285547448329369722999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9085523698298886246481999 13628285547448329369722999)
      ·
        refine ⟨20442428321172494054584499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13628285547448329369722999 20442428321172494054584499)
        ·
          refine ⟨30663642481758741081876749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20442428321172494054584499 30663642481758741081876749)
          ·
            refine ⟨11498865930659527905703781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30663642481758741081876749 11498865930659527905703781)
            ·
              refine ⟨2156037361998661482319459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11498865930659527905703781 2156037361998661482319459)
              ·
                refine ⟨3234056042997992223479189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156037361998661482319459 3234056042997992223479189)
                ·
                  refine ⟨151596377015530885475587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3234056042997992223479189 151596377015530885475587)
                  ·
                    rfl

theorem cell20_332137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_332137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332137 prefixEnd_332137 := by exact prefixLift 332137
  have htrace : WordTrace (prefixWord ++ tailWord_332137) baseStart_332137 baseEnd_332137 := by
    simpa [prefixWord, tailWord_332137, baseEnd_332137] using wordTrace_append hprefix tailTrace_332137
  have hstable : (prefixWord ++ tailWord_332137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332137).length < 2 ^ (prefixWord ++ tailWord_332137).sum := by decide
  have hdescent : baseEnd_332137 < baseStart_332137 := by decide
  rcases family_descends (prefixWord ++ tailWord_332137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332161 : List Nat := [1, 2, 4, 3, 1, 9]
def baseStart_332161 : Nat := 118140960795 + 332161 * 2 ^ 59
def prefixEnd_332161 : Nat := 4983230072969 + 3 ^ 40 * 332161 * 2
def baseEnd_332161 : Nat := 5615086343314572913907

theorem tailTrace_332161 : CollatzResearch.WordTrace tailWord_332161 prefixEnd_332161 5615086343314572913907 := by
  unfold tailWord_332161
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114906949644900427516337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8076604633096600285010891 12114906949644900427516337)
  ·
    refine ⟨9086180212233675320637253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12114906949644900427516337 9086180212233675320637253)
    ·
      refine ⟨1703658789793814122619485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9086180212233675320637253 1703658789793814122619485)
      ·
        refine ⟨638872046172680295982307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1703658789793814122619485 638872046172680295982307)
        ·
          refine ⟨958308069259020443973461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638872046172680295982307 958308069259020443973461)
          ·
            refine ⟨5615086343314572913907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 958308069259020443973461 5615086343314572913907)
            ·
              rfl

theorem cell20_332161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 9].length) (baseStart_332161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332161 prefixEnd_332161 := by exact prefixLift 332161
  have htrace : WordTrace (prefixWord ++ tailWord_332161) baseStart_332161 baseEnd_332161 := by
    simpa [prefixWord, tailWord_332161, baseEnd_332161] using wordTrace_append hprefix tailTrace_332161
  have hstable : (prefixWord ++ tailWord_332161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332161).length < 2 ^ (prefixWord ++ tailWord_332161).sum := by decide
  have hdescent : baseEnd_332161 < baseStart_332161 := by decide
  rcases family_descends (prefixWord ++ tailWord_332161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332171 : List Nat := [1, 1, 1, 1, 4, 5, 1, 4, 2]
def baseStart_332171 : Nat := 118140960795 + 332171 * 2 ^ 59
def prefixEnd_332171 : Nat := 4983230072969 + 3 ^ 40 * 332171 * 2
def baseEnd_332171 : Nat := 151611895541977878342115

theorem tailTrace_332171 : CollatzResearch.WordTrace tailWord_332171 prefixEnd_332171 151611895541977878342115 := by
  unfold tailWord_332171
  simp only [CollatzResearch.WordTrace]
  refine ⟨12115271679608672135380367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8076847786405781423586911 12115271679608672135380367)
  ·
    refine ⟨18172907519413008203070551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12115271679608672135380367 18172907519413008203070551)
    ·
      refine ⟨27259361279119512304605827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18172907519413008203070551 27259361279119512304605827)
      ·
        refine ⟨40889041918679268456908741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27259361279119512304605827 40889041918679268456908741)
        ·
          refine ⟨7666695359752362835670389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40889041918679268456908741 7666695359752362835670389)
          ·
            refine ⟨718752689976784015844099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7666695359752362835670389 718752689976784015844099)
            ·
              refine ⟨1078129034965176023766149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718752689976784015844099 1078129034965176023766149)
              ·
                refine ⟨202149194055970504456153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1078129034965176023766149 202149194055970504456153)
                ·
                  refine ⟨151611895541977878342115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202149194055970504456153 151611895541977878342115)
                  ·
                    rfl

theorem cell20_332171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 2].length) (baseStart_332171 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332171 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332171 prefixEnd_332171 := by exact prefixLift 332171
  have htrace : WordTrace (prefixWord ++ tailWord_332171) baseStart_332171 baseEnd_332171 := by
    simpa [prefixWord, tailWord_332171, baseEnd_332171] using wordTrace_append hprefix tailTrace_332171
  have hstable : (prefixWord ++ tailWord_332171).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332171).length < 2 ^ (prefixWord ++ tailWord_332171).sum := by decide
  have hdescent : baseEnd_332171 < baseStart_332171 := by decide
  rcases family_descends (prefixWord ++ tailWord_332171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332192 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_332192 : Nat := 118140960795 + 332192 * 2 ^ 59
def prefixEnd_332192 : Nat := 4983230072969 + 3 ^ 40 * 332192 * 2
def baseEnd_332192 : Nat := 151621480514195138642029

theorem tailTrace_332192 : CollatzResearch.WordTrace tailWord_332192 prefixEnd_332192 151621480514195138642029 := by
  unfold tailWord_332192
  simp only [CollatzResearch.WordTrace]
  refine ⟨6058018806266296360947415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8077358408355061814596553 6058018806266296360947415)
  ·
    refine ⟨9087028209399444541421123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6058018806266296360947415 9087028209399444541421123)
    ·
      refine ⟨13630542314099166812131685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9087028209399444541421123 13630542314099166812131685)
      ·
        refine ⟨2555726683893593777274691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13630542314099166812131685 2555726683893593777274691)
        ·
          refine ⟨3833590025840390665912037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2555726683893593777274691 3833590025840390665912037)
          ·
            refine ⟨718798129845073249858507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3833590025840390665912037 718798129845073249858507)
            ·
              refine ⟨1078197194767609874787761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718798129845073249858507 1078197194767609874787761)
              ·
                refine ⟨808647896075707406090821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078197194767609874787761 808647896075707406090821)
                ·
                  refine ⟨151621480514195138642029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 808647896075707406090821 151621480514195138642029)
                  ·
                    rfl

theorem cell20_332192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_332192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332192 prefixEnd_332192 := by exact prefixLift 332192
  have htrace : WordTrace (prefixWord ++ tailWord_332192) baseStart_332192 baseEnd_332192 := by
    simpa [prefixWord, tailWord_332192, baseEnd_332192] using wordTrace_append hprefix tailTrace_332192
  have hstable : (prefixWord ++ tailWord_332192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332192).length < 2 ^ (prefixWord ++ tailWord_332192).sum := by decide
  have hdescent : baseEnd_332192 < baseStart_332192 := by decide
  rcases family_descends (prefixWord ++ tailWord_332192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332205 : List Nat := [1, 5, 2, 2, 2, 1, 2, 3, 2]
def baseStart_332205 : Nat := 118140960795 + 332205 * 2 ^ 59
def prefixEnd_332205 : Nat := 4983230072969 + 3 ^ 40 * 332205 * 2
def baseEnd_332205 : Nat := 151627414068424871208643

theorem tailTrace_332205 : CollatzResearch.WordTrace tailWord_332205 prefixEnd_332205 151627414068424871208643 := by
  unfold tailWord_332205
  simp only [CollatzResearch.WordTrace]
  refine ⟨12116511761485495942118069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8077674507656997294745379 12116511761485495942118069)
  ·
    refine ⟨1135922977639265244573569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12116511761485495942118069 1135922977639265244573569)
    ·
      refine ⟨851942233229448933430177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1135922977639265244573569 851942233229448933430177)
      ·
        refine ⟨638956674922086700072633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 851942233229448933430177 638956674922086700072633)
        ·
          refine ⟨479217506191565025054475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638956674922086700072633 479217506191565025054475)
          ·
            refine ⟨718826259287347537581713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479217506191565025054475 718826259287347537581713)
            ·
              refine ⟨539119694465510653186285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718826259287347537581713 539119694465510653186285)
              ·
                refine ⟨202169885424566494944857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 539119694465510653186285 202169885424566494944857)
                ·
                  refine ⟨151627414068424871208643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202169885424566494944857 151627414068424871208643)
                  ·
                    rfl

theorem cell20_332205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_332205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332205 prefixEnd_332205 := by exact prefixLift 332205
  have htrace : WordTrace (prefixWord ++ tailWord_332205) baseStart_332205 baseEnd_332205 := by
    simpa [prefixWord, tailWord_332205, baseEnd_332205] using wordTrace_append hprefix tailTrace_332205
  have hstable : (prefixWord ++ tailWord_332205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332205).length < 2 ^ (prefixWord ++ tailWord_332205).sum := by decide
  have hdescent : baseEnd_332205 < baseStart_332205 := by decide
  rcases family_descends (prefixWord ++ tailWord_332205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332209 : List Nat := [1, 2, 2, 4, 1, 2, 1, 5, 2]
def baseStart_332209 : Nat := 118140960795 + 332209 * 2 ^ 59
def prefixEnd_332209 : Nat := 4983230072969 + 3 ^ 40 * 332209 * 2
def baseEnd_332209 : Nat := 151629239777418635075293

theorem tailTrace_332209 : CollatzResearch.WordTrace tailWord_332209 prefixEnd_332209 151629239777418635075293 := by
  unfold tailWord_332209
  simp only [CollatzResearch.WordTrace]
  refine ⟨12116657653471004625263681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8077771768980669750175787 12116657653471004625263681)
  ·
    refine ⟨9087493240103253468947761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12116657653471004625263681 9087493240103253468947761)
    ·
      refine ⟨6815619930077440101710821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9087493240103253468947761 6815619930077440101710821)
      ·
        refine ⟨1277928736889520019070779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6815619930077440101710821 1277928736889520019070779)
        ·
          refine ⟨1916893105334280028606169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277928736889520019070779 1916893105334280028606169)
          ·
            refine ⟨1437669829000710021454627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1916893105334280028606169 1437669829000710021454627)
            ·
              refine ⟨2156504743501065032181941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437669829000710021454627 2156504743501065032181941)
              ·
                refine ⟨202172319703224846767057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2156504743501065032181941 202172319703224846767057)
                ·
                  refine ⟨151629239777418635075293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202172319703224846767057 151629239777418635075293)
                  ·
                    rfl

theorem cell20_332209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_332209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332209 prefixEnd_332209 := by exact prefixLift 332209
  have htrace : WordTrace (prefixWord ++ tailWord_332209) baseStart_332209 baseEnd_332209 := by
    simpa [prefixWord, tailWord_332209, baseEnd_332209] using wordTrace_append hprefix tailTrace_332209
  have hstable : (prefixWord ++ tailWord_332209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332209).length < 2 ^ (prefixWord ++ tailWord_332209).sum := by decide
  have hdescent : baseEnd_332209 < baseStart_332209 := by decide
  rcases family_descends (prefixWord ++ tailWord_332209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332264 : List Nat := [2, 1, 4, 1, 1, 5, 1, 3, 2]
def baseStart_332264 : Nat := 118140960795 + 332264 * 2 ^ 59
def prefixEnd_332264 : Nat := 4983230072969 + 3 ^ 40 * 332264 * 2
def baseEnd_332264 : Nat := 151654343276082888241735

theorem tailTrace_332264 : CollatzResearch.WordTrace tailWord_332264 prefixEnd_332264 151654343276082888241735 := by
  unfold tailWord_332264
  simp only [CollatzResearch.WordTrace]
  refine ⟨6059331834135874509257923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8079109112181166012343897 6059331834135874509257923)
  ·
    refine ⟨9088997751203811763886885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6059331834135874509257923 9088997751203811763886885)
    ·
      refine ⟨1704187078350714705728791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9088997751203811763886885 1704187078350714705728791)
      ·
        refine ⟨2556280617526072058593187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704187078350714705728791 2556280617526072058593187)
        ·
          refine ⟨3834420926289108087889781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2556280617526072058593187 3834420926289108087889781)
          ·
            refine ⟨359476961839603883239667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3834420926289108087889781 359476961839603883239667)
            ·
              refine ⟨539215442759405824859501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359476961839603883239667 539215442759405824859501)
              ·
                refine ⟨202205791034777184322313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 539215442759405824859501 202205791034777184322313)
                ·
                  refine ⟨151654343276082888241735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202205791034777184322313 151654343276082888241735)
                  ·
                    rfl

theorem cell20_332264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_332264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332264 prefixEnd_332264 := by exact prefixLift 332264
  have htrace : WordTrace (prefixWord ++ tailWord_332264) baseStart_332264 baseEnd_332264 := by
    simpa [prefixWord, tailWord_332264, baseEnd_332264] using wordTrace_append hprefix tailTrace_332264
  have hstable : (prefixWord ++ tailWord_332264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332264).length < 2 ^ (prefixWord ++ tailWord_332264).sum := by decide
  have hdescent : baseEnd_332264 < baseStart_332264 := by decide
  rcases family_descends (prefixWord ++ tailWord_332264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332292 : List Nat := [2, 3, 2, 3, 1, 2, 2, 5]
def baseStart_332292 : Nat := 118140960795 + 332292 * 2 ^ 59
def prefixEnd_332292 : Nat := 4983230072969 + 3 ^ 40 * 332292 * 2
def baseEnd_332292 : Nat := 50555707746346411769429

theorem tailTrace_332292 : CollatzResearch.WordTrace tailWord_332292 prefixEnd_332292 50555707746346411769429 := by
  unfold tailWord_332292
  simp only [CollatzResearch.WordTrace]
  refine ⟨6059842456085154900267565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8079789941446873200356753 6059842456085154900267565)
  ·
    refine ⟨2272440921031933087600337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6059842456085154900267565 2272440921031933087600337)
    ·
      refine ⟨1704330690773949815700253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2272440921031933087600337 1704330690773949815700253)
      ·
        refine ⟨639124009040231180887595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1704330690773949815700253 639124009040231180887595)
        ·
          refine ⟨958686013560346771331393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639124009040231180887595 958686013560346771331393)
          ·
            refine ⟨719014510170260078498545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958686013560346771331393 719014510170260078498545)
            ·
              refine ⟨539260882627695058873909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719014510170260078498545 539260882627695058873909)
              ·
                refine ⟨50555707746346411769429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 539260882627695058873909 50555707746346411769429)
                ·
                  rfl

theorem cell20_332292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_332292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332292 prefixEnd_332292 := by exact prefixLift 332292
  have htrace : WordTrace (prefixWord ++ tailWord_332292) baseStart_332292 baseEnd_332292 := by
    simpa [prefixWord, tailWord_332292, baseEnd_332292] using wordTrace_append hprefix tailTrace_332292
  have hstable : (prefixWord ++ tailWord_332292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332292).length < 2 ^ (prefixWord ++ tailWord_332292).sum := by decide
  have hdescent : baseEnd_332292 < baseStart_332292 := by decide
  rcases family_descends (prefixWord ++ tailWord_332292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332295 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 3]
def baseStart_332295 : Nat := 118140960795 + 332295 * 2 ^ 59
def prefixEnd_332295 : Nat := 4983230072969 + 3 ^ 40 * 332295 * 2
def baseEnd_332295 : Nat := 151668492520784558208275

theorem tailTrace_332295 : CollatzResearch.WordTrace tailWord_332295 prefixEnd_332295 151668492520784558208275 := by
  unfold tailWord_332295
  simp only [CollatzResearch.WordTrace]
  refine ⟨12119794331159441312894339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8079862887439627541929559 12119794331159441312894339)
  ·
    refine ⟨18179691496739161969341509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12119794331159441312894339 18179691496739161969341509)
    ·
      refine ⟨3408692155638592869251533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18179691496739161969341509 3408692155638592869251533)
      ·
        refine ⟨1278259558364472325969325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3408692155638592869251533 1278259558364472325969325)
        ·
          refine ⟨479347334386677122238497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1278259558364472325969325 479347334386677122238497)
          ·
            refine ⟨359510500790007841678873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479347334386677122238497 359510500790007841678873)
            ·
              refine ⟨269632875592505881259155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359510500790007841678873 269632875592505881259155)
              ·
                refine ⟨404449313388758821888733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269632875592505881259155 404449313388758821888733)
                ·
                  refine ⟨151668492520784558208275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404449313388758821888733 151668492520784558208275)
                  ·
                    rfl

theorem cell20_332295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 3].length) (baseStart_332295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332295 prefixEnd_332295 := by exact prefixLift 332295
  have htrace : WordTrace (prefixWord ++ tailWord_332295) baseStart_332295 baseEnd_332295 := by
    simpa [prefixWord, tailWord_332295, baseEnd_332295] using wordTrace_append hprefix tailTrace_332295
  have hstable : (prefixWord ++ tailWord_332295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332295).length < 2 ^ (prefixWord ++ tailWord_332295).sum := by decide
  have hdescent : baseEnd_332295 < baseStart_332295 := by decide
  rcases family_descends (prefixWord ++ tailWord_332295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332299 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 3]
def baseStart_332299 : Nat := 118140960795 + 332299 * 2 ^ 59
def prefixEnd_332299 : Nat := 4983230072969 + 3 ^ 40 * 332299 * 2
def baseEnd_332299 : Nat := 151670318229778322074925

theorem tailTrace_332299 : CollatzResearch.WordTrace tailWord_332299 prefixEnd_332299 151670318229778322074925 := by
  unfold tailWord_332299
  simp only [CollatzResearch.WordTrace]
  refine ⟨12119940223144949996039951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8079960148763299997359967 12119940223144949996039951)
  ·
    refine ⟨18179910334717424994059927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12119940223144949996039951 18179910334717424994059927)
    ·
      refine ⟨27269865502076137491089891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18179910334717424994059927 27269865502076137491089891)
      ·
        refine ⟨40904798253114206236634837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27269865502076137491089891 40904798253114206236634837)
        ·
          refine ⟨958706209057364208671129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 40904798253114206236634837 958706209057364208671129)
          ·
            refine ⟨719029656793023156503347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958706209057364208671129 719029656793023156503347)
            ·
              refine ⟨1078544485189534734755021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719029656793023156503347 1078544485189534734755021)
              ·
                refine ⟨404454181946075525533133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1078544485189534734755021 404454181946075525533133)
                ·
                  refine ⟨151670318229778322074925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404454181946075525533133 151670318229778322074925)
                  ·
                    rfl

theorem cell20_332299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_332299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332299 prefixEnd_332299 := by exact prefixLift 332299
  have htrace : WordTrace (prefixWord ++ tailWord_332299) baseStart_332299 baseEnd_332299 := by
    simpa [prefixWord, tailWord_332299, baseEnd_332299] using wordTrace_append hprefix tailTrace_332299
  have hstable : (prefixWord ++ tailWord_332299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332299).length < 2 ^ (prefixWord ++ tailWord_332299).sum := by decide
  have hdescent : baseEnd_332299 < baseStart_332299 := by decide
  rcases family_descends (prefixWord ++ tailWord_332299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332389 : List Nat := [1, 3, 1, 3, 4, 1, 7]
def baseStart_332389 : Nat := 118140960795 + 332389 * 2 ^ 59
def prefixEnd_332389 : Nat := 4983230072969 + 3 ^ 40 * 332389 * 2
def baseEnd_332389 : Nat := 16856821853570889897173

theorem tailTrace_332389 : CollatzResearch.WordTrace tailWord_332389 prefixEnd_332389 16856821853570889897173 := by
  unfold tailWord_332389
  simp only [CollatzResearch.WordTrace]
  refine ⟨12123222792818895366816221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8082148528545930244544147 12123222792818895366816221)
  ·
    refine ⟨4546208547307085762556083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12123222792818895366816221 4546208547307085762556083)
    ·
      refine ⟨6819312820960628643834125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4546208547307085762556083 6819312820960628643834125)
      ·
        refine ⟨2557242307860235741437797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6819312820960628643834125 2557242307860235741437797)
        ·
          refine ⟨479482932723794201519587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2557242307860235741437797 479482932723794201519587)
          ·
            refine ⟨719224399085691302279381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479482932723794201519587 719224399085691302279381)
            ·
              refine ⟨16856821853570889897173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 719224399085691302279381 16856821853570889897173)
              ·
                rfl

theorem cell20_332389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 7].length) (baseStart_332389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332389 prefixEnd_332389 := by exact prefixLift 332389
  have htrace : WordTrace (prefixWord ++ tailWord_332389) baseStart_332389 baseEnd_332389 := by
    simpa [prefixWord, tailWord_332389, baseEnd_332389] using wordTrace_append hprefix tailTrace_332389
  have hstable : (prefixWord ++ tailWord_332389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332389).length < 2 ^ (prefixWord ++ tailWord_332389).sum := by decide
  have hdescent : baseEnd_332389 < baseStart_332389 := by decide
  rcases family_descends (prefixWord ++ tailWord_332389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332420 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_332420 : Nat := 118140960795 + 332420 * 2 ^ 59
def prefixEnd_332420 : Nat := 4983230072969 + 3 ^ 40 * 332420 * 2
def baseEnd_332420 : Nat := 151725545926839679041097

theorem tailTrace_332420 : CollatzResearch.WordTrace tailWord_332420 prefixEnd_332420 151725545926839679041097 := by
  unfold tailWord_332420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6062176727853293830597357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8082902303804391774129809 6062176727853293830597357)
  ·
    refine ⟨2273316272944985186474009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6062176727853293830597357 2273316272944985186474009)
    ·
      refine ⟨1704987204708738889855507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2273316272944985186474009 1704987204708738889855507)
      ·
        refine ⟨2557480807063108334783261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704987204708738889855507 2557480807063108334783261)
        ·
          refine ⟨959055302648665625543723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2557480807063108334783261 959055302648665625543723)
          ·
            refine ⟨1438582953972998438315585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959055302648665625543723 1438582953972998438315585)
            ·
              refine ⟨1078937215479748828736689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438582953972998438315585 1078937215479748828736689)
              ·
                refine ⟨809202911609811621552517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078937215479748828736689 809202911609811621552517)
                ·
                  refine ⟨151725545926839679041097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 809202911609811621552517 151725545926839679041097)
                  ·
                    rfl

theorem cell20_332420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_332420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332420 prefixEnd_332420 := by exact prefixLift 332420
  have htrace : WordTrace (prefixWord ++ tailWord_332420) baseStart_332420 baseEnd_332420 := by
    simpa [prefixWord, tailWord_332420, baseEnd_332420] using wordTrace_append hprefix tailTrace_332420
  have hstable : (prefixWord ++ tailWord_332420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332420).length < 2 ^ (prefixWord ++ tailWord_332420).sum := by decide
  have hdescent : baseEnd_332420 < baseStart_332420 := by decide
  rcases family_descends (prefixWord ++ tailWord_332420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332513 : List Nat := [1, 2, 3, 1, 4, 2, 1, 4, 2]
def baseStart_332513 : Nat := 118140960795 + 332513 * 2 ^ 59
def prefixEnd_332513 : Nat := 4983230072969 + 3 ^ 40 * 332513 * 2
def baseEnd_332513 : Nat := 151767993660944688940717

theorem tailTrace_332513 : CollatzResearch.WordTrace tailWord_332513 prefixEnd_332513 151767993660944688940717 := by
  unfold tailWord_332513
  simp only [CollatzResearch.WordTrace]
  refine ⟨12127745444369664544330193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8085163629579776362886795 12127745444369664544330193)
  ·
    refine ⟨9095809083277248408247645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12127745444369664544330193 9095809083277248408247645)
    ·
      refine ⟨3410928406228968153092867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9095809083277248408247645 3410928406228968153092867)
      ·
        refine ⟨5116392609343452229639301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3410928406228968153092867 5116392609343452229639301)
        ·
          refine ⟨959323614251897293057369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5116392609343452229639301 959323614251897293057369)
          ·
            refine ⟨719492710688922969793027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959323614251897293057369 719492710688922969793027)
            ·
              refine ⟨1079239066033384454689541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719492710688922969793027 1079239066033384454689541)
              ·
                refine ⟨202357324881259585254289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1079239066033384454689541 202357324881259585254289)
                ·
                  refine ⟨151767993660944688940717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202357324881259585254289 151767993660944688940717)
                  ·
                    rfl

theorem cell20_332513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_332513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332513 prefixEnd_332513 := by exact prefixLift 332513
  have htrace : WordTrace (prefixWord ++ tailWord_332513) baseStart_332513 baseEnd_332513 := by
    simpa [prefixWord, tailWord_332513, baseEnd_332513] using wordTrace_append hprefix tailTrace_332513
  have hstable : (prefixWord ++ tailWord_332513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332513).length < 2 ^ (prefixWord ++ tailWord_332513).sum := by decide
  have hdescent : baseEnd_332513 < baseStart_332513 := by decide
  rcases family_descends (prefixWord ++ tailWord_332513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332520 : List Nat := [2, 1, 4, 1, 4, 2, 1, 5]
def baseStart_332520 : Nat := 118140960795 + 332520 * 2 ^ 59
def prefixEnd_332520 : Nat := 4983230072969 + 3 ^ 40 * 332520 * 2
def baseEnd_332520 : Nat := 50590396217227925235785

theorem tailTrace_332520 : CollatzResearch.WordTrace tailWord_332520 prefixEnd_332520 50590396217227925235785 := by
  unfold tailWord_332520
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064000377672152369917507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8085333836896203159890009 6064000377672152369917507)
  ·
    refine ⟨9096000566508228554876261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6064000377672152369917507 9096000566508228554876261)
    ·
      refine ⟨1705500106220292854039299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9096000566508228554876261 1705500106220292854039299)
      ·
        refine ⟨2558250159330439281058949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705500106220292854039299 2558250159330439281058949)
        ·
          refine ⟨479671904874457365198553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2558250159330439281058949 479671904874457365198553)
          ·
            refine ⟨359753928655843023898915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479671904874457365198553 359753928655843023898915)
            ·
              refine ⟨539630892983764535848373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359753928655843023898915 539630892983764535848373)
              ·
                refine ⟨50590396217227925235785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 539630892983764535848373 50590396217227925235785)
                ·
                  rfl

theorem cell20_332520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_332520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332520 prefixEnd_332520 := by exact prefixLift 332520
  have htrace : WordTrace (prefixWord ++ tailWord_332520) baseStart_332520 baseEnd_332520 := by
    simpa [prefixWord, tailWord_332520, baseEnd_332520] using wordTrace_append hprefix tailTrace_332520
  have hstable : (prefixWord ++ tailWord_332520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332520).length < 2 ^ (prefixWord ++ tailWord_332520).sum := by decide
  have hdescent : baseEnd_332520 < baseStart_332520 := by decide
  rcases family_descends (prefixWord ++ tailWord_332520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332531 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_332531 : Nat := 118140960795 + 332531 * 2 ^ 59
def prefixEnd_332531 : Nat := 4983230072969 + 3 ^ 40 * 332531 * 2
def baseEnd_332531 : Nat := 151776209351416626340643

theorem tailTrace_332531 : CollatzResearch.WordTrace tailWord_332531 prefixEnd_332531 151776209351416626340643 := by
  unfold tailWord_332531
  simp only [CollatzResearch.WordTrace]
  refine ⟨12128401958304453618485447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8085601305536302412323631 12128401958304453618485447)
  ·
    refine ⟨18192602937456680427728171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12128401958304453618485447 18192602937456680427728171)
    ·
      refine ⟨27288904406185020641592257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18192602937456680427728171 27288904406185020641592257)
      ·
        refine ⟨20466678304638765481194193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27288904406185020641592257 20466678304638765481194193)
        ·
          refine ⟨15350008728479074110895645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20466678304638765481194193 15350008728479074110895645)
          ·
            refine ⟨5756253273179652791585867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15350008728479074110895645 5756253273179652791585867)
            ·
              refine ⟨8634379909769479187378801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5756253273179652791585867 8634379909769479187378801)
              ·
                refine ⟨6475784932327109390534101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8634379909769479187378801 6475784932327109390534101)
                ·
                  refine ⟨151776209351416626340643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6475784932327109390534101 151776209351416626340643)
                  ·
                    rfl

theorem cell20_332531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_332531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332531 prefixEnd_332531 := by exact prefixLift 332531
  have htrace : WordTrace (prefixWord ++ tailWord_332531) baseStart_332531 baseEnd_332531 := by
    simpa [prefixWord, tailWord_332531, baseEnd_332531] using wordTrace_append hprefix tailTrace_332531
  have hstable : (prefixWord ++ tailWord_332531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332531).length < 2 ^ (prefixWord ++ tailWord_332531).sum := by decide
  have hdescent : baseEnd_332531 < baseStart_332531 := by decide
  rcases family_descends (prefixWord ++ tailWord_332531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332534 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_332534 : Nat := 118140960795 + 332534 * 2 ^ 59
def prefixEnd_332534 : Nat := 4983230072969 + 3 ^ 40 * 332534 * 2
def baseEnd_332534 : Nat := 151777578633161949240631

theorem tailTrace_332534 : CollatzResearch.WordTrace tailWord_332534 prefixEnd_332534 151777578633161949240631 := by
  unfold tailWord_332534
  simp only [CollatzResearch.WordTrace]
  refine ⟨758031961080849070677791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8085674251529056753896437 758031961080849070677791)
  ·
    refine ⟨1137047941621273606016687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 758031961080849070677791 1137047941621273606016687)
    ·
      refine ⟨1705571912431910409025031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137047941621273606016687 1705571912431910409025031)
      ·
        refine ⟨2558357868647865613537547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705571912431910409025031 2558357868647865613537547)
        ·
          refine ⟨3837536802971798420306321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558357868647865613537547 3837536802971798420306321)
          ·
            refine ⟨2878152602228848815229741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3837536802971798420306321 2878152602228848815229741)
            ·
              refine ⟨1079307225835818305711153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2878152602228848815229741 1079307225835818305711153)
              ·
                refine ⟨809480419376863729283365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079307225835818305711153 809480419376863729283365)
                ·
                  refine ⟨151777578633161949240631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 809480419376863729283365 151777578633161949240631)
                  ·
                    rfl

theorem cell20_332534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_332534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332534 prefixEnd_332534 := by exact prefixLift 332534
  have htrace : WordTrace (prefixWord ++ tailWord_332534) baseStart_332534 baseEnd_332534 := by
    simpa [prefixWord, tailWord_332534, baseEnd_332534] using wordTrace_append hprefix tailTrace_332534
  have hstable : (prefixWord ++ tailWord_332534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332534).length < 2 ^ (prefixWord ++ tailWord_332534).sum := by decide
  have hdescent : baseEnd_332534 < baseStart_332534 := by decide
  rcases family_descends (prefixWord ++ tailWord_332534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332541 : List Nat := [1, 4, 1, 1, 1, 1, 7, 4]
def baseStart_332541 : Nat := 118140960795 + 332541 * 2 ^ 59
def prefixEnd_332541 : Nat := 4983230072969 + 3 ^ 40 * 332541 * 2
def baseEnd_332541 : Nat := 50593591207967012002423

theorem tailTrace_332541 : CollatzResearch.WordTrace tailWord_332541 prefixEnd_332541 50593591207967012002423 := by
  unfold tailWord_332541
  simp only [CollatzResearch.WordTrace]
  refine ⟨12128766688268225326349477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8085844458845483550899651 12128766688268225326349477)
  ·
    refine ⟨2274143754050292248690527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12128766688268225326349477 2274143754050292248690527)
    ·
      refine ⟨3411215631075438373035791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2274143754050292248690527 3411215631075438373035791)
      ·
        refine ⟨5116823446613157559553687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411215631075438373035791 5116823446613157559553687)
        ·
          refine ⟨7675235169919736339330531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116823446613157559553687 7675235169919736339330531)
          ·
            refine ⟨11512852754879604508995797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675235169919736339330531 11512852754879604508995797)
            ·
              refine ⟨269832486442490730679589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11512852754879604508995797 269832486442490730679589)
              ·
                refine ⟨50593591207967012002423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 269832486442490730679589 50593591207967012002423)
                ·
                  rfl

theorem cell20_332541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 4].length) (baseStart_332541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332541 prefixEnd_332541 := by exact prefixLift 332541
  have htrace : WordTrace (prefixWord ++ tailWord_332541) baseStart_332541 baseEnd_332541 := by
    simpa [prefixWord, tailWord_332541, baseEnd_332541] using wordTrace_append hprefix tailTrace_332541
  have hstable : (prefixWord ++ tailWord_332541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332541).length < 2 ^ (prefixWord ++ tailWord_332541).sum := by decide
  have hdescent : baseEnd_332541 < baseStart_332541 := by decide
  rcases family_descends (prefixWord ++ tailWord_332541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332548 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_332548 : Nat := 118140960795 + 332548 * 2 ^ 59
def prefixEnd_332548 : Nat := 4983230072969 + 3 ^ 40 * 332548 * 2
def baseEnd_332548 : Nat := 151783968614640122773907

theorem tailTrace_332548 : CollatzResearch.WordTrace tailWord_332548 prefixEnd_332548 151783968614640122773907 := by
  unfold tailWord_332548
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064510999621432760927149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8086014666161910347902865 6064510999621432760927149)
  ·
    refine ⟨2274191624858037285347681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6064510999621432760927149 2274191624858037285347681)
    ·
      refine ⟨1705643718643527964010761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2274191624858037285347681 1705643718643527964010761)
      ·
        refine ⟨1279232788982645973008071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1705643718643527964010761 1279232788982645973008071)
        ·
          refine ⟨1918849183473968959512107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279232788982645973008071 1918849183473968959512107)
          ·
            refine ⟨2878273775210953439268161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918849183473968959512107 2878273775210953439268161)
            ·
              refine ⟨2158705331408215079451121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2878273775210953439268161 2158705331408215079451121)
              ·
                refine ⟨1619028998556161309588341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158705331408215079451121 1619028998556161309588341)
                ·
                  refine ⟨151783968614640122773907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1619028998556161309588341 151783968614640122773907)
                  ·
                    rfl

theorem cell20_332548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_332548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332548 prefixEnd_332548 := by exact prefixLift 332548
  have htrace : WordTrace (prefixWord ++ tailWord_332548) baseStart_332548 baseEnd_332548 := by
    simpa [prefixWord, tailWord_332548, baseEnd_332548] using wordTrace_append hprefix tailTrace_332548
  have hstable : (prefixWord ++ tailWord_332548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332548).length < 2 ^ (prefixWord ++ tailWord_332548).sum := by decide
  have hdescent : baseEnd_332548 < baseStart_332548 := by decide
  rcases family_descends (prefixWord ++ tailWord_332548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332551 : List Nat := [1, 1, 4, 4, 1, 1, 1, 5, 2]
def baseStart_332551 : Nat := 118140960795 + 332551 * 2 ^ 59
def prefixEnd_332551 : Nat := 4983230072969 + 3 ^ 40 * 332551 * 2
def baseEnd_332551 : Nat := 151785337896385445673895

theorem tailTrace_332551 : CollatzResearch.WordTrace tailWord_332551 prefixEnd_332551 151785337896385445673895 := by
  unfold tailWord_332551
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129131418231997034213507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8086087612154664689475671 12129131418231997034213507)
  ·
    refine ⟨18193697127347995551320261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12129131418231997034213507 18193697127347995551320261)
    ·
      refine ⟨3411318211377749165872549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18193697127347995551320261 3411318211377749165872549)
      ·
        refine ⟨639622164633327968601103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3411318211377749165872549 639622164633327968601103)
        ·
          refine ⟨959433246949991952901655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639622164633327968601103 959433246949991952901655)
          ·
            refine ⟨1439149870424987929352483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959433246949991952901655 1439149870424987929352483)
            ·
              refine ⟨2158724805637481894028725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439149870424987929352483 2158724805637481894028725)
              ·
                refine ⟨202380450528513927565193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2158724805637481894028725 202380450528513927565193)
                ·
                  refine ⟨151785337896385445673895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202380450528513927565193 151785337896385445673895)
                  ·
                    rfl

theorem cell20_332551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 2].length) (baseStart_332551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332551 prefixEnd_332551 := by exact prefixLift 332551
  have htrace : WordTrace (prefixWord ++ tailWord_332551) baseStart_332551 baseEnd_332551 := by
    simpa [prefixWord, tailWord_332551, baseEnd_332551] using wordTrace_append hprefix tailTrace_332551
  have hstable : (prefixWord ++ tailWord_332551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332551).length < 2 ^ (prefixWord ++ tailWord_332551).sum := by decide
  have hdescent : baseEnd_332551 < baseStart_332551 := by decide
  rcases family_descends (prefixWord ++ tailWord_332551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332572 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 4]
def baseStart_332572 : Nat := 118140960795 + 332572 * 2 ^ 59
def prefixEnd_332572 : Nat := 4983230072969 + 3 ^ 40 * 332572 * 2
def baseEnd_332572 : Nat := 151794922868602705973809

theorem tailTrace_332572 : CollatzResearch.WordTrace tailWord_332572 prefixEnd_332572 151794922868602705973809 := by
  unfold tailWord_332572
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064948675577958810363985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8086598234103945080485313 6064948675577958810363985)
  ·
    refine ⟨4548711506683469107772989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6064948675577958810363985 4548711506683469107772989)
    ·
      refine ⟨1705766815006300915414871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4548711506683469107772989 1705766815006300915414871)
      ·
        refine ⟨2558650222509451373122307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705766815006300915414871 2558650222509451373122307)
        ·
          refine ⟨3837975333764177059683461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558650222509451373122307 3837975333764177059683461)
          ·
            refine ⟨719620375080783198690649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3837975333764177059683461 719620375080783198690649)
            ·
              refine ⟨539715281310587399017987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719620375080783198690649 539715281310587399017987)
              ·
                refine ⟨809572921965881098526981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539715281310587399017987 809572921965881098526981)
                ·
                  refine ⟨151794922868602705973809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 809572921965881098526981 151794922868602705973809)
                  ·
                    rfl

theorem cell20_332572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_332572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332572 prefixEnd_332572 := by exact prefixLift 332572
  have htrace : WordTrace (prefixWord ++ tailWord_332572) baseStart_332572 baseEnd_332572 := by
    simpa [prefixWord, tailWord_332572, baseEnd_332572] using wordTrace_append hprefix tailTrace_332572
  have hstable : (prefixWord ++ tailWord_332572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332572).length < 2 ^ (prefixWord ++ tailWord_332572).sum := by decide
  have hdescent : baseEnd_332572 < baseStart_332572 := by decide
  rcases family_descends (prefixWord ++ tailWord_332572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332593 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_332593 : Nat := 118140960795 + 332593 * 2 ^ 59
def prefixEnd_332593 : Nat := 4983230072969 + 3 ^ 40 * 332593 * 2
def baseEnd_332593 : Nat := 151804507840819966273723

theorem tailTrace_332593 : CollatzResearch.WordTrace tailWord_332593 prefixEnd_332593 151804507840819966273723 := by
  unfold tailWord_332593
  simp only [CollatzResearch.WordTrace]
  refine ⟨12130663284079838207242433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8087108856053225471494955 12130663284079838207242433)
  ·
    refine ⟨9097997463059878655431825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12130663284079838207242433 9097997463059878655431825)
    ·
      refine ⟨6823498097294908991573869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9097997463059878655431825 6823498097294908991573869)
      ·
        refine ⟨2558811786485590871840201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6823498097294908991573869 2558811786485590871840201)
        ·
          refine ⟨1919108839864193153880151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2558811786485590871840201 1919108839864193153880151)
          ·
            refine ⟨2878663259796289730820227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919108839864193153880151 2878663259796289730820227)
            ·
              refine ⟨4317994889694434596230341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878663259796289730820227 4317994889694434596230341)
              ·
                refine ⟨809624041817706486793189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4317994889694434596230341 809624041817706486793189)
                ·
                  refine ⟨151804507840819966273723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 809624041817706486793189 151804507840819966273723)
                  ·
                    rfl

theorem cell20_332593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_332593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332593 prefixEnd_332593 := by exact prefixLift 332593
  have htrace : WordTrace (prefixWord ++ tailWord_332593) baseStart_332593 baseEnd_332593 := by
    simpa [prefixWord, tailWord_332593, baseEnd_332593] using wordTrace_append hprefix tailTrace_332593
  have hstable : (prefixWord ++ tailWord_332593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332593).length < 2 ^ (prefixWord ++ tailWord_332593).sum := by decide
  have hdescent : baseEnd_332593 < baseStart_332593 := by decide
  rcases family_descends (prefixWord ++ tailWord_332593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332596 : List Nat := [2, 5, 1, 1, 3, 1, 1, 6]
def baseStart_332596 : Nat := 118140960795 + 332596 * 2 ^ 59
def prefixEnd_332596 : Nat := 4983230072969 + 3 ^ 40 * 332596 * 2
def baseEnd_332596 : Nat := 50601959040855096391237

theorem tailTrace_332596 : CollatzResearch.WordTrace tailWord_332596 prefixEnd_332596 50601959040855096391237 := by
  unfold tailWord_332596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6065386351534484859800821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8087181802045979813067761 6065386351534484859800821)
  ·
    refine ⟨568629970456357955606327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6065386351534484859800821 568629970456357955606327)
    ·
      refine ⟨852944955684536933409491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568629970456357955606327 852944955684536933409491)
      ·
        refine ⟨1279417433526805400114237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852944955684536933409491 1279417433526805400114237)
        ·
          refine ⟨479781537572552025042839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1279417433526805400114237 479781537572552025042839)
          ·
            refine ⟨719672306358828037564259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479781537572552025042839 719672306358828037564259)
            ·
              refine ⟨1079508459538242056346389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719672306358828037564259 1079508459538242056346389)
              ·
                refine ⟨50601959040855096391237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1079508459538242056346389 50601959040855096391237)
                ·
                  rfl

theorem cell20_332596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_332596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332596 prefixEnd_332596 := by exact prefixLift 332596
  have htrace : WordTrace (prefixWord ++ tailWord_332596) baseStart_332596 baseEnd_332596 := by
    simpa [prefixWord, tailWord_332596, baseEnd_332596] using wordTrace_append hprefix tailTrace_332596
  have hstable : (prefixWord ++ tailWord_332596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332596).length < 2 ^ (prefixWord ++ tailWord_332596).sum := by decide
  have hdescent : baseEnd_332596 < baseStart_332596 := by decide
  rcases family_descends (prefixWord ++ tailWord_332596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332600 : List Nat := [2, 1, 2, 1, 3, 2, 3, 6]
def baseStart_332600 : Nat := 118140960795 + 332600 * 2 ^ 59
def prefixEnd_332600 : Nat := 4983230072969 + 3 ^ 40 * 332600 * 2
def baseEnd_332600 : Nat := 50602567610519684346787

theorem tailTrace_332600 : CollatzResearch.WordTrace tailWord_332600 prefixEnd_332600 50602567610519684346787 := by
  unfold tailWord_332600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6065459297527239201373627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8087279063369652268498169 6065459297527239201373627)
  ·
    refine ⟨9098188946290858802060441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6065459297527239201373627 9098188946290858802060441)
    ·
      refine ⟨6823641709718144101545331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9098188946290858802060441 6823641709718144101545331)
      ·
        refine ⟨10235462564577216152317997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6823641709718144101545331 10235462564577216152317997)
        ·
          refine ⟨3838298461716456057119249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10235462564577216152317997 3838298461716456057119249)
          ·
            refine ⟨2878723846287342042839437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3838298461716456057119249 2878723846287342042839437)
            ·
              refine ⟨1079521442357753266064789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2878723846287342042839437 1079521442357753266064789)
              ·
                refine ⟨50602567610519684346787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1079521442357753266064789 50602567610519684346787)
                ·
                  rfl

theorem cell20_332600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_332600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332600 prefixEnd_332600 := by exact prefixLift 332600
  have htrace : WordTrace (prefixWord ++ tailWord_332600) baseStart_332600 baseEnd_332600 := by
    simpa [prefixWord, tailWord_332600, baseEnd_332600] using wordTrace_append hprefix tailTrace_332600
  have hstable : (prefixWord ++ tailWord_332600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332600).length < 2 ^ (prefixWord ++ tailWord_332600).sum := by decide
  have hdescent : baseEnd_332600 < baseStart_332600 := by decide
  rcases family_descends (prefixWord ++ tailWord_332600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332679 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 3]
def baseStart_332679 : Nat := 118140960795 + 332679 * 2 ^ 59
def prefixEnd_332679 : Nat := 4983230072969 + 3 ^ 40 * 332679 * 2
def baseEnd_332679 : Nat := 151843760584185889406705

theorem tailTrace_332679 : CollatzResearch.WordTrace tailWord_332679 prefixEnd_332679 151843760584185889406705 := by
  unfold tailWord_332679
  simp only [CollatzResearch.WordTrace]
  refine ⟨12133799961768274894873091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8089199974512183263248727 12133799961768274894873091)
  ·
    refine ⟨18200699942652412342309637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12133799961768274894873091 18200699942652412342309637)
    ·
      refine ⟨3412631239247327314183057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18200699942652412342309637 3412631239247327314183057)
      ·
        refine ⟨2559473429435495485637293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3412631239247327314183057 2559473429435495485637293)
        ·
          refine ⟨959802536038310807113985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2559473429435495485637293 959802536038310807113985)
          ·
            refine ⟨719851902028733105335489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 959802536038310807113985 719851902028733105335489)
            ·
              refine ⟨539888926521549829001617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719851902028733105335489 539888926521549829001617)
              ·
                refine ⟨404916694891162371751213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539888926521549829001617 404916694891162371751213)
                ·
                  refine ⟨151843760584185889406705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404916694891162371751213 151843760584185889406705)
                  ·
                    rfl

theorem cell20_332679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_332679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332679 prefixEnd_332679 := by exact prefixLift 332679
  have htrace : WordTrace (prefixWord ++ tailWord_332679) baseStart_332679 baseEnd_332679 := by
    simpa [prefixWord, tailWord_332679, baseEnd_332679] using wordTrace_append hprefix tailTrace_332679
  have hstable : (prefixWord ++ tailWord_332679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332679).length < 2 ^ (prefixWord ++ tailWord_332679).sum := by decide
  have hdescent : baseEnd_332679 < baseStart_332679 := by decide
  rcases family_descends (prefixWord ++ tailWord_332679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332682 : List Nat := [3, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_332682 : Nat := 118140960795 + 332682 * 2 ^ 59
def prefixEnd_332682 : Nat := 4983230072969 + 3 ^ 40 * 332682 * 2
def baseEnd_332682 : Nat := 151845129865931212306693

theorem tailTrace_332682 : CollatzResearch.WordTrace tailWord_332682 prefixEnd_332682 151845129865931212306693 := by
  unfold tailWord_332682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033477345189351601808075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8089272920504937604821533 3033477345189351601808075)
  ·
    refine ⟨4550216017784027402712113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3033477345189351601808075 4550216017784027402712113)
    ·
      refine ⟨3412662013338020552034085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4550216017784027402712113 3412662013338020552034085)
      ·
        refine ⟨639874127500878853506391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3412662013338020552034085 639874127500878853506391)
        ·
          refine ⟨959811191251318280259587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639874127500878853506391 959811191251318280259587)
          ·
            refine ⟨1439716786876977420389381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959811191251318280259587 1439716786876977420389381)
            ·
              refine ⟨269946897539433266323009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1439716786876977420389381 269946897539433266323009)
              ·
                refine ⟨202460173154574949742257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269946897539433266323009 202460173154574949742257)
                ·
                  refine ⟨151845129865931212306693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202460173154574949742257 151845129865931212306693)
                  ·
                    rfl

theorem cell20_332682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_332682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332682 prefixEnd_332682 := by exact prefixLift 332682
  have htrace : WordTrace (prefixWord ++ tailWord_332682) baseStart_332682 baseEnd_332682 := by
    simpa [prefixWord, tailWord_332682, baseEnd_332682] using wordTrace_append hprefix tailTrace_332682
  have hstable : (prefixWord ++ tailWord_332682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332682).length < 2 ^ (prefixWord ++ tailWord_332682).sum := by decide
  have hdescent : baseEnd_332682 < baseStart_332682 := by decide
  rcases family_descends (prefixWord ++ tailWord_332682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332683 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_332683 : Nat := 118140960795 + 332683 * 2 ^ 59
def prefixEnd_332683 : Nat := 4983230072969 + 3 ^ 40 * 332683 * 2
def baseEnd_332683 : Nat := 151845586293179653273355

theorem tailTrace_332683 : CollatzResearch.WordTrace tailWord_332683 prefixEnd_332683 151845586293179653273355 := by
  unfold tailWord_332683
  simp only [CollatzResearch.WordTrace]
  refine ⟨12133945853753783578018703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8089297235835855718679135 12133945853753783578018703)
  ·
    refine ⟨18200918780630675367028055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12133945853753783578018703 18200918780630675367028055)
    ·
      refine ⟨27301378170946013050542083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18200918780630675367028055 27301378170946013050542083)
      ·
        refine ⟨40952067256419019575813125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27301378170946013050542083 40952067256419019575813125)
        ·
          refine ⟨7678512610578566170464961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40952067256419019575813125 7678512610578566170464961)
          ·
            refine ⟨5758884457933924627848721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7678512610578566170464961 5758884457933924627848721)
            ·
              refine ⟨4319163343450443470886541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5758884457933924627848721 4319163343450443470886541)
              ·
                refine ⟨1619686253793916301582453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4319163343450443470886541 1619686253793916301582453)
                ·
                  refine ⟨151845586293179653273355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1619686253793916301582453 151845586293179653273355)
                  ·
                    rfl

theorem cell20_332683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_332683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332683 prefixEnd_332683 := by exact prefixLift 332683
  have htrace : WordTrace (prefixWord ++ tailWord_332683) baseStart_332683 baseEnd_332683 := by
    simpa [prefixWord, tailWord_332683, baseEnd_332683] using wordTrace_append hprefix tailTrace_332683
  have hstable : (prefixWord ++ tailWord_332683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332683).length < 2 ^ (prefixWord ++ tailWord_332683).sum := by decide
  have hdescent : baseEnd_332683 < baseStart_332683 := by decide
  rcases family_descends (prefixWord ++ tailWord_332683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332693 : List Nat := [1, 3, 2, 1, 1, 6, 1, 5]
def baseStart_332693 : Nat := 118140960795 + 332693 * 2 ^ 59
def prefixEnd_332693 : Nat := 4983230072969 + 3 ^ 40 * 332693 * 2
def baseEnd_332693 : Nat := 50616716855221354313327

theorem tailTrace_332693 : CollatzResearch.WordTrace tailWord_332693 prefixEnd_332693 50616716855221354313327 := by
  unfold tailWord_332693
  simp only [CollatzResearch.WordTrace]
  refine ⟨12134310583717555285882733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8089540389145036857255155 12134310583717555285882733)
  ·
    refine ⟨4550366468894083232206025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12134310583717555285882733 4550366468894083232206025)
    ·
      refine ⟨3412774851670562424154519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4550366468894083232206025 3412774851670562424154519)
      ·
        refine ⟨5119162277505843636231779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3412774851670562424154519 5119162277505843636231779)
        ·
          refine ⟨7678743416258765454347669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5119162277505843636231779 7678743416258765454347669)
          ·
            refine ⟨359941097637129630672547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7678743416258765454347669 359941097637129630672547)
            ·
              refine ⟨539911646455694446008821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359941097637129630672547 539911646455694446008821)
              ·
                refine ⟨50616716855221354313327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 539911646455694446008821 50616716855221354313327)
                ·
                  rfl

theorem cell20_332693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 5].length) (baseStart_332693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332693 prefixEnd_332693 := by exact prefixLift 332693
  have htrace : WordTrace (prefixWord ++ tailWord_332693) baseStart_332693 baseEnd_332693 := by
    simpa [prefixWord, tailWord_332693, baseEnd_332693] using wordTrace_append hprefix tailTrace_332693
  have hstable : (prefixWord ++ tailWord_332693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332693).length < 2 ^ (prefixWord ++ tailWord_332693).sum := by decide
  have hdescent : baseEnd_332693 < baseStart_332693 := by decide
  rcases family_descends (prefixWord ++ tailWord_332693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332786 : List Nat := [3, 2, 1, 5, 1, 2, 6]
def baseStart_332786 : Nat := 118140960795 + 332786 * 2 ^ 59
def prefixEnd_332786 : Nat := 4983230072969 + 3 ^ 40 * 332786 * 2
def baseEnd_332786 : Nat := 16876955366641008093289

theorem tailTrace_332786 : CollatzResearch.WordTrace tailWord_332786 prefixEnd_332786 16876955366641008093289 := by
  unfold tailWord_332786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034425643095158042254553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8091801714920421446012141 3034425643095158042254553)
  ·
    refine ⟨2275819232321368531690915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3034425643095158042254553 2275819232321368531690915)
    ·
      refine ⟨3413728848482052797536373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2275819232321368531690915 3413728848482052797536373)
      ·
        refine ⟨320037079545192449769035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3413728848482052797536373 320037079545192449769035)
        ·
          refine ⟨480055619317788674653553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320037079545192449769035 480055619317788674653553)
          ·
            refine ⟨360041714488341505990165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480055619317788674653553 360041714488341505990165)
            ·
              refine ⟨16876955366641008093289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 360041714488341505990165 16876955366641008093289)
              ·
                rfl

theorem cell20_332786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 6].length) (baseStart_332786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332786 prefixEnd_332786 := by exact prefixLift 332786
  have htrace : WordTrace (prefixWord ++ tailWord_332786) baseStart_332786 baseEnd_332786 := by
    simpa [prefixWord, tailWord_332786, baseEnd_332786] using wordTrace_append hprefix tailTrace_332786
  have hstable : (prefixWord ++ tailWord_332786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332786).length < 2 ^ (prefixWord ++ tailWord_332786).sum := by decide
  have hdescent : baseEnd_332786 < baseStart_332786 := by decide
  rcases family_descends (prefixWord ++ tailWord_332786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332810 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_332810 : Nat := 118140960795 + 332810 * 2 ^ 59
def prefixEnd_332810 : Nat := 4983230072969 + 3 ^ 40 * 332810 * 2
def baseEnd_332810 : Nat := 151903552553731656039503

theorem tailTrace_332810 : CollatzResearch.WordTrace tailWord_332810 prefixEnd_332810 151903552553731656039503 := by
  unfold tailWord_332810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034644481073421066972971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8092385282862456178594589 3034644481073421066972971)
  ·
    refine ⟨4551966721610131600459457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3034644481073421066972971 4551966721610131600459457)
    ·
      refine ⟨3413975041207598700344593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4551966721610131600459457 3413975041207598700344593)
      ·
        refine ⟨2560481280905699025258445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3413975041207598700344593 2560481280905699025258445)
        ·
          refine ⟨960180480339637134471917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2560481280905699025258445 960180480339637134471917)
          ·
            refine ⟨360067680127363925426969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 960180480339637134471917 360067680127363925426969)
            ·
              refine ⟨270050760095522944070227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360067680127363925426969 270050760095522944070227)
              ·
                refine ⟨405076140143284416105341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270050760095522944070227 405076140143284416105341)
                ·
                  refine ⟨151903552553731656039503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405076140143284416105341 151903552553731656039503)
                  ·
                    rfl

theorem cell20_332810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_332810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332810 prefixEnd_332810 := by exact prefixLift 332810
  have htrace : WordTrace (prefixWord ++ tailWord_332810) baseStart_332810 baseEnd_332810 := by
    simpa [prefixWord, tailWord_332810, baseEnd_332810] using wordTrace_append hprefix tailTrace_332810
  have hstable : (prefixWord ++ tailWord_332810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332810).length < 2 ^ (prefixWord ++ tailWord_332810).sum := by decide
  have hdescent : baseEnd_332810 < baseStart_332810 := by decide
  rcases family_descends (prefixWord ++ tailWord_332810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332862 : List Nat := [4, 2, 1, 3, 1, 3, 1, 5]
def baseStart_332862 : Nat := 118140960795 + 332862 * 2 ^ 59
def prefixEnd_332862 : Nat := 4983230072969 + 3 ^ 40 * 332862 * 2
def baseEnd_332862 : Nat := 50642428923550195435319

theorem tailTrace_332862 : CollatzResearch.WordTrace tailWord_332862 prefixEnd_332862 50642428923550195435319 := by
  unfold tailWord_332862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517559315013162143598105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8093649680070198099189893 1517559315013162143598105)
  ·
    refine ⟨1138169486259871607698579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1517559315013162143598105 1138169486259871607698579)
    ·
      refine ⟨1707254229389807411547869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138169486259871607698579 1707254229389807411547869)
      ·
        refine ⟨640220336021177779330451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1707254229389807411547869 640220336021177779330451)
        ·
          refine ⟨960330504031766668995677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640220336021177779330451 960330504031766668995677)
          ·
            refine ⟨360123939011912500873379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 960330504031766668995677 360123939011912500873379)
            ·
              refine ⟨540185908517868751310069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360123939011912500873379 540185908517868751310069)
              ·
                refine ⟨50642428923550195435319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540185908517868751310069 50642428923550195435319)
                ·
                  rfl

theorem cell20_332862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_332862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332862 prefixEnd_332862 := by exact prefixLift 332862
  have htrace : WordTrace (prefixWord ++ tailWord_332862) baseStart_332862 baseEnd_332862 := by
    simpa [prefixWord, tailWord_332862, baseEnd_332862] using wordTrace_append hprefix tailTrace_332862
  have hstable : (prefixWord ++ tailWord_332862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332862).length < 2 ^ (prefixWord ++ tailWord_332862).sum := by decide
  have hdescent : baseEnd_332862 < baseStart_332862 := by decide
  rcases family_descends (prefixWord ++ tailWord_332862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332911 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_332911 : Nat := 118140960795 + 332911 * 2 ^ 59
def prefixEnd_332911 : Nat := 4983230072969 + 3 ^ 40 * 332911 * 2
def baseEnd_332911 : Nat := 151949651705824193672423

theorem tailTrace_332911 : CollatzResearch.WordTrace tailWord_332911 prefixEnd_332911 151949651705824193672423 := by
  unfold tailWord_332911
  simp only [CollatzResearch.WordTrace]
  refine ⟨12142261696927778517318587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8094841131285185678212391 12142261696927778517318587)
  ·
    refine ⟨18213392545391667775977881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12142261696927778517318587 18213392545391667775977881)
    ·
      refine ⟨13660044409043750831983411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18213392545391667775977881 13660044409043750831983411)
      ·
        refine ⟨20490066613565626247975117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13660044409043750831983411 20490066613565626247975117)
        ·
          refine ⟨7683774980087109842990669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20490066613565626247975117 7683774980087109842990669)
          ·
            refine ⟨2881415617532666191121501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7683774980087109842990669 2881415617532666191121501)
            ·
              refine ⟨1080530856574749821670563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2881415617532666191121501 1080530856574749821670563)
              ·
                refine ⟨1620796284862124732505845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080530856574749821670563 1620796284862124732505845)
                ·
                  refine ⟨151949651705824193672423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1620796284862124732505845 151949651705824193672423)
                  ·
                    rfl

theorem cell20_332911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_332911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332911 prefixEnd_332911 := by exact prefixLift 332911
  have htrace : WordTrace (prefixWord ++ tailWord_332911) baseStart_332911 baseEnd_332911 := by
    simpa [prefixWord, tailWord_332911, baseEnd_332911] using wordTrace_append hprefix tailTrace_332911
  have hstable : (prefixWord ++ tailWord_332911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332911).length < 2 ^ (prefixWord ++ tailWord_332911).sum := by decide
  have hdescent : baseEnd_332911 < baseStart_332911 := by decide
  rcases family_descends (prefixWord ++ tailWord_332911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332914 : List Nat := [3, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_332914 : Nat := 118140960795 + 332914 * 2 ^ 59
def prefixEnd_332914 : Nat := 4983230072969 + 3 ^ 40 * 332914 * 2
def baseEnd_332914 : Nat := 151951020987569516572411

theorem tailTrace_332914 : CollatzResearch.WordTrace tailWord_332914 prefixEnd_332914 151951020987569516572411 := by
  unfold tailWord_332914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035592778979227507419449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8094914077277940019785197 3035592778979227507419449)
  ·
    refine ⟨2276694584234420630564587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3035592778979227507419449 2276694584234420630564587)
    ·
      refine ⟨3415041876351630945846881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2276694584234420630564587 3415041876351630945846881)
      ·
        refine ⟨2561281407263723209385161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3415041876351630945846881 2561281407263723209385161)
        ·
          refine ⟨1920961055447792407038871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2561281407263723209385161 1920961055447792407038871)
          ·
            refine ⟨2881441583171688610558307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920961055447792407038871 2881441583171688610558307)
            ·
              refine ⟨4322162374757532915837461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881441583171688610558307 4322162374757532915837461)
              ·
                refine ⟨202601361316759355429881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4322162374757532915837461 202601361316759355429881)
                ·
                  refine ⟨151951020987569516572411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202601361316759355429881 151951020987569516572411)
                  ·
                    rfl

theorem cell20_332914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_332914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332914 prefixEnd_332914 := by exact prefixLift 332914
  have htrace : WordTrace (prefixWord ++ tailWord_332914) baseStart_332914 baseEnd_332914 := by
    simpa [prefixWord, tailWord_332914, baseEnd_332914] using wordTrace_append hprefix tailTrace_332914
  have hstable : (prefixWord ++ tailWord_332914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332914).length < 2 ^ (prefixWord ++ tailWord_332914).sum := by decide
  have hdescent : baseEnd_332914 < baseStart_332914 := by decide
  rcases family_descends (prefixWord ++ tailWord_332914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_332959 : List Nat := [1, 1, 2, 6, 2, 2, 6]
def baseStart_332959 : Nat := 118140960795 + 332959 * 2 ^ 59
def prefixEnd_332959 : Nat := 4983230072969 + 3 ^ 40 * 332959 * 2
def baseEnd_332959 : Nat := 16885728912638817785803

theorem tailTrace_332959 : CollatzResearch.WordTrace tailWord_332959 prefixEnd_332959 16885728912638817785803 := by
  unfold tailWord_332959
  simp only [CollatzResearch.WordTrace]
  refine ⟨12144012400753882715065931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8096008267169255143377287 12144012400753882715065931)
  ·
    refine ⟨18216018601130824072598897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12144012400753882715065931 18216018601130824072598897)
    ·
      refine ⟨13662013950848118054449173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18216018601130824072598897 13662013950848118054449173)
      ·
        refine ⟨640406903946005533802305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13662013950848118054449173 640406903946005533802305)
        ·
          refine ⟨480305177959504150351729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 640406903946005533802305 480305177959504150351729)
          ·
            refine ⟨360228883469628112763797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480305177959504150351729 360228883469628112763797)
            ·
              refine ⟨16885728912638817785803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 360228883469628112763797 16885728912638817785803)
              ·
                rfl

theorem cell20_332959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 6].length) (baseStart_332959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_332959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_332959 prefixEnd_332959 := by exact prefixLift 332959
  have htrace : WordTrace (prefixWord ++ tailWord_332959) baseStart_332959 baseEnd_332959 := by
    simpa [prefixWord, tailWord_332959, baseEnd_332959] using wordTrace_append hprefix tailTrace_332959
  have hstable : (prefixWord ++ tailWord_332959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_332959).length < 2 ^ (prefixWord ++ tailWord_332959).sum := by decide
  have hdescent : baseEnd_332959 < baseStart_332959 := by decide
  rcases family_descends (prefixWord ++ tailWord_332959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333014 : List Nat := [5, 2, 1, 2, 3, 7]
def baseStart_333014 : Nat := 118140960795 + 333014 * 2 ^ 59
def prefixEnd_333014 : Nat := 4983230072969 + 3 ^ 40 * 333014 * 2
def baseEnd_333014 : Nat := 5629506063422726416247

theorem tailTrace_333014 : CollatzResearch.WordTrace tailWord_333014 prefixEnd_333014 5629506063422726416247 := by
  unfold tailWord_333014
  simp only [CollatzResearch.WordTrace]
  refine ⟨759126150972164194269881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8097345610369751405545397 759126150972164194269881)
  ·
    refine ⟨569344613229123145702411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 759126150972164194269881 569344613229123145702411)
    ·
      refine ⟨854016919843684718553617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569344613229123145702411 854016919843684718553617)
      ·
        refine ⟨640512689882763538915213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 854016919843684718553617 640512689882763538915213)
        ·
          refine ⟨240192258706036327093205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 640512689882763538915213 240192258706036327093205)
          ·
            refine ⟨5629506063422726416247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 240192258706036327093205 5629506063422726416247)
            ·
              rfl

theorem cell20_333014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 7].length) (baseStart_333014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333014 prefixEnd_333014 := by exact prefixLift 333014
  have htrace : WordTrace (prefixWord ++ tailWord_333014) baseStart_333014 baseEnd_333014 := by
    simpa [prefixWord, tailWord_333014, baseEnd_333014] using wordTrace_append hprefix tailTrace_333014
  have hstable : (prefixWord ++ tailWord_333014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333014).length < 2 ^ (prefixWord ++ tailWord_333014).sum := by decide
  have hdescent : baseEnd_333014 < baseStart_333014 := by decide
  rcases family_descends (prefixWord ++ tailWord_333014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333080 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_333080 : Nat := 118140960795 + 333080 * 2 ^ 59
def prefixEnd_333080 : Nat := 4983230072969 + 3 ^ 40 * 333080 * 2
def baseEnd_333080 : Nat := 152026787910810717038399

theorem tailTrace_333080 : CollatzResearch.WordTrace tailWord_333080 prefixEnd_333080 152026787910810717038399 := by
  unfold tailWord_333080
  simp only [CollatzResearch.WordTrace]
  refine ⟨6074212816657760190110347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8098950422210346920147129 6074212816657760190110347)
  ·
    refine ⟨9111319224986640285165521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6074212816657760190110347 9111319224986640285165521)
    ·
      refine ⟨6833489418739980213874141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9111319224986640285165521 6833489418739980213874141)
      ·
        refine ⟨2562558532027492580202803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6833489418739980213874141 2562558532027492580202803)
        ·
          refine ⟨3843837798041238870304205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562558532027492580202803 3843837798041238870304205)
          ·
            refine ⟨1441439174265464576364077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3843837798041238870304205 1441439174265464576364077)
            ·
              refine ⟨540539690349549216136529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1441439174265464576364077 540539690349549216136529)
              ·
                refine ⟨405404767762161912102397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540539690349549216136529 405404767762161912102397)
                ·
                  refine ⟨152026787910810717038399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405404767762161912102397 152026787910810717038399)
                  ·
                    rfl

theorem cell20_333080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_333080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333080 prefixEnd_333080 := by exact prefixLift 333080
  have htrace : WordTrace (prefixWord ++ tailWord_333080) baseStart_333080 baseEnd_333080 := by
    simpa [prefixWord, tailWord_333080, baseEnd_333080] using wordTrace_append hprefix tailTrace_333080
  have hstable : (prefixWord ++ tailWord_333080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333080).length < 2 ^ (prefixWord ++ tailWord_333080).sum := by decide
  have hdescent : baseEnd_333080 < baseStart_333080 := by decide
  rcases family_descends (prefixWord ++ tailWord_333080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333117 : List Nat := [1, 4, 1, 5, 2, 1, 1, 3, 2]
def baseStart_333117 : Nat := 118140960795 + 333117 * 2 ^ 59
def prefixEnd_333117 : Nat := 4983230072969 + 3 ^ 40 * 333117 * 2
def baseEnd_333117 : Nat := 152043675719003032804915

theorem tailTrace_333117 : CollatzResearch.WordTrace tailWord_333117 prefixEnd_333117 152043675719003032804915 := by
  unfold tailWord_333117
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149775134181475699317605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8099850089454317132878403 12149775134181475699317605)
  ·
    refine ⟨2278082837659026693622051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12149775134181475699317605 2278082837659026693622051)
    ·
      refine ⟨3417124256488540040433077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278082837659026693622051 3417124256488540040433077)
      ·
        refine ⟨320355399045800628790601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3417124256488540040433077 320355399045800628790601)
        ·
          refine ⟨240266549284350471592951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320355399045800628790601 240266549284350471592951)
          ·
            refine ⟨360399823926525707389427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240266549284350471592951 360399823926525707389427)
            ·
              refine ⟨540599735889788561084141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360399823926525707389427 540599735889788561084141)
              ·
                refine ⟨202724900958670710406553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 540599735889788561084141 202724900958670710406553)
                ·
                  refine ⟨152043675719003032804915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202724900958670710406553 152043675719003032804915)
                  ·
                    rfl

theorem cell20_333117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_333117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333117 prefixEnd_333117 := by exact prefixLift 333117
  have htrace : WordTrace (prefixWord ++ tailWord_333117) baseStart_333117 baseEnd_333117 := by
    simpa [prefixWord, tailWord_333117, baseEnd_333117] using wordTrace_append hprefix tailTrace_333117
  have hstable : (prefixWord ++ tailWord_333117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333117).length < 2 ^ (prefixWord ++ tailWord_333117).sum := by decide
  have hdescent : baseEnd_333117 < baseStart_333117 := by decide
  rcases family_descends (prefixWord ++ tailWord_333117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333121 : List Nat := [1, 2, 5, 2, 1, 1, 3, 3, 2]
def baseStart_333121 : Nat := 118140960795 + 333121 * 2 ^ 59
def prefixEnd_333121 : Nat := 4983230072969 + 3 ^ 40 * 333121 * 2
def baseEnd_333121 : Nat := 152045501427996796671565

theorem tailTrace_333121 : CollatzResearch.WordTrace tailWord_333121 prefixEnd_333121 152045501427996796671565 := by
  unfold tailWord_333121
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149921026166984382463217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8099947350777989588308811 12149921026166984382463217)
  ·
    refine ⟨9112440769625238286847413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12149921026166984382463217 9112440769625238286847413)
    ·
      refine ⟨854291322152366089391945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9112440769625238286847413 854291322152366089391945)
      ·
        refine ⟨640718491614274567043959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 854291322152366089391945 640718491614274567043959)
        ·
          refine ⟨961077737421411850565939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640718491614274567043959 961077737421411850565939)
          ·
            refine ⟨1441616606132117775848909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961077737421411850565939 1441616606132117775848909)
            ·
              refine ⟨540606227299544165943341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1441616606132117775848909 540606227299544165943341)
              ·
                refine ⟨202727335237329062228753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 540606227299544165943341 202727335237329062228753)
                ·
                  refine ⟨152045501427996796671565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202727335237329062228753 152045501427996796671565)
                  ·
                    rfl

theorem cell20_333121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_333121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333121 prefixEnd_333121 := by exact prefixLift 333121
  have htrace : WordTrace (prefixWord ++ tailWord_333121) baseStart_333121 baseEnd_333121 := by
    simpa [prefixWord, tailWord_333121, baseEnd_333121] using wordTrace_append hprefix tailTrace_333121
  have hstable : (prefixWord ++ tailWord_333121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333121).length < 2 ^ (prefixWord ++ tailWord_333121).sum := by decide
  have hdescent : baseEnd_333121 < baseStart_333121 := by decide
  rcases family_descends (prefixWord ++ tailWord_333121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333132 : List Nat := [2, 2, 1, 3, 2, 4, 6]
def baseStart_333132 : Nat := 118140960795 + 333132 * 2 ^ 59
def prefixEnd_333132 : Nat := 4983230072969 + 3 ^ 40 * 333132 * 2
def baseEnd_333132 : Nat := 16894502458636627478317

theorem tailTrace_333132 : CollatzResearch.WordTrace tailWord_333132 prefixEnd_333132 16894502458636627478317 := by
  unfold tailWord_333132
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075161114563566630556825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8100214819418088840742433 6075161114563566630556825)
  ·
    refine ⟨4556370835922674972917619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6075161114563566630556825 4556370835922674972917619)
    ·
      refine ⟨6834556253884012459376429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4556370835922674972917619 6834556253884012459376429)
      ·
        refine ⟨2562958595206504672266161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6834556253884012459376429 2562958595206504672266161)
        ·
          refine ⟨1922218946404878504199621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2562958595206504672266161 1922218946404878504199621)
          ·
            refine ⟨360416052450914719537429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1922218946404878504199621 360416052450914719537429)
            ·
              refine ⟨16894502458636627478317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 360416052450914719537429 16894502458636627478317)
              ·
                rfl

theorem cell20_333132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 6].length) (baseStart_333132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333132 prefixEnd_333132 := by exact prefixLift 333132
  have htrace : WordTrace (prefixWord ++ tailWord_333132) baseStart_333132 baseEnd_333132 := by
    simpa [prefixWord, tailWord_333132, baseEnd_333132] using wordTrace_append hprefix tailTrace_333132
  have hstable : (prefixWord ++ tailWord_333132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333132).length < 2 ^ (prefixWord ++ tailWord_333132).sum := by decide
  have hdescent : baseEnd_333132 < baseStart_333132 := by decide
  rcases family_descends (prefixWord ++ tailWord_333132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333139 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 3]
def baseStart_333139 : Nat := 118140960795 + 333139 * 2 ^ 59
def prefixEnd_333139 : Nat := 4983230072969 + 3 ^ 40 * 333139 * 2
def baseEnd_333139 : Nat := 152053717118468734071491

theorem tailTrace_333139 : CollatzResearch.WordTrace tailWord_333139 prefixEnd_333139 152053717118468734071491 := by
  unfold tailWord_333139
  simp only [CollatzResearch.WordTrace]
  refine ⟨12150577540101773456618471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8100385026734515637745647 12150577540101773456618471)
  ·
    refine ⟨18225866310152660184927707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12150577540101773456618471 18225866310152660184927707)
    ·
      refine ⟨27338799465228990277391561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18225866310152660184927707 27338799465228990277391561)
      ·
        refine ⟨20504099598921742708043671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27338799465228990277391561 20504099598921742708043671)
        ·
          refine ⟨30756149398382614062065507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20504099598921742708043671 30756149398382614062065507)
          ·
            refine ⟨46134224097573921093098261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30756149398382614062065507 46134224097573921093098261)
            ·
              refine ⟨2162541754573777551238981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46134224097573921093098261 2162541754573777551238981)
              ·
                refine ⟨405476578982583290857309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2162541754573777551238981 405476578982583290857309)
                ·
                  refine ⟨152053717118468734071491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405476578982583290857309 152053717118468734071491)
                  ·
                    rfl

theorem cell20_333139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_333139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333139 prefixEnd_333139 := by exact prefixLift 333139
  have htrace : WordTrace (prefixWord ++ tailWord_333139) baseStart_333139 baseEnd_333139 := by
    simpa [prefixWord, tailWord_333139, baseEnd_333139] using wordTrace_append hprefix tailTrace_333139
  have hstable : (prefixWord ++ tailWord_333139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333139).length < 2 ^ (prefixWord ++ tailWord_333139).sum := by decide
  have hdescent : baseEnd_333139 < baseStart_333139 := by decide
  rcases family_descends (prefixWord ++ tailWord_333139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333156 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_333156 : Nat := 118140960795 + 333156 * 2 ^ 59
def prefixEnd_333156 : Nat := 4983230072969 + 3 ^ 40 * 333156 * 2
def baseEnd_333156 : Nat := 152061476381692230504755

theorem tailTrace_333156 : CollatzResearch.WordTrace tailWord_333156 prefixEnd_333156 152061476381692230504755 := by
  unfold tailWord_333156
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075598790520092679993661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8100798387360123573324881 6075598790520092679993661)
  ·
    refine ⟨2278349546445034754997623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6075598790520092679993661 2278349546445034754997623)
    ·
      refine ⟨3417524319667552132496435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278349546445034754997623 3417524319667552132496435)
      ·
        refine ⟨5126286479501328198744653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3417524319667552132496435 5126286479501328198744653)
        ·
          refine ⟨1922357429812998074529245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5126286479501328198744653 1922357429812998074529245)
          ·
            refine ⟨720884036179874277948467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1922357429812998074529245 720884036179874277948467)
            ·
              refine ⟨1081326054269811416922701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720884036179874277948467 1081326054269811416922701)
              ·
                refine ⟨405497270351179281346013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1081326054269811416922701 405497270351179281346013)
                ·
                  refine ⟨152061476381692230504755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405497270351179281346013 152061476381692230504755)
                  ·
                    rfl

theorem cell20_333156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_333156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333156 prefixEnd_333156 := by exact prefixLift 333156
  have htrace : WordTrace (prefixWord ++ tailWord_333156) baseStart_333156 baseEnd_333156 := by
    simpa [prefixWord, tailWord_333156, baseEnd_333156] using wordTrace_append hprefix tailTrace_333156
  have hstable : (prefixWord ++ tailWord_333156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333156).length < 2 ^ (prefixWord ++ tailWord_333156).sum := by decide
  have hdescent : baseEnd_333156 < baseStart_333156 := by decide
  rcases family_descends (prefixWord ++ tailWord_333156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333191 : List Nat := [1, 1, 4, 2, 2, 10]
def baseStart_333191 : Nat := 118140960795 + 333191 * 2 ^ 59
def prefixEnd_333191 : Nat := 4983230072969 + 3 ^ 40 * 333191 * 2
def baseEnd_333191 : Nat := 5632498197606950531035

theorem tailTrace_333191 : CollatzResearch.WordTrace tailWord_333191 prefixEnd_333191 5632498197606950531035 := by
  unfold tailWord_333191
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152474135913386337511427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8101649423942257558340951 12152474135913386337511427)
  ·
    refine ⟨18228711203870079506267141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12152474135913386337511427 18228711203870079506267141)
    ·
      refine ⟨3417883350725639907425089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18228711203870079506267141 3417883350725639907425089)
      ·
        refine ⟨2563412513044229930568817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3417883350725639907425089 2563412513044229930568817)
        ·
          refine ⟨1922559384783172447926613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563412513044229930568817 1922559384783172447926613)
          ·
            refine ⟨5632498197606950531035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1922559384783172447926613 5632498197606950531035)
            ·
              rfl

theorem cell20_333191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 10].length) (baseStart_333191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333191 prefixEnd_333191 := by exact prefixLift 333191
  have htrace : WordTrace (prefixWord ++ tailWord_333191) baseStart_333191 baseEnd_333191 := by
    simpa [prefixWord, tailWord_333191, baseEnd_333191] using wordTrace_append hprefix tailTrace_333191
  have hstable : (prefixWord ++ tailWord_333191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333191).length < 2 ^ (prefixWord ++ tailWord_333191).sum := by decide
  have hdescent : baseEnd_333191 < baseStart_333191 := by decide
  rcases family_descends (prefixWord ++ tailWord_333191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333201 : List Nat := [1, 2, 2, 1, 1, 1, 2, 8, 2]
def baseStart_333201 : Nat := 118140960795 + 333201 * 2 ^ 59
def prefixEnd_333201 : Nat := 4983230072969 + 3 ^ 40 * 333201 * 2
def baseEnd_333201 : Nat := 152082015607872074004571

theorem tailTrace_333201 : CollatzResearch.WordTrace tailWord_333201 prefixEnd_333201 152082015607872074004571 := by
  unfold tailWord_333201
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152838865877158045375457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8101892577251438696916971 12152838865877158045375457)
  ·
    refine ⟨9114629149407868534031593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12152838865877158045375457 9114629149407868534031593)
    ·
      refine ⟨6835971862055901400523695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9114629149407868534031593 6835971862055901400523695)
      ·
        refine ⟨10253957793083852100785543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6835971862055901400523695 10253957793083852100785543)
        ·
          refine ⟨15380936689625778151178315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10253957793083852100785543 15380936689625778151178315)
          ·
            refine ⟨23071405034438667226767473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15380936689625778151178315 23071405034438667226767473)
            ·
              refine ⟨17303553775829000420075605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23071405034438667226767473 17303553775829000420075605)
              ·
                refine ⟨202776020810496098672761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 17303553775829000420075605 202776020810496098672761)
                ·
                  refine ⟨152082015607872074004571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202776020810496098672761 152082015607872074004571)
                  ·
                    rfl

theorem cell20_333201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_333201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333201 prefixEnd_333201 := by exact prefixLift 333201
  have htrace : WordTrace (prefixWord ++ tailWord_333201) baseStart_333201 baseEnd_333201 := by
    simpa [prefixWord, tailWord_333201, baseEnd_333201] using wordTrace_append hprefix tailTrace_333201
  have hstable : (prefixWord ++ tailWord_333201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333201).length < 2 ^ (prefixWord ++ tailWord_333201).sum := by decide
  have hdescent : baseEnd_333201 < baseStart_333201 := by decide
  rcases family_descends (prefixWord ++ tailWord_333201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333277 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_333277 : Nat := 118140960795 + 333277 * 2 ^ 59
def prefixEnd_333277 : Nat := 4983230072969 + 3 ^ 40 * 333277 * 2
def baseEnd_333277 : Nat := 152116704078753587470927

theorem tailTrace_333277 : CollatzResearch.WordTrace tailWord_333277 prefixEnd_333277 152116704078753587470927 := by
  unfold tailWord_333277
  simp only [CollatzResearch.WordTrace]
  refine ⟨12155610813601823025142085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8103740542401215350094723 12155610813601823025142085)
  ·
    refine ⟨2279177027550341817214141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12155610813601823025142085 2279177027550341817214141)
    ·
      refine ⟨854691385331378181455303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2279177027550341817214141 854691385331378181455303)
      ·
        refine ⟨1282037077997067272182955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854691385331378181455303 1282037077997067272182955)
        ·
          refine ⟨1923055616995600908274433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282037077997067272182955 1923055616995600908274433)
          ·
            refine ⟨1442291712746700681205825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1923055616995600908274433 1442291712746700681205825)
            ·
              refine ⟨1081718784560025510904369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442291712746700681205825 1081718784560025510904369)
              ·
                refine ⟨811289088420019133178277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081718784560025510904369 811289088420019133178277)
                ·
                  refine ⟨152116704078753587470927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811289088420019133178277 152116704078753587470927)
                  ·
                    rfl

theorem cell20_333277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_333277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333277 prefixEnd_333277 := by exact prefixLift 333277
  have htrace : WordTrace (prefixWord ++ tailWord_333277) baseStart_333277 baseEnd_333277 := by
    simpa [prefixWord, tailWord_333277, baseEnd_333277] using wordTrace_append hprefix tailTrace_333277
  have hstable : (prefixWord ++ tailWord_333277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333277).length < 2 ^ (prefixWord ++ tailWord_333277).sum := by decide
  have hdescent : baseEnd_333277 < baseStart_333277 := by decide
  rcases family_descends (prefixWord ++ tailWord_333277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333290 : List Nat := [3, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_333290 : Nat := 118140960795 + 333290 * 2 ^ 59
def prefixEnd_333290 : Nat := 4983230072969 + 3 ^ 40 * 333290 * 2
def baseEnd_333290 : Nat := 152122637632983320037541

theorem tailTrace_333290 : CollatzResearch.WordTrace tailWord_333290 prefixEnd_333290 152122637632983320037541 := by
  unfold tailWord_333290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039021240638681561341331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8104056641703150830243549 3039021240638681561341331)
  ·
    refine ⟨4558531860958022342011997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3039021240638681561341331 4558531860958022342011997)
    ·
      refine ⟨1709449447859258378254499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4558531860958022342011997 1709449447859258378254499)
      ·
        refine ⟨2564174171788887567381749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709449447859258378254499 2564174171788887567381749)
        ·
          refine ⟨240391328605208209442039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2564174171788887567381749 240391328605208209442039)
          ·
            refine ⟨360586992907812314163059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240391328605208209442039 360586992907812314163059)
            ·
              refine ⟨540880489361718471244589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360586992907812314163059 540880489361718471244589)
              ·
                refine ⟨202830183510644426716721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 540880489361718471244589 202830183510644426716721)
                ·
                  refine ⟨152122637632983320037541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202830183510644426716721 152122637632983320037541)
                  ·
                    rfl

theorem cell20_333290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_333290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333290 prefixEnd_333290 := by exact prefixLift 333290
  have htrace : WordTrace (prefixWord ++ tailWord_333290) baseStart_333290 baseEnd_333290 := by
    simpa [prefixWord, tailWord_333290, baseEnd_333290] using wordTrace_append hprefix tailTrace_333290
  have hstable : (prefixWord ++ tailWord_333290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333290).length < 2 ^ (prefixWord ++ tailWord_333290).sum := by decide
  have hdescent : baseEnd_333290 < baseStart_333290 := by decide
  rcases family_descends (prefixWord ++ tailWord_333290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333301 : List Nat := [1, 3, 5, 1, 1, 3, 6]
def baseStart_333301 : Nat := 118140960795 + 333301 * 2 ^ 59
def prefixEnd_333301 : Nat := 4983230072969 + 3 ^ 40 * 333301 * 2
def baseEnd_333301 : Nat := 16903073148079574518981

theorem tailTrace_333301 : CollatzResearch.WordTrace tailWord_333301 prefixEnd_333301 16903073148079574518981 := by
  unfold tailWord_333301
  simp only [CollatzResearch.WordTrace]
  refine ⟨12156486165514875124015757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8104324110343250082677171 12156486165514875124015757)
  ·
    refine ⟨4558682312068078171505909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12156486165514875124015757 4558682312068078171505909)
    ·
      refine ⟨427376466756382328578679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4558682312068078171505909 427376466756382328578679)
      ·
        refine ⟨641064700134573492868019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427376466756382328578679 641064700134573492868019)
        ·
          refine ⟨961597050201860239302029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641064700134573492868019 961597050201860239302029)
          ·
            refine ⟨360598893825697589738261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 961597050201860239302029 360598893825697589738261)
            ·
              refine ⟨16903073148079574518981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 360598893825697589738261 16903073148079574518981)
              ·
                rfl

theorem cell20_333301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 6].length) (baseStart_333301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333301 prefixEnd_333301 := by exact prefixLift 333301
  have htrace : WordTrace (prefixWord ++ tailWord_333301) baseStart_333301 baseEnd_333301 := by
    simpa [prefixWord, tailWord_333301, baseEnd_333301] using wordTrace_append hprefix tailTrace_333301
  have hstable : (prefixWord ++ tailWord_333301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333301).length < 2 ^ (prefixWord ++ tailWord_333301).sum := by decide
  have hdescent : baseEnd_333301 < baseStart_333301 := by decide
  rcases family_descends (prefixWord ++ tailWord_333301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333322 : List Nat := [3, 1, 2, 2, 2, 3, 2, 5]
def baseStart_333322 : Nat := 118140960795 + 333322 * 2 ^ 59
def prefixEnd_333322 : Nat := 4983230072969 + 3 ^ 40 * 333322 * 2
def baseEnd_333322 : Nat := 50712414434977810323581

theorem tailTrace_333322 : CollatzResearch.WordTrace tailWord_333322 prefixEnd_333322 50712414434977810323581 := by
  unfold tailWord_333322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039313024609698927632555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8104834732292530473686813 3039313024609698927632555)
  ·
    refine ⟨4558969536914548391448833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3039313024609698927632555 4558969536914548391448833)
    ·
      refine ⟨3419227152685911293586625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4558969536914548391448833 3419227152685911293586625)
      ·
        refine ⟨2564420364514433470189969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3419227152685911293586625 2564420364514433470189969)
        ·
          refine ⟨1923315273385825102642477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564420364514433470189969 1923315273385825102642477)
          ·
            refine ⟨721243227519684413490929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1923315273385825102642477 721243227519684413490929)
            ·
              refine ⟨540932420639763310118197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721243227519684413490929 540932420639763310118197)
              ·
                refine ⟨50712414434977810323581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540932420639763310118197 50712414434977810323581)
                ·
                  rfl

theorem cell20_333322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_333322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333322 prefixEnd_333322 := by exact prefixLift 333322
  have htrace : WordTrace (prefixWord ++ tailWord_333322) baseStart_333322 baseEnd_333322 := by
    simpa [prefixWord, tailWord_333322, baseEnd_333322] using wordTrace_append hprefix tailTrace_333322
  have hstable : (prefixWord ++ tailWord_333322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333322).length < 2 ^ (prefixWord ++ tailWord_333322).sum := by decide
  have hdescent : baseEnd_333322 < baseStart_333322 := by decide
  rcases family_descends (prefixWord ++ tailWord_333322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333329 : List Nat := [1, 2, 2, 1, 1, 2, 5, 3, 3]
def baseStart_333329 : Nat := 118140960795 + 333329 * 2 ^ 59
def prefixEnd_333329 : Nat := 4983230072969 + 3 ^ 40 * 333329 * 2
def baseEnd_333329 : Nat := 152140438295672517737381

theorem tailTrace_333329 : CollatzResearch.WordTrace tailWord_333329 prefixEnd_333329 152140438295672517737381 := by
  unfold tailWord_333329
  simp only [CollatzResearch.WordTrace]
  refine ⟨12157507409413435906035041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8105004939608957270690027 12157507409413435906035041)
  ·
    refine ⟨9118130557060076929526281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12157507409413435906035041 9118130557060076929526281)
    ·
      refine ⟨6838597917795057697144711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9118130557060076929526281 6838597917795057697144711)
      ·
        refine ⟨10257896876692586545717067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6838597917795057697144711 10257896876692586545717067)
        ·
          refine ⟨15386845315038879818575601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10257896876692586545717067 15386845315038879818575601)
          ·
            refine ⟨11540133986279159863931701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15386845315038879818575601 11540133986279159863931701)
            ·
              refine ⟨1081887561213671237243597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11540133986279159863931701 1081887561213671237243597)
              ·
                refine ⟨405707835455126713966349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1081887561213671237243597 405707835455126713966349)
                ·
                  refine ⟨152140438295672517737381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405707835455126713966349 152140438295672517737381)
                  ·
                    rfl

theorem cell20_333329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_333329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333329 prefixEnd_333329 := by exact prefixLift 333329
  have htrace : WordTrace (prefixWord ++ tailWord_333329) baseStart_333329 baseEnd_333329 := by
    simpa [prefixWord, tailWord_333329, baseEnd_333329] using wordTrace_append hprefix tailTrace_333329
  have hstable : (prefixWord ++ tailWord_333329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333329).length < 2 ^ (prefixWord ++ tailWord_333329).sum := by decide
  have hdescent : baseEnd_333329 < baseStart_333329 := by decide
  rcases family_descends (prefixWord ++ tailWord_333329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333343 : List Nat := [1, 1, 2, 4, 1, 1, 4, 6]
def baseStart_333343 : Nat := 118140960795 + 333343 * 2 ^ 59
def prefixEnd_333343 : Nat := 4983230072969 + 3 ^ 40 * 333343 * 2
def baseEnd_333343 : Nat := 50715609425716897090219

theorem tailTrace_333343 : CollatzResearch.WordTrace tailWord_333343 prefixEnd_333343 50715609425716897090219 := by
  unfold tailWord_333343
  simp only [CollatzResearch.WordTrace]
  refine ⟨12158018031362716297044683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8105345354241810864696455 12158018031362716297044683)
  ·
    refine ⟨18237027047044074445567025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12158018031362716297044683 18237027047044074445567025)
    ·
      refine ⟨13677770285283055834175269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18237027047044074445567025 13677770285283055834175269)
      ·
        refine ⟨2564581928490572968907863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13677770285283055834175269 2564581928490572968907863)
        ·
          refine ⟨3846872892735859453361795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564581928490572968907863 3846872892735859453361795)
          ·
            refine ⟨5770309339103789180042693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846872892735859453361795 5770309339103789180042693)
            ·
              refine ⟨1081933001081960471258005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5770309339103789180042693 1081933001081960471258005)
              ·
                refine ⟨50715609425716897090219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1081933001081960471258005 50715609425716897090219)
                ·
                  rfl

theorem cell20_333343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_333343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333343 prefixEnd_333343 := by exact prefixLift 333343
  have htrace : WordTrace (prefixWord ++ tailWord_333343) baseStart_333343 baseEnd_333343 := by
    simpa [prefixWord, tailWord_333343, baseEnd_333343] using wordTrace_append hprefix tailTrace_333343
  have hstable : (prefixWord ++ tailWord_333343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333343).length < 2 ^ (prefixWord ++ tailWord_333343).sum := by decide
  have hdescent : baseEnd_333343 < baseStart_333343 := by decide
  rcases family_descends (prefixWord ++ tailWord_333343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333367 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 3]
def baseStart_333367 : Nat := 118140960795 + 333367 * 2 ^ 59
def prefixEnd_333367 : Nat := 4983230072969 + 3 ^ 40 * 333367 * 2
def baseEnd_333367 : Nat := 152157782531113274470559

theorem tailTrace_333367 : CollatzResearch.WordTrace tailWord_333367 prefixEnd_333367 152157782531113274470559 := by
  unfold tailWord_333367
  simp only [CollatzResearch.WordTrace]
  refine ⟨12158893383275768395918355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8105928922183845597278903 12158893383275768395918355)
  ·
    refine ⟨18238340074913652593877533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12158893383275768395918355 18238340074913652593877533)
    ·
      refine ⟨6839377528092619722704075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18238340074913652593877533 6839377528092619722704075)
      ·
        refine ⟨10259066292138929584056113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6839377528092619722704075 10259066292138929584056113)
        ·
          refine ⟨7694299719104197188042085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10259066292138929584056113 7694299719104197188042085)
          ·
            refine ⟨1442681197332036972757891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7694299719104197188042085 1442681197332036972757891)
            ·
              refine ⟨2164021795998055459136837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442681197332036972757891 2164021795998055459136837)
              ·
                refine ⟨405754086749635398588157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2164021795998055459136837 405754086749635398588157)
                ·
                  refine ⟨152157782531113274470559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405754086749635398588157 152157782531113274470559)
                  ·
                    rfl

theorem cell20_333367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_333367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333367 prefixEnd_333367 := by exact prefixLift 333367
  have htrace : WordTrace (prefixWord ++ tailWord_333367) baseStart_333367 baseEnd_333367 := by
    simpa [prefixWord, tailWord_333367, baseEnd_333367] using wordTrace_append hprefix tailTrace_333367
  have hstable : (prefixWord ++ tailWord_333367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333367).length < 2 ^ (prefixWord ++ tailWord_333367).sum := by decide
  have hdescent : baseEnd_333367 < baseStart_333367 := by decide
  rcases family_descends (prefixWord ++ tailWord_333367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333422 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_333422 : Nat := 118140960795 + 333422 * 2 ^ 59
def prefixEnd_333422 : Nat := 4983230072969 + 3 ^ 40 * 333422 * 2
def baseEnd_333422 : Nat := 152182886029777527637001

theorem tailTrace_333422 : CollatzResearch.WordTrace tailWord_333422 prefixEnd_333422 152182886029777527637001 := by
  unfold tailWord_333422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520112424759564098646315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8107266265384341859447013 1520112424759564098646315)
  ·
    refine ⟨2280168637139346147969473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1520112424759564098646315 2280168637139346147969473)
    ·
      refine ⟨1710126477854509610977105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2280168637139346147969473 1710126477854509610977105)
      ·
        refine ⟨1282594858390882208232829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1710126477854509610977105 1282594858390882208232829)
        ·
          refine ⟨480973071896580828087311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1282594858390882208232829 480973071896580828087311)
          ·
            refine ⟨721459607844871242130967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480973071896580828087311 721459607844871242130967)
            ·
              refine ⟨1082189411767306863196451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721459607844871242130967 1082189411767306863196451)
              ·
                refine ⟨1623284117650960294794677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082189411767306863196451 1623284117650960294794677)
                ·
                  refine ⟨152182886029777527637001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1623284117650960294794677 152182886029777527637001)
                  ·
                    rfl

theorem cell20_333422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_333422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333422 prefixEnd_333422 := by exact prefixLift 333422
  have htrace : WordTrace (prefixWord ++ tailWord_333422) baseStart_333422 baseEnd_333422 := by
    simpa [prefixWord, tailWord_333422, baseEnd_333422] using wordTrace_append hprefix tailTrace_333422
  have hstable : (prefixWord ++ tailWord_333422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333422).length < 2 ^ (prefixWord ++ tailWord_333422).sum := by decide
  have hdescent : baseEnd_333422 < baseStart_333422 := by decide
  rcases family_descends (prefixWord ++ tailWord_333422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333429 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_333429 : Nat := 118140960795 + 333429 * 2 ^ 59
def prefixEnd_333429 : Nat := 4983230072969 + 3 ^ 40 * 333429 * 2
def baseEnd_333429 : Nat := 152186081020516614403639

theorem tailTrace_333429 : CollatzResearch.WordTrace tailWord_333429 prefixEnd_333429 152186081020516614403639 := by
  unfold tailWord_333429
  simp only [CollatzResearch.WordTrace]
  refine ⟨12161154709051152984675341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8107436472700768656450227 12161154709051152984675341)
  ·
    refine ⟨4560433015894182369253253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12161154709051152984675341 4560433015894182369253253)
    ·
      refine ⟨855081190480159194234985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4560433015894182369253253 855081190480159194234985)
      ·
        refine ⟨641310892860119395676239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 855081190480159194234985 641310892860119395676239)
        ·
          refine ⟨961966339290179093514359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641310892860119395676239 961966339290179093514359)
          ·
            refine ⟨1442949508935268640271539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961966339290179093514359 1442949508935268640271539)
            ·
              refine ⟨2164424263402902960407309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442949508935268640271539 2164424263402902960407309)
              ·
                refine ⟨811659098776088610152741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2164424263402902960407309 811659098776088610152741)
                ·
                  refine ⟨152186081020516614403639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811659098776088610152741 152186081020516614403639)
                  ·
                    rfl

theorem cell20_333429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_333429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333429 prefixEnd_333429 := by exact prefixLift 333429
  have htrace : WordTrace (prefixWord ++ tailWord_333429) baseStart_333429 baseEnd_333429 := by
    simpa [prefixWord, tailWord_333429, baseEnd_333429] using wordTrace_append hprefix tailTrace_333429
  have hstable : (prefixWord ++ tailWord_333429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333429).length < 2 ^ (prefixWord ++ tailWord_333429).sum := by decide
  have hdescent : baseEnd_333429 < baseStart_333429 := by decide
  rcases family_descends (prefixWord ++ tailWord_333429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333480 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 4]
def baseStart_333480 : Nat := 118140960795 + 333480 * 2 ^ 59
def prefixEnd_333480 : Nat := 4983230072969 + 3 ^ 40 * 333480 * 2
def baseEnd_333480 : Nat := 152209358810187103703431

theorem tailTrace_333480 : CollatzResearch.WordTrace tailWord_333480 prefixEnd_333480 152209358810187103703431 := by
  unfold tailWord_333480
  simp only [CollatzResearch.WordTrace]
  refine ⟨6081507415933194347390947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8108676554577592463187929 6081507415933194347390947)
  ·
    refine ⟨9122261123899791521086421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6081507415933194347390947 9122261123899791521086421)
    ·
      refine ⟨213802995091401363775463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9122261123899791521086421 213802995091401363775463)
      ·
        refine ⟨320704492637102045663195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213802995091401363775463 320704492637102045663195)
        ·
          refine ⟨481056738955653068494793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320704492637102045663195 481056738955653068494793)
          ·
            refine ⟨360792554216739801371095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481056738955653068494793 360792554216739801371095)
            ·
              refine ⟨541188831325109702056643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360792554216739801371095 541188831325109702056643)
              ·
                refine ⟨811783246987664553084965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541188831325109702056643 811783246987664553084965)
                ·
                  refine ⟨152209358810187103703431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811783246987664553084965 152209358810187103703431)
                  ·
                    rfl

theorem cell20_333480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_333480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333480 prefixEnd_333480 := by exact prefixLift 333480
  have htrace : WordTrace (prefixWord ++ tailWord_333480) baseStart_333480 baseEnd_333480 := by
    simpa [prefixWord, tailWord_333480, baseEnd_333480] using wordTrace_append hprefix tailTrace_333480
  have hstable : (prefixWord ++ tailWord_333480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333480).length < 2 ^ (prefixWord ++ tailWord_333480).sum := by decide
  have hdescent : baseEnd_333480 < baseStart_333480 := by decide
  rcases family_descends (prefixWord ++ tailWord_333480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333488 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_333488 : Nat := 118140960795 + 333488 * 2 ^ 59
def prefixEnd_333488 : Nat := 4983230072969 + 3 ^ 40 * 333488 * 2
def baseEnd_333488 : Nat := 152213010228174631436731

theorem tailTrace_333488 : CollatzResearch.WordTrace tailWord_333488 prefixEnd_333488 152213010228174631436731 := by
  unfold tailWord_333488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6081653307918703030536559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8108871077224937374048745 6081653307918703030536559)
  ·
    refine ⟨9122479961878054545804839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6081653307918703030536559 9122479961878054545804839)
    ·
      refine ⟨13683719942817081818707259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9122479961878054545804839 13683719942817081818707259)
      ·
        refine ⟨20525579914225622728060889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13683719942817081818707259 20525579914225622728060889)
        ·
          refine ⟨15394184935669217046045667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20525579914225622728060889 15394184935669217046045667)
          ·
            refine ⟨23091277403503825569068501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15394184935669217046045667 23091277403503825569068501)
            ·
              refine ⟨541201814144620911775043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23091277403503825569068501 541201814144620911775043)
              ·
                refine ⟨811802721216931367662565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541201814144620911775043 811802721216931367662565)
                ·
                  refine ⟨152213010228174631436731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811802721216931367662565 152213010228174631436731)
                  ·
                    rfl

theorem cell20_333488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_333488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333488 prefixEnd_333488 := by exact prefixLift 333488
  have htrace : WordTrace (prefixWord ++ tailWord_333488) baseStart_333488 baseEnd_333488 := by
    simpa [prefixWord, tailWord_333488, baseEnd_333488] using wordTrace_append hprefix tailTrace_333488
  have hstable : (prefixWord ++ tailWord_333488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333488).length < 2 ^ (prefixWord ++ tailWord_333488).sum := by decide
  have hdescent : baseEnd_333488 < baseStart_333488 := by decide
  rcases family_descends (prefixWord ++ tailWord_333488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333494 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_333494 : Nat := 118140960795 + 333494 * 2 ^ 59
def prefixEnd_333494 : Nat := 4983230072969 + 3 ^ 40 * 333494 * 2
def baseEnd_333494 : Nat := 152215748791665277236707

theorem tailTrace_333494 : CollatzResearch.WordTrace tailWord_333494 prefixEnd_333494 152215748791665277236707 := by
  unfold tailWord_333494
  simp only [CollatzResearch.WordTrace]
  refine ⟨760220340863479317861971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8109016969210446057194357 760220340863479317861971)
  ·
    refine ⟨1140330511295218976792957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 760220340863479317861971 1140330511295218976792957)
    ·
      refine ⟨427623941735707116297359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1140330511295218976792957 427623941735707116297359)
      ·
        refine ⟨641435912603560674446039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427623941735707116297359 641435912603560674446039)
        ·
          refine ⟨962153868905341011669059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641435912603560674446039 962153868905341011669059)
          ·
            refine ⟨1443230803358011517503589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962153868905341011669059 1443230803358011517503589)
            ·
              refine ⟨270605775629627159531923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1443230803358011517503589 270605775629627159531923)
              ·
                refine ⟨405908663444440739297885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270605775629627159531923 405908663444440739297885)
                ·
                  refine ⟨152215748791665277236707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405908663444440739297885 152215748791665277236707)
                  ·
                    rfl

theorem cell20_333494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_333494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333494 prefixEnd_333494 := by exact prefixLift 333494
  have htrace : WordTrace (prefixWord ++ tailWord_333494) baseStart_333494 baseEnd_333494 := by
    simpa [prefixWord, tailWord_333494, baseEnd_333494] using wordTrace_append hprefix tailTrace_333494
  have hstable : (prefixWord ++ tailWord_333494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333494).length < 2 ^ (prefixWord ++ tailWord_333494).sum := by decide
  have hdescent : baseEnd_333494 < baseStart_333494 := by decide
  rcases family_descends (prefixWord ++ tailWord_333494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333495 : List Nat := [1, 1, 3, 1, 5, 1, 1, 7]
def baseStart_333495 : Nat := 118140960795 + 333495 * 2 ^ 59
def prefixEnd_333495 : Nat := 4983230072969 + 3 ^ 40 * 333495 * 2
def baseEnd_333495 : Nat := 50738735072971239401123

theorem tailTrace_333495 : CollatzResearch.WordTrace tailWord_333495 prefixEnd_333495 50738735072971239401123 := by
  unfold tailWord_333495
  simp only [CollatzResearch.WordTrace]
  refine ⟨12163561926812046256577939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8109041284541364171051959 12163561926812046256577939)
  ·
    refine ⟨18245342890218069384866909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12163561926812046256577939 18245342890218069384866909)
    ·
      refine ⟨6842003583831776019325091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18245342890218069384866909 6842003583831776019325091)
      ·
        refine ⟨10263005375747664028987637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6842003583831776019325091 10263005375747664028987637)
        ·
          refine ⟨962156753976343502717591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10263005375747664028987637 962156753976343502717591)
          ·
            refine ⟨1443235130964515254076387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962156753976343502717591 1443235130964515254076387)
            ·
              refine ⟨2164852696446772881114581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443235130964515254076387 2164852696446772881114581)
              ·
                refine ⟨50738735072971239401123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2164852696446772881114581 50738735072971239401123)
                ·
                  rfl

theorem cell20_333495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_333495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333495 prefixEnd_333495 := by exact prefixLift 333495
  have htrace : WordTrace (prefixWord ++ tailWord_333495) baseStart_333495 baseEnd_333495 := by
    simpa [prefixWord, tailWord_333495, baseEnd_333495] using wordTrace_append hprefix tailTrace_333495
  have hstable : (prefixWord ++ tailWord_333495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333495).length < 2 ^ (prefixWord ++ tailWord_333495).sum := by decide
  have hdescent : baseEnd_333495 < baseStart_333495 := by decide
  rcases family_descends (prefixWord ++ tailWord_333495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333498 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_333498 : Nat := 118140960795 + 333498 * 2 ^ 59
def prefixEnd_333498 : Nat := 4983230072969 + 3 ^ 40 * 333498 * 2
def baseEnd_333498 : Nat := 152217574500659041103357

theorem tailTrace_333498 : CollatzResearch.WordTrace tailWord_333498 prefixEnd_333498 152217574500659041103357 := by
  unfold tailWord_333498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3040917836450294442234287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8109114230534118512624765 3040917836450294442234287)
  ·
    refine ⟨4561376754675441663351431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3040917836450294442234287 4561376754675441663351431)
    ·
      refine ⟨6842065132013162495027147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4561376754675441663351431 6842065132013162495027147)
      ·
        refine ⟨10263097698019743742540721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6842065132013162495027147 10263097698019743742540721)
        ·
          refine ⟨7697323273514807806905541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10263097698019743742540721 7697323273514807806905541)
          ·
            refine ⟨1443248113784026463794789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7697323273514807806905541 1443248113784026463794789)
            ·
              refine ⟨270609021334504961961523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1443248113784026463794789 270609021334504961961523)
              ·
                refine ⟨405913532001757442942285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270609021334504961961523 405913532001757442942285)
                ·
                  refine ⟨152217574500659041103357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405913532001757442942285 152217574500659041103357)
                  ·
                    rfl

theorem cell20_333498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_333498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333498 prefixEnd_333498 := by exact prefixLift 333498
  have htrace : WordTrace (prefixWord ++ tailWord_333498) baseStart_333498 baseEnd_333498 := by
    simpa [prefixWord, tailWord_333498, baseEnd_333498] using wordTrace_append hprefix tailTrace_333498
  have hstable : (prefixWord ++ tailWord_333498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333498).length < 2 ^ (prefixWord ++ tailWord_333498).sum := by decide
  have hdescent : baseEnd_333498 < baseStart_333498 := by decide
  rcases family_descends (prefixWord ++ tailWord_333498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333564 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_333564 : Nat := 118140960795 + 333564 * 2 ^ 59
def prefixEnd_333564 : Nat := 4983230072969 + 3 ^ 40 * 333564 * 2
def baseEnd_333564 : Nat := 152247698699056144903087

theorem tailTrace_333564 : CollatzResearch.WordTrace tailWord_333564 prefixEnd_333564 152247698699056144903087 := by
  unfold tailWord_333564
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083039281781035520419873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8110719042374714027226497 6083039281781035520419873)
  ·
    refine ⟨4562279461335776640314905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6083039281781035520419873 4562279461335776640314905)
    ·
      refine ⟨3421709596001832480236179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4562279461335776640314905 3421709596001832480236179)
      ·
        refine ⟨5132564394002748720354269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3421709596001832480236179 5132564394002748720354269)
        ·
          refine ⟨1924711647751030770132851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5132564394002748720354269 1924711647751030770132851)
          ·
            refine ⟨2887067471626546155199277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924711647751030770132851 2887067471626546155199277)
            ·
              refine ⟨1082650301859954808199729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2887067471626546155199277 1082650301859954808199729)
              ·
                refine ⟨811987726394966106149797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1082650301859954808199729 811987726394966106149797)
                ·
                  refine ⟨152247698699056144903087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 811987726394966106149797 152247698699056144903087)
                  ·
                    rfl

theorem cell20_333564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_333564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333564 prefixEnd_333564 := by exact prefixLift 333564
  have htrace : WordTrace (prefixWord ++ tailWord_333564) baseStart_333564 baseEnd_333564 := by
    simpa [prefixWord, tailWord_333564, baseEnd_333564] using wordTrace_append hprefix tailTrace_333564
  have hstable : (prefixWord ++ tailWord_333564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333564).length < 2 ^ (prefixWord ++ tailWord_333564).sum := by decide
  have hdescent : baseEnd_333564 < baseStart_333564 := by decide
  rcases family_descends (prefixWord ++ tailWord_333564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333585 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_333585 : Nat := 118140960795 + 333585 * 2 ^ 59
def prefixEnd_333585 : Nat := 4983230072969 + 3 ^ 40 * 333585 * 2
def baseEnd_333585 : Nat := 152257283671273405203001

theorem tailTrace_333585 : CollatzResearch.WordTrace tailWord_333585 prefixEnd_333585 152257283671273405203001 := by
  unfold tailWord_333585
  simp only [CollatzResearch.WordTrace]
  refine ⟨12166844496485991627354209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8111229664323994418236139 12166844496485991627354209)
  ·
    refine ⟨9125133372364493720515657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12166844496485991627354209 9125133372364493720515657)
    ·
      refine ⟨6843850029273370290386743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9125133372364493720515657 6843850029273370290386743)
      ·
        refine ⟨10265775043910055435580115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6843850029273370290386743 10265775043910055435580115)
        ·
          refine ⟨15398662565865083153370173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10265775043910055435580115 15398662565865083153370173)
          ·
            refine ⟨5774498462199406182513815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15398662565865083153370173 5774498462199406182513815)
            ·
              refine ⟨8661747693299109273770723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5774498462199406182513815 8661747693299109273770723)
              ·
                refine ⟨12992621539948663910656085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8661747693299109273770723 12992621539948663910656085)
                ·
                  refine ⟨152257283671273405203001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12992621539948663910656085 152257283671273405203001)
                  ·
                    rfl

theorem cell20_333585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_333585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333585 prefixEnd_333585 := by exact prefixLift 333585
  have htrace : WordTrace (prefixWord ++ tailWord_333585) baseStart_333585 baseEnd_333585 := by
    simpa [prefixWord, tailWord_333585, baseEnd_333585] using wordTrace_append hprefix tailTrace_333585
  have hstable : (prefixWord ++ tailWord_333585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333585).length < 2 ^ (prefixWord ++ tailWord_333585).sum := by decide
  have hdescent : baseEnd_333585 < baseStart_333585 := by decide
  rcases family_descends (prefixWord ++ tailWord_333585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333612 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 3]
def baseStart_333612 : Nat := 118140960795 + 333612 * 2 ^ 59
def prefixEnd_333612 : Nat := 4983230072969 + 3 ^ 40 * 333612 * 2
def baseEnd_333612 : Nat := 152269607206981311302891

theorem tailTrace_333612 : CollatzResearch.WordTrace tailWord_333612 prefixEnd_333612 152269607206981311302891 := by
  unfold tailWord_333612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083914633694087619293545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8111886178258783492391393 6083914633694087619293545)
  ·
    refine ⟨4562935975270565714470159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6083914633694087619293545 4562935975270565714470159)
    ·
      refine ⟨6844403962905848571705239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4562935975270565714470159 6844403962905848571705239)
      ·
        refine ⟨10266605944358772857557859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6844403962905848571705239 10266605944358772857557859)
        ·
          refine ⟨15399908916538159286336789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10266605944358772857557859 15399908916538159286336789)
          ·
            refine ⟨721870730462726216547037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15399908916538159286336789 721870730462726216547037)
            ·
              refine ⟨270701523923522331205139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 721870730462726216547037 270701523923522331205139)
              ·
                refine ⟨406052285885283496807709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270701523923522331205139 406052285885283496807709)
                ·
                  refine ⟨152269607206981311302891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406052285885283496807709 152269607206981311302891)
                  ·
                    rfl

theorem cell20_333612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_333612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333612 prefixEnd_333612 := by exact prefixLift 333612
  have htrace : WordTrace (prefixWord ++ tailWord_333612) baseStart_333612 baseEnd_333612 := by
    simpa [prefixWord, tailWord_333612, baseEnd_333612] using wordTrace_append hprefix tailTrace_333612
  have hstable : (prefixWord ++ tailWord_333612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333612).length < 2 ^ (prefixWord ++ tailWord_333612).sum := by decide
  have hdescent : baseEnd_333612 < baseStart_333612 := by decide
  rcases family_descends (prefixWord ++ tailWord_333612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333622 : List Nat := [5, 1, 2, 2, 1, 3, 2, 4]
def baseStart_333622 : Nat := 118140960795 + 333622 * 2 ^ 59
def prefixEnd_333622 : Nat := 4983230072969 + 3 ^ 40 * 333622 * 2
def baseEnd_333622 : Nat := 50758057159821906989839

theorem tailTrace_333622 : CollatzResearch.WordTrace tailWord_333622 prefixEnd_333622 50758057159821906989839 := by
  unfold tailWord_333622
  simp only [CollatzResearch.WordTrace]
  refine ⟨760512124834496684153195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8112129331567964630967413 760512124834496684153195)
  ·
    refine ⟨1140768187251745026229793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 760512124834496684153195 1140768187251745026229793)
    ·
      refine ⟨855576140438808769672345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1140768187251745026229793 855576140438808769672345)
      ·
        refine ⟨641682105329106577254259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 855576140438808769672345 641682105329106577254259)
        ·
          refine ⟨962523157993659865881389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641682105329106577254259 962523157993659865881389)
          ·
            refine ⟨360946184247622449705521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 962523157993659865881389 360946184247622449705521)
            ·
              refine ⟨270709638185716837279141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360946184247622449705521 270709638185716837279141)
              ·
                refine ⟨50758057159821906989839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270709638185716837279141 50758057159821906989839)
                ·
                  rfl

theorem cell20_333622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_333622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333622 prefixEnd_333622 := by exact prefixLift 333622
  have htrace : WordTrace (prefixWord ++ tailWord_333622) baseStart_333622 baseEnd_333622 := by
    simpa [prefixWord, tailWord_333622, baseEnd_333622] using wordTrace_append hprefix tailTrace_333622
  have hstable : (prefixWord ++ tailWord_333622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333622).length < 2 ^ (prefixWord ++ tailWord_333622).sum := by decide
  have hdescent : baseEnd_333622 < baseStart_333622 := by decide
  rcases family_descends (prefixWord ++ tailWord_333622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333623 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_333623 : Nat := 118140960795 + 333623 * 2 ^ 59
def prefixEnd_333623 : Nat := 4983230072969 + 3 ^ 40 * 333623 * 2
def baseEnd_333623 : Nat := 152274627906714161936179

theorem tailTrace_333623 : CollatzResearch.WordTrace tailWord_333623 prefixEnd_333623 152274627906714161936179 := by
  unfold tailWord_333623
  simp only [CollatzResearch.WordTrace]
  refine ⟨12168230470348324117237523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8112153646898882744825015 12168230470348324117237523)
  ·
    refine ⟨18252345705522486175856285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12168230470348324117237523 18252345705522486175856285)
    ·
      refine ⟨6844629639570932315946107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18252345705522486175856285 6844629639570932315946107)
      ·
        refine ⟨10266944459356398473919161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6844629639570932315946107 10266944459356398473919161)
        ·
          refine ⟨7700208344517298855439371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10266944459356398473919161 7700208344517298855439371)
          ·
            refine ⟨11550312516775948283159057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7700208344517298855439371 11550312516775948283159057)
            ·
              refine ⟨8662734387581961212369293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11550312516775948283159057 8662734387581961212369293)
              ·
                refine ⟨3248525395343235454638485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8662734387581961212369293 3248525395343235454638485)
                ·
                  refine ⟨152274627906714161936179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3248525395343235454638485 152274627906714161936179)
                  ·
                    rfl

theorem cell20_333623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_333623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333623 prefixEnd_333623 := by exact prefixLift 333623
  have htrace : WordTrace (prefixWord ++ tailWord_333623) baseStart_333623 baseEnd_333623 := by
    simpa [prefixWord, tailWord_333623, baseEnd_333623] using wordTrace_append hprefix tailTrace_333623
  have hstable : (prefixWord ++ tailWord_333623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333623).length < 2 ^ (prefixWord ++ tailWord_333623).sum := by decide
  have hdescent : baseEnd_333623 < baseStart_333623 := by decide
  rcases family_descends (prefixWord ++ tailWord_333623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333626 : List Nat := [3, 1, 1, 1, 5, 1, 4, 4]
def baseStart_333626 : Nat := 118140960795 + 333626 * 2 ^ 59
def prefixEnd_333626 : Nat := 4983230072969 + 3 ^ 40 * 333626 * 2
def baseEnd_333626 : Nat := 50758665729486494945389

theorem tailTrace_333626 : CollatzResearch.WordTrace tailWord_333626 prefixEnd_333626 50758665729486494945389 := by
  unfold tailWord_333626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042084972334363907399183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8112226592891637086397821 3042084972334363907399183)
  ·
    refine ⟨4563127458501545861098775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3042084972334363907399183 4563127458501545861098775)
    ·
      refine ⟨6844691187752318791648163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4563127458501545861098775 6844691187752318791648163)
      ·
        refine ⟨10267036781628478187472245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6844691187752318791648163 10267036781628478187472245)
        ·
          refine ⟨962534698277669830075523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10267036781628478187472245 962534698277669830075523)
          ·
            refine ⟨1443802047416504745113285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962534698277669830075523 1443802047416504745113285)
            ·
              refine ⟨270712883890594639708741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1443802047416504745113285 270712883890594639708741)
              ·
                refine ⟨50758665729486494945389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270712883890594639708741 50758665729486494945389)
                ·
                  rfl

theorem cell20_333626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_333626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333626 prefixEnd_333626 := by exact prefixLift 333626
  have htrace : WordTrace (prefixWord ++ tailWord_333626) baseStart_333626 baseEnd_333626 := by
    simpa [prefixWord, tailWord_333626, baseEnd_333626] using wordTrace_append hprefix tailTrace_333626
  have hstable : (prefixWord ++ tailWord_333626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333626).length < 2 ^ (prefixWord ++ tailWord_333626).sum := by decide
  have hdescent : baseEnd_333626 < baseStart_333626 := by decide
  rcases family_descends (prefixWord ++ tailWord_333626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333667 : List Nat := [1, 1, 1, 5, 4, 2, 2, 1, 3]
def baseStart_333667 : Nat := 118140960795 + 333667 * 2 ^ 59
def prefixEnd_333667 : Nat := 4983230072969 + 3 ^ 40 * 333667 * 2
def baseEnd_333667 : Nat := 152294710705645564469333

theorem tailTrace_333667 : CollatzResearch.WordTrace tailWord_333667 prefixEnd_333667 152294710705645564469333 := by
  unfold tailWord_333667
  simp only [CollatzResearch.WordTrace]
  refine ⟨12169835282188919631839255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8113223521459279754559503 12169835282188919631839255)
  ·
    refine ⟨18254752923283379447758883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12169835282188919631839255 18254752923283379447758883)
    ·
      refine ⟨27382129384925069171638325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18254752923283379447758883 27382129384925069171638325)
      ·
        refine ⟨2567074629836725234841093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27382129384925069171638325 2567074629836725234841093)
        ·
          refine ⟨481326493094385981532705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2567074629836725234841093 481326493094385981532705)
          ·
            refine ⟨360994869820789486149529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481326493094385981532705 360994869820789486149529)
            ·
              refine ⟨270746152365592114612147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360994869820789486149529 270746152365592114612147)
              ·
                refine ⟨406119228548388171918221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270746152365592114612147 406119228548388171918221)
                ·
                  refine ⟨152294710705645564469333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406119228548388171918221 152294710705645564469333)
                  ·
                    rfl

theorem cell20_333667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 3].length) (baseStart_333667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333667 prefixEnd_333667 := by exact prefixLift 333667
  have htrace : WordTrace (prefixWord ++ tailWord_333667) baseStart_333667 baseEnd_333667 := by
    simpa [prefixWord, tailWord_333667, baseEnd_333667] using wordTrace_append hprefix tailTrace_333667
  have hstable : (prefixWord ++ tailWord_333667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333667).length < 2 ^ (prefixWord ++ tailWord_333667).sum := by decide
  have hdescent : baseEnd_333667 < baseStart_333667 := by decide
  rcases family_descends (prefixWord ++ tailWord_333667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333671 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 3]
def baseStart_333671 : Nat := 118140960795 + 333671 * 2 ^ 59
def prefixEnd_333671 : Nat := 4983230072969 + 3 ^ 40 * 333671 * 2
def baseEnd_333671 : Nat := 152296536414639328335983

theorem tailTrace_333671 : CollatzResearch.WordTrace tailWord_333671 prefixEnd_333671 152296536414639328335983 := by
  unfold tailWord_333671
  simp only [CollatzResearch.WordTrace]
  refine ⟨12169981174174428314984867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8113320782782952209989911 12169981174174428314984867)
  ·
    refine ⟨18254971761261642472477301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12169981174174428314984867 18254971761261642472477301)
    ·
      refine ⟨1711403602618278981794747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18254971761261642472477301 1711403602618278981794747)
      ·
        refine ⟨2567105403927418472692121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711403602618278981794747 2567105403927418472692121)
        ·
          refine ⟨1925329052945563854519091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2567105403927418472692121 1925329052945563854519091)
          ·
            refine ⟨2887993579418345781778637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925329052945563854519091 2887993579418345781778637)
            ·
              refine ⟨1082997592281879668166989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2887993579418345781778637 1082997592281879668166989)
              ·
                refine ⟨406124097105704875562621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1082997592281879668166989 406124097105704875562621)
                ·
                  refine ⟨152296536414639328335983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406124097105704875562621 152296536414639328335983)
                  ·
                    rfl

theorem cell20_333671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_333671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333671 prefixEnd_333671 := by exact prefixLift 333671
  have htrace : WordTrace (prefixWord ++ tailWord_333671) baseStart_333671 baseEnd_333671 := by
    simpa [prefixWord, tailWord_333671, baseEnd_333671] using wordTrace_append hprefix tailTrace_333671
  have hstable : (prefixWord ++ tailWord_333671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333671).length < 2 ^ (prefixWord ++ tailWord_333671).sum := by decide
  have hdescent : baseEnd_333671 < baseStart_333671 := by decide
  rcases family_descends (prefixWord ++ tailWord_333671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333685 : List Nat := [1, 3, 4, 1, 1, 1, 1, 8]
def baseStart_333685 : Nat := 118140960795 + 333685 * 2 ^ 59
def prefixEnd_333685 : Nat := 4983230072969 + 3 ^ 40 * 333685 * 2
def baseEnd_333685 : Nat := 50767642132039167289753

theorem tailTrace_333685 : CollatzResearch.WordTrace tailWord_333685 prefixEnd_333685 50767642132039167289753 := by
  unfold tailWord_333685
  simp only [CollatzResearch.WordTrace]
  refine ⟨12170491796123708705994509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8113661197415805803996339 12170491796123708705994509)
  ·
    refine ⟨4563934423546390764747941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12170491796123708705994509 4563934423546390764747941)
    ·
      refine ⟨855737704414948268390239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4563934423546390764747941 855737704414948268390239)
      ·
        refine ⟨1283606556622422402585359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855737704414948268390239 1283606556622422402585359)
        ·
          refine ⟨1925409834933633603878039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283606556622422402585359 1925409834933633603878039)
          ·
            refine ⟨2888114752400450405817059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925409834933633603878039 2888114752400450405817059)
            ·
              refine ⟨4332172128600675608725589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2888114752400450405817059 4332172128600675608725589)
              ·
                refine ⟨50767642132039167289753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4332172128600675608725589 50767642132039167289753)
                ·
                  rfl

theorem cell20_333685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_333685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333685 prefixEnd_333685 := by exact prefixLift 333685
  have htrace : WordTrace (prefixWord ++ tailWord_333685) baseStart_333685 baseEnd_333685 := by
    simpa [prefixWord, tailWord_333685, baseEnd_333685] using wordTrace_append hprefix tailTrace_333685
  have hstable : (prefixWord ++ tailWord_333685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333685).length < 2 ^ (prefixWord ++ tailWord_333685).sum := by decide
  have hdescent : baseEnd_333685 < baseStart_333685 := by decide
  rcases family_descends (prefixWord ++ tailWord_333685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333736 : List Nat := [2, 1, 6, 2, 1, 1, 3, 4]
def baseStart_333736 : Nat := 118140960795 + 333736 * 2 ^ 59
def prefixEnd_333736 : Nat := 4983230072969 + 3 ^ 40 * 333736 * 2
def baseEnd_333736 : Nat := 50775401395262663723017

theorem tailTrace_333736 : CollatzResearch.WordTrace tailWord_333736 prefixEnd_333736 50775401395262663723017 := by
  unfold tailWord_333736
  simp only [CollatzResearch.WordTrace]
  refine ⟨6086175959469472208050531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8114901279292629610734041 6086175959469472208050531)
  ·
    refine ⟨9129263939204208312075797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6086175959469472208050531 9129263939204208312075797)
    ·
      refine ⟨427934247150197264628553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9129263939204208312075797 427934247150197264628553)
      ·
        refine ⟨320950685362647948471415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427934247150197264628553 320950685362647948471415)
        ·
          refine ⟨481426028043971922707123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320950685362647948471415 481426028043971922707123)
          ·
            refine ⟨722139042065957884060685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481426028043971922707123 722139042065957884060685)
            ·
              refine ⟨270802140774734206522757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722139042065957884060685 270802140774734206522757)
              ·
                refine ⟨50775401395262663723017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270802140774734206522757 50775401395262663723017)
                ·
                  rfl

theorem cell20_333736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_333736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333736 prefixEnd_333736 := by exact prefixLift 333736
  have htrace : WordTrace (prefixWord ++ tailWord_333736) baseStart_333736 baseEnd_333736 := by
    simpa [prefixWord, tailWord_333736, baseEnd_333736] using wordTrace_append hprefix tailTrace_333736
  have hstable : (prefixWord ++ tailWord_333736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333736).length < 2 ^ (prefixWord ++ tailWord_333736).sum := by decide
  have hdescent : baseEnd_333736 < baseStart_333736 := by decide
  rcases family_descends (prefixWord ++ tailWord_333736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333878 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_333878 : Nat := 118140960795 + 333878 * 2 ^ 59
def prefixEnd_333878 : Nat := 4983230072969 + 3 ^ 40 * 333878 * 2
def baseEnd_333878 : Nat := 152391016855066608435137

theorem tailTrace_333878 : CollatzResearch.WordTrace tailWord_333878 prefixEnd_333878 152391016855066608435137 := by
  unfold tailWord_333878
  simp only [CollatzResearch.WordTrace]
  refine ⟨761095692776531416735643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8118354056283001778513525 761095692776531416735643)
  ·
    refine ⟨1141643539164797125103465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 761095692776531416735643 1141643539164797125103465)
    ·
      refine ⟨856232654373597843827599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1141643539164797125103465 856232654373597843827599)
      ·
        refine ⟨1284348981560396765741399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856232654373597843827599 1284348981560396765741399)
        ·
          refine ⟨1926523472340595148612099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284348981560396765741399 1926523472340595148612099)
          ·
            refine ⟨2889785208510892722918149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926523472340595148612099 2889785208510892722918149)
            ·
              refine ⟨541834726595792385547153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2889785208510892722918149 541834726595792385547153)
              ·
                refine ⟨406376044946844289160365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541834726595792385547153 406376044946844289160365)
                ·
                  refine ⟨152391016855066608435137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406376044946844289160365 152391016855066608435137)
                  ·
                    rfl

theorem cell20_333878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_333878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333878 prefixEnd_333878 := by exact prefixLift 333878
  have htrace : WordTrace (prefixWord ++ tailWord_333878) baseStart_333878 baseEnd_333878 := by
    simpa [prefixWord, tailWord_333878, baseEnd_333878] using wordTrace_append hprefix tailTrace_333878
  have hstable : (prefixWord ++ tailWord_333878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333878).length < 2 ^ (prefixWord ++ tailWord_333878).sum := by decide
  have hdescent : baseEnd_333878 < baseStart_333878 := by decide
  rcases family_descends (prefixWord ++ tailWord_333878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333881 : List Nat := [1, 2, 1, 5, 3, 2, 2, 2, 2]
def baseStart_333881 : Nat := 118140960795 + 333881 * 2 ^ 59
def prefixEnd_333881 : Nat := 4983230072969 + 3 ^ 40 * 333881 * 2
def baseEnd_333881 : Nat := 152392386136811931335125

theorem tailTrace_333881 : CollatzResearch.WordTrace tailWord_333881 prefixEnd_333881 152392386136811931335125 := by
  unfold tailWord_333881
  simp only [CollatzResearch.WordTrace]
  refine ⟨12177640503413634180129497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8118427002275756120086331 12177640503413634180129497)
  ·
    refine ⟨9133230377560225635097123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12177640503413634180129497 9133230377560225635097123)
    ·
      refine ⟨13699845566340338452645685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9133230377560225635097123 13699845566340338452645685)
      ·
        refine ⟨1284360521844406729935533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13699845566340338452645685 1284360521844406729935533)
        ·
          refine ⟨481635195691652523725825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1284360521844406729935533 481635195691652523725825)
          ·
            refine ⟨361226396768739392794369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481635195691652523725825 361226396768739392794369)
            ·
              refine ⟨270919797576554544595777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361226396768739392794369 270919797576554544595777)
              ·
                refine ⟨203189848182415908446833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270919797576554544595777 203189848182415908446833)
                ·
                  refine ⟨152392386136811931335125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203189848182415908446833 152392386136811931335125)
                  ·
                    rfl

theorem cell20_333881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_333881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333881 prefixEnd_333881 := by exact prefixLift 333881
  have htrace : WordTrace (prefixWord ++ tailWord_333881) baseStart_333881 baseEnd_333881 := by
    simpa [prefixWord, tailWord_333881, baseEnd_333881] using wordTrace_append hprefix tailTrace_333881
  have hstable : (prefixWord ++ tailWord_333881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333881).length < 2 ^ (prefixWord ++ tailWord_333881).sum := by decide
  have hdescent : baseEnd_333881 < baseStart_333881 := by decide
  rcases family_descends (prefixWord ++ tailWord_333881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333885 : List Nat := [1, 4, 1, 3, 1, 1, 3, 4, 2]
def baseStart_333885 : Nat := 118140960795 + 333885 * 2 ^ 59
def prefixEnd_333885 : Nat := 4983230072969 + 3 ^ 40 * 333885 * 2
def baseEnd_333885 : Nat := 152394211845805695201775

theorem tailTrace_333885 : CollatzResearch.WordTrace tailWord_333885 prefixEnd_333885 152394211845805695201775 := by
  unfold tailWord_333885
  simp only [CollatzResearch.WordTrace]
  refine ⟨12177786395399142863275109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8118524263599428575516739 12177786395399142863275109)
  ·
    refine ⟨2283334949137339286864083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12177786395399142863275109 2283334949137339286864083)
    ·
      refine ⟨3425002423706008930296125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2283334949137339286864083 3425002423706008930296125)
      ·
        refine ⟨1284375908889753348861047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3425002423706008930296125 1284375908889753348861047)
        ·
          refine ⟨1926563863334630023291571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284375908889753348861047 1926563863334630023291571)
          ·
            refine ⟨2889845795001945034937357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926563863334630023291571 2889845795001945034937357)
            ·
              refine ⟨1083692173125729388101509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2889845795001945034937357 1083692173125729388101509)
              ·
                refine ⟨203192282461074260269033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1083692173125729388101509 203192282461074260269033)
                ·
                  refine ⟨152394211845805695201775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203192282461074260269033 152394211845805695201775)
                  ·
                    rfl

theorem cell20_333885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_333885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333885 prefixEnd_333885 := by exact prefixLift 333885
  have htrace : WordTrace (prefixWord ++ tailWord_333885) baseStart_333885 baseEnd_333885 := by
    simpa [prefixWord, tailWord_333885, baseEnd_333885] using wordTrace_append hprefix tailTrace_333885
  have hstable : (prefixWord ++ tailWord_333885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333885).length < 2 ^ (prefixWord ++ tailWord_333885).sum := by decide
  have hdescent : baseEnd_333885 < baseStart_333885 := by decide
  rcases family_descends (prefixWord ++ tailWord_333885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333896 : List Nat := [2, 1, 3, 1, 1, 1, 2, 9]
def baseStart_333896 : Nat := 118140960795 + 333896 * 2 ^ 59
def prefixEnd_333896 : Nat := 4983230072969 + 3 ^ 40 * 333896 * 2
def baseEnd_333896 : Nat := 50799744181846181945021

theorem tailTrace_333896 : CollatzResearch.WordTrace tailWord_333896 prefixEnd_333896 50799744181846181945021 := by
  unfold tailWord_333896
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089093799179645870962771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8118791732239527827950361 6089093799179645870962771)
  ·
    refine ⟨9133640698769468806444157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089093799179645870962771 9133640698769468806444157)
    ·
      refine ⟨3425115262038550802416559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9133640698769468806444157 3425115262038550802416559)
      ·
        refine ⟨5137672893057826203624839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3425115262038550802416559 5137672893057826203624839)
        ·
          refine ⟨7706509339586739305437259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5137672893057826203624839 7706509339586739305437259)
          ·
            refine ⟨11559764009380108958155889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7706509339586739305437259 11559764009380108958155889)
            ·
              refine ⟨8669823007035081718616917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11559764009380108958155889 8669823007035081718616917)
              ·
                refine ⟨50799744181846181945021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8669823007035081718616917 50799744181846181945021)
                ·
                  rfl

theorem cell20_333896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_333896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333896 prefixEnd_333896 := by exact prefixLift 333896
  have htrace : WordTrace (prefixWord ++ tailWord_333896) baseStart_333896 baseEnd_333896 := by
    simpa [prefixWord, tailWord_333896, baseEnd_333896] using wordTrace_append hprefix tailTrace_333896
  have hstable : (prefixWord ++ tailWord_333896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333896).length < 2 ^ (prefixWord ++ tailWord_333896).sum := by decide
  have hdescent : baseEnd_333896 < baseStart_333896 := by decide
  rcases family_descends (prefixWord ++ tailWord_333896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333913 : List Nat := [1, 2, 1, 2, 2, 1, 7, 4]
def baseStart_333913 : Nat := 118140960795 + 333913 * 2 ^ 59
def prefixEnd_333913 : Nat := 4983230072969 + 3 ^ 40 * 333913 * 2
def baseEnd_333913 : Nat := 50802330602920680756109

theorem tailTrace_333913 : CollatzResearch.WordTrace tailWord_333913 prefixEnd_333913 50802330602920680756109 := by
  unfold tailWord_333913
  simp only [CollatzResearch.WordTrace]
  refine ⟨12178807639297703645294393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8119205092865135763529595 12178807639297703645294393)
  ·
    refine ⟨9134105729473277733970795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12178807639297703645294393 9134105729473277733970795)
    ·
      refine ⟨13701158594209916600956193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9134105729473277733970795 13701158594209916600956193)
      ·
        refine ⟨10275868945657437450717145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13701158594209916600956193 10275868945657437450717145)
        ·
          refine ⟨7706901709243078088037859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10275868945657437450717145 7706901709243078088037859)
          ·
            refine ⟨11560352563864617132056789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7706901709243078088037859 11560352563864617132056789)
            ·
              refine ⟨270945763215576964032581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11560352563864617132056789 270945763215576964032581)
              ·
                refine ⟨50802330602920680756109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270945763215576964032581 50802330602920680756109)
                ·
                  rfl

theorem cell20_333913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 4].length) (baseStart_333913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333913 prefixEnd_333913 := by exact prefixLift 333913
  have htrace : WordTrace (prefixWord ++ tailWord_333913) baseStart_333913 baseEnd_333913 := by
    simpa [prefixWord, tailWord_333913, baseEnd_333913] using wordTrace_append hprefix tailTrace_333913
  have hstable : (prefixWord ++ tailWord_333913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333913).length < 2 ^ (prefixWord ++ tailWord_333913).sum := by decide
  have hdescent : baseEnd_333913 < baseStart_333913 := by decide
  rcases family_descends (prefixWord ++ tailWord_333913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333927 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_333927 : Nat := 118140960795 + 333927 * 2 ^ 59
def prefixEnd_333927 : Nat := 4983230072969 + 3 ^ 40 * 333927 * 2
def baseEnd_333927 : Nat := 152413381790240215801603

theorem tailTrace_333927 : CollatzResearch.WordTrace tailWord_333927 prefixEnd_333927 152413381790240215801603 := by
  unfold tailWord_333927
  simp only [CollatzResearch.WordTrace]
  refine ⟨12179318261246984036304035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8119545507497989357536023 12179318261246984036304035)
  ·
    refine ⟨18268977391870476054456053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12179318261246984036304035 18268977391870476054456053)
    ·
      refine ⟨1712716630487857130105255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18268977391870476054456053 1712716630487857130105255)
      ·
        refine ⟨2569074945731785695157883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712716630487857130105255 2569074945731785695157883)
        ·
          refine ⟨3853612418597678542736825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569074945731785695157883 3853612418597678542736825)
          ·
            refine ⟨2890209313948258907052619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3853612418597678542736825 2890209313948258907052619)
            ·
              refine ⟨4335313970922388360578929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890209313948258907052619 4335313970922388360578929)
              ·
                refine ⟨3251485478191791270434197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4335313970922388360578929 3251485478191791270434197)
                ·
                  refine ⟨152413381790240215801603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3251485478191791270434197 152413381790240215801603)
                  ·
                    rfl

theorem cell20_333927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_333927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333927 prefixEnd_333927 := by exact prefixLift 333927
  have htrace : WordTrace (prefixWord ++ tailWord_333927) baseStart_333927 baseEnd_333927 := by
    simpa [prefixWord, tailWord_333927, baseEnd_333927] using wordTrace_append hprefix tailTrace_333927
  have hstable : (prefixWord ++ tailWord_333927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333927).length < 2 ^ (prefixWord ++ tailWord_333927).sum := by decide
  have hdescent : baseEnd_333927 < baseStart_333927 := by decide
  rcases family_descends (prefixWord ++ tailWord_333927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_333979 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_333979 : Nat := 118140960795 + 333979 * 2 ^ 59
def prefixEnd_333979 : Nat := 4983230072969 + 3 ^ 40 * 333979 * 2
def baseEnd_333979 : Nat := 152437116007159146068057

theorem tailTrace_333979 : CollatzResearch.WordTrace tailWord_333979 prefixEnd_333979 152437116007159146068057 := by
  unfold tailWord_333979
  simp only [CollatzResearch.WordTrace]
  refine ⟨12181214857058596917196991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8120809904705731278131327 12181214857058596917196991)
  ·
    refine ⟨18271822285587895375795487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12181214857058596917196991 18271822285587895375795487)
    ·
      refine ⟨27407733428381843063693231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18271822285587895375795487 27407733428381843063693231)
      ·
        refine ⟨41111600142572764595539847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27407733428381843063693231 41111600142572764595539847)
        ·
          refine ⟨61667400213859146893309771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41111600142572764595539847 61667400213859146893309771)
          ·
            refine ⟨92501100320788720339964657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61667400213859146893309771 92501100320788720339964657)
            ·
              refine ⟨69375825240591540254973493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92501100320788720339964657 69375825240591540254973493)
              ·
                refine ⟨6503983616305456898903765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69375825240591540254973493 6503983616305456898903765)
                ·
                  refine ⟨152437116007159146068057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6503983616305456898903765 152437116007159146068057)
                  ·
                    rfl

theorem cell20_333979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_333979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_333979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_333979 prefixEnd_333979 := by exact prefixLift 333979
  have htrace : WordTrace (prefixWord ++ tailWord_333979) baseStart_333979 baseEnd_333979 := by
    simpa [prefixWord, tailWord_333979, baseEnd_333979] using wordTrace_append hprefix tailTrace_333979
  have hstable : (prefixWord ++ tailWord_333979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_333979).length < 2 ^ (prefixWord ++ tailWord_333979).sum := by decide
  have hdescent : baseEnd_333979 < baseStart_333979 := by decide
  rcases family_descends (prefixWord ++ tailWord_333979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334010 : List Nat := [3, 1, 1, 1, 2, 2, 3, 7]
def baseStart_334010 : Nat := 118140960795 + 334010 * 2 ^ 59
def prefixEnd_334010 : Nat := 4983230072969 + 3 ^ 40 * 334010 * 2
def baseEnd_334010 : Nat := 50817088417286938678199

theorem tailTrace_334010 : CollatzResearch.WordTrace tailWord_334010 prefixEnd_334010 50817088417286938678199 := by
  unfold tailWord_334010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3045586379986572302893871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8121563679964192807716989 3045586379986572302893871)
  ·
    refine ⟨4568379569979858454340807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3045586379986572302893871 4568379569979858454340807)
    ·
      refine ⟨6852569354969787681511211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4568379569979858454340807 6852569354969787681511211)
      ·
        refine ⟨10278854032454681522266817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6852569354969787681511211 10278854032454681522266817)
        ·
          refine ⟨7709140524341011141700113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10278854032454681522266817 7709140524341011141700113)
          ·
            refine ⟨5781855393255758356275085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7709140524341011141700113 5781855393255758356275085)
            ·
              refine ⟨2168195772470909383603157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5781855393255758356275085 2168195772470909383603157)
              ·
                refine ⟨50817088417286938678199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2168195772470909383603157 50817088417286938678199)
                ·
                  rfl

theorem cell20_334010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_334010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334010 prefixEnd_334010 := by exact prefixLift 334010
  have htrace : WordTrace (prefixWord ++ tailWord_334010) baseStart_334010 baseEnd_334010 := by
    simpa [prefixWord, tailWord_334010, baseEnd_334010] using wordTrace_append hprefix tailTrace_334010
  have hstable : (prefixWord ++ tailWord_334010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334010).length < 2 ^ (prefixWord ++ tailWord_334010).sum := by decide
  have hdescent : baseEnd_334010 < baseStart_334010 := by decide
  rcases family_descends (prefixWord ++ tailWord_334010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334044 : List Nat := [2, 2, 5, 2, 1, 8]
def baseStart_334044 : Nat := 118140960795 + 334044 * 2 ^ 59
def prefixEnd_334044 : Nat := 4983230072969 + 3 ^ 40 * 334044 * 2
def baseEnd_334044 : Nat := 5646917917715104033375

theorem tailTrace_334044 : CollatzResearch.WordTrace tailWord_334044 prefixEnd_334044 5646917917715104033375 := by
  unfold tailWord_334044
  simp only [CollatzResearch.WordTrace]
  refine ⟨6091792800911556509156593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8122390401215408678875457 6091792800911556509156593)
  ·
    refine ⟨4568844600683667381867445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6091792800911556509156593 4568844600683667381867445)
    ·
      refine ⟨428329181314093817050073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4568844600683667381867445 428329181314093817050073)
      ·
        refine ⟨321246885985570362787555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428329181314093817050073 321246885985570362787555)
        ·
          refine ⟨481870328978355544181333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321246885985570362787555 481870328978355544181333)
          ·
            refine ⟨5646917917715104033375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 481870328978355544181333 5646917917715104033375)
            ·
              rfl

theorem cell20_334044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 8].length) (baseStart_334044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334044 prefixEnd_334044 := by exact prefixLift 334044
  have htrace : WordTrace (prefixWord ++ tailWord_334044) baseStart_334044 baseEnd_334044 := by
    simpa [prefixWord, tailWord_334044, baseEnd_334044] using wordTrace_append hprefix tailTrace_334044
  have hstable : (prefixWord ++ tailWord_334044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334044).length < 2 ^ (prefixWord ++ tailWord_334044).sum := by decide
  have hdescent : baseEnd_334044 < baseStart_334044 := by decide
  rcases family_descends (prefixWord ++ tailWord_334044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334050 : List Nat := [3, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_334050 : Nat := 118140960795 + 334050 * 2 ^ 59
def prefixEnd_334050 : Nat := 4983230072969 + 3 ^ 40 * 334050 * 2
def baseEnd_334050 : Nat := 152469522341798454701101

theorem tailTrace_334050 : CollatzResearch.WordTrace tailWord_334050 prefixEnd_334050 152469522341798454701101 := by
  unfold tailWord_334050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3045951109950344010757901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8122536293200917362021069 3045951109950344010757901)
  ·
    refine ⟨1142231666231379004034213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3045951109950344010757901 1142231666231379004034213)
    ·
      refine ⟨214168437418383563256415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1142231666231379004034213 214168437418383563256415)
      ·
        refine ⟨321252656127575344884623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214168437418383563256415 321252656127575344884623)
        ·
          refine ⟨481878984191363017326935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321252656127575344884623 481878984191363017326935)
          ·
            refine ⟨722818476287044525990403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481878984191363017326935 722818476287044525990403)
            ·
              refine ⟨1084227714430566788985605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722818476287044525990403 1084227714430566788985605)
              ·
                refine ⟨203292696455731272934801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1084227714430566788985605 203292696455731272934801)
                ·
                  refine ⟨152469522341798454701101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203292696455731272934801 152469522341798454701101)
                  ·
                    rfl

theorem cell20_334050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_334050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334050 prefixEnd_334050 := by exact prefixLift 334050
  have htrace : WordTrace (prefixWord ++ tailWord_334050) baseStart_334050 baseEnd_334050 := by
    simpa [prefixWord, tailWord_334050, baseEnd_334050] using wordTrace_append hprefix tailTrace_334050
  have hstable : (prefixWord ++ tailWord_334050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334050).length < 2 ^ (prefixWord ++ tailWord_334050).sum := by decide
  have hdescent : baseEnd_334050 < baseStart_334050 := by decide
  rcases family_descends (prefixWord ++ tailWord_334050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334061 : List Nat := [1, 5, 1, 2, 4, 1, 1, 5]
def baseStart_334061 : Nat := 118140960795 + 334061 * 2 ^ 59
def prefixEnd_334061 : Nat := 4983230072969 + 3 ^ 40 * 334061 * 2
def baseEnd_334061 : Nat := 50824847680510435111463

theorem tailTrace_334061 : CollatzResearch.WordTrace tailWord_334061 prefixEnd_334061 50824847680510435111463 := by
  unfold tailWord_334061
  simp only [CollatzResearch.WordTrace]
  refine ⟨12184205642761524921682037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8122803761841016614454691 12184205642761524921682037)
  ·
    refine ⟨1142269279008892961407691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12184205642761524921682037 1142269279008892961407691)
    ·
      refine ⟨1713403918513339442111537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1142269279008892961407691 1713403918513339442111537)
      ·
        refine ⟨1285052938885004581583653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1713403918513339442111537 1285052938885004581583653)
        ·
          refine ⟨240947426040938359046935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1285052938885004581583653 240947426040938359046935)
          ·
            refine ⟨361421139061407538570403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240947426040938359046935 361421139061407538570403)
            ·
              refine ⟨542131708592111307855605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361421139061407538570403 542131708592111307855605)
              ·
                refine ⟨50824847680510435111463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 542131708592111307855605 50824847680510435111463)
                ·
                  rfl

theorem cell20_334061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 5].length) (baseStart_334061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334061 prefixEnd_334061 := by exact prefixLift 334061
  have htrace : WordTrace (prefixWord ++ tailWord_334061) baseStart_334061 baseEnd_334061 := by
    simpa [prefixWord, tailWord_334061, baseEnd_334061] using wordTrace_append hprefix tailTrace_334061
  have hstable : (prefixWord ++ tailWord_334061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334061).length < 2 ^ (prefixWord ++ tailWord_334061).sum := by decide
  have hdescent : baseEnd_334061 < baseStart_334061 := by decide
  rcases family_descends (prefixWord ++ tailWord_334061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334079 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_334079 : Nat := 118140960795 + 334079 * 2 ^ 59
def prefixEnd_334079 : Nat := 4983230072969 + 3 ^ 40 * 334079 * 2
def baseEnd_334079 : Nat := 152482758732003242734315

theorem tailTrace_334079 : CollatzResearch.WordTrace tailWord_334079 prefixEnd_334079 152482758732003242734315 := by
  unfold tailWord_334079
  simp only [CollatzResearch.WordTrace]
  refine ⟨12184862156696313995837291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8123241437797542663891527 12184862156696313995837291)
  ·
    refine ⟨18277293235044470993755937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12184862156696313995837291 18277293235044470993755937)
    ·
      refine ⟨13707969926283353245316953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18277293235044470993755937 13707969926283353245316953)
      ·
        refine ⟨10280977444712514933987715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13707969926283353245316953 10280977444712514933987715)
        ·
          refine ⟨15421466167068772400981573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10280977444712514933987715 15421466167068772400981573)
          ·
            refine ⟨2891524906325394825184045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15421466167068772400981573 2891524906325394825184045)
            ·
              refine ⟨1084321839872023059444017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2891524906325394825184045 1084321839872023059444017)
              ·
                refine ⟨813241379904017294583013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084321839872023059444017 813241379904017294583013)
                ·
                  refine ⟨152482758732003242734315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 813241379904017294583013 152482758732003242734315)
                  ·
                    rfl

theorem cell20_334079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_334079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334079 prefixEnd_334079 := by exact prefixLift 334079
  have htrace : WordTrace (prefixWord ++ tailWord_334079) baseStart_334079 baseEnd_334079 := by
    simpa [prefixWord, tailWord_334079, baseEnd_334079] using wordTrace_append hprefix tailTrace_334079
  have hstable : (prefixWord ++ tailWord_334079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334079).length < 2 ^ (prefixWord ++ tailWord_334079).sum := by decide
  have hdescent : baseEnd_334079 < baseStart_334079 := by decide
  rcases family_descends (prefixWord ++ tailWord_334079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334106 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_334106 : Nat := 118140960795 + 334106 * 2 ^ 59
def prefixEnd_334106 : Nat := 4983230072969 + 3 ^ 40 * 334106 * 2
def baseEnd_334106 : Nat := 152495082267711148834205

theorem tailTrace_334106 : CollatzResearch.WordTrace tailWord_334106 prefixEnd_334106 152495082267711148834205 := by
  unfold tailWord_334106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046461731899624401767543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8123897951732331738046781 3046461731899624401767543)
  ·
    refine ⟨4569692597849436602651315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3046461731899624401767543 4569692597849436602651315)
    ·
      refine ⟨6854538896774154903976973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4569692597849436602651315 6854538896774154903976973)
      ·
        refine ⟨2570452086290308088991365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6854538896774154903976973 2570452086290308088991365)
        ·
          refine ⟨481959766179432766685881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2570452086290308088991365 481959766179432766685881)
          ·
            refine ⟨361469824634574575014411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481959766179432766685881 361469824634574575014411)
            ·
              refine ⟨542204736951861862521617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361469824634574575014411 542204736951861862521617)
              ·
                refine ⟨406653552713896396891213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542204736951861862521617 406653552713896396891213)
                ·
                  refine ⟨152495082267711148834205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406653552713896396891213 152495082267711148834205)
                  ·
                    rfl

theorem cell20_334106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_334106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334106 prefixEnd_334106 := by exact prefixLift 334106
  have htrace : WordTrace (prefixWord ++ tailWord_334106) baseStart_334106 baseEnd_334106 := by
    simpa [prefixWord, tailWord_334106, baseEnd_334106] using wordTrace_append hprefix tailTrace_334106
  have hstable : (prefixWord ++ tailWord_334106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334106).length < 2 ^ (prefixWord ++ tailWord_334106).sum := by decide
  have hdescent : baseEnd_334106 < baseStart_334106 := by decide
  rcases family_descends (prefixWord ++ tailWord_334106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334162 : List Nat := [3, 2, 2, 1, 1, 1, 10]
def baseStart_334162 : Nat := 118140960795 + 334162 * 2 ^ 59
def prefixEnd_334162 : Nat := 4983230072969 + 3 ^ 40 * 334162 * 2
def baseEnd_334162 : Nat := 16946738021513760329701

theorem tailTrace_334162 : CollatzResearch.WordTrace tailWord_334162 prefixEnd_334162 16946738021513760329701 := by
  unfold tailWord_334162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046972353848904792777185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8125259610263746114072493 3046972353848904792777185)
  ·
    refine ⟨2285229265386678594582889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3046972353848904792777185 2285229265386678594582889)
    ·
      refine ⟨1713921949040008945937167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2285229265386678594582889 1713921949040008945937167)
      ·
        refine ⟨2570882923560013418905751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713921949040008945937167 2570882923560013418905751)
        ·
          refine ⟨3856324385340020128358627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570882923560013418905751 3856324385340020128358627)
          ·
            refine ⟨5784486578010030192537941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3856324385340020128358627 5784486578010030192537941)
            ·
              refine ⟨16946738021513760329701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5784486578010030192537941 16946738021513760329701)
              ·
                rfl

theorem cell20_334162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 10].length) (baseStart_334162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334162 prefixEnd_334162 := by exact prefixLift 334162
  have htrace : WordTrace (prefixWord ++ tailWord_334162) baseStart_334162 baseEnd_334162 := by
    simpa [prefixWord, tailWord_334162, baseEnd_334162] using wordTrace_append hprefix tailTrace_334162
  have hstable : (prefixWord ++ tailWord_334162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334162).length < 2 ^ (prefixWord ++ tailWord_334162).sum := by decide
  have hdescent : baseEnd_334162 < baseStart_334162 := by decide
  rcases family_descends (prefixWord ++ tailWord_334162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334174 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_334174 : Nat := 118140960795 + 334174 * 2 ^ 59
def prefixEnd_334174 : Nat := 4983230072969 + 3 ^ 40 * 334174 * 2
def baseEnd_334174 : Nat := 152526119320605134567261

theorem tailTrace_334174 : CollatzResearch.WordTrace tailWord_334174 prefixEnd_334174 152526119320605134567261 := by
  unfold tailWord_334174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1523540886419018152568197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8125551394234763480363717 1523540886419018152568197)
  ·
    refine ⟨285663916203565903606537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1523540886419018152568197 285663916203565903606537)
    ·
      refine ⟨214247937152674427704903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285663916203565903606537 214247937152674427704903)
      ·
        refine ⟨321371905729011641557355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214247937152674427704903 321371905729011641557355)
        ·
          refine ⟨482057858593517462336033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321371905729011641557355 482057858593517462336033)
          ·
            refine ⟨361543393945138096752025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482057858593517462336033 361543393945138096752025)
            ·
              refine ⟨271157545458853572564019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361543393945138096752025 271157545458853572564019)
              ·
                refine ⟨406736318188280358846029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271157545458853572564019 406736318188280358846029)
                ·
                  refine ⟨152526119320605134567261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406736318188280358846029 152526119320605134567261)
                  ·
                    rfl

theorem cell20_334174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_334174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334174 prefixEnd_334174 := by exact prefixLift 334174
  have htrace : WordTrace (prefixWord ++ tailWord_334174) baseStart_334174 baseEnd_334174 := by
    simpa [prefixWord, tailWord_334174, baseEnd_334174] using wordTrace_append hprefix tailTrace_334174
  have hstable : (prefixWord ++ tailWord_334174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334174).length < 2 ^ (prefixWord ++ tailWord_334174).sum := by decide
  have hdescent : baseEnd_334174 < baseStart_334174 := by decide
  rcases family_descends (prefixWord ++ tailWord_334174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334248 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_334248 : Nat := 118140960795 + 334248 * 2 ^ 59
def prefixEnd_334248 : Nat := 4983230072969 + 3 ^ 40 * 334248 * 2
def baseEnd_334248 : Nat := 152559894936989766100291

theorem tailTrace_334248 : CollatzResearch.WordTrace tailWord_334248 prefixEnd_334248 152559894936989766100291 := by
  unfold tailWord_334248
  simp only [CollatzResearch.WordTrace]
  refine ⟨6095513046542027929369699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8127350728722703905826265 6095513046542027929369699)
  ·
    refine ⟨9143269569813041894054549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6095513046542027929369699 9143269569813041894054549)
    ·
      refine ⟨428590761084986338783807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9143269569813041894054549 428590761084986338783807)
      ·
        refine ⟨642886141627479508175711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428590761084986338783807 642886141627479508175711)
        ·
          refine ⟨964329212441219262263567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642886141627479508175711 964329212441219262263567)
          ·
            refine ⟨1446493818661828893395351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964329212441219262263567 1446493818661828893395351)
            ·
              refine ⟨2169740727992743340093027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446493818661828893395351 2169740727992743340093027)
              ·
                refine ⟨3254611091989115010139541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169740727992743340093027 3254611091989115010139541)
                ·
                  refine ⟨152559894936989766100291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3254611091989115010139541 152559894936989766100291)
                  ·
                    rfl

theorem cell20_334248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_334248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334248 prefixEnd_334248 := by exact prefixLift 334248
  have htrace : WordTrace (prefixWord ++ tailWord_334248) baseStart_334248 baseEnd_334248 := by
    simpa [prefixWord, tailWord_334248, baseEnd_334248] using wordTrace_append hprefix tailTrace_334248
  have hstable : (prefixWord ++ tailWord_334248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334248).length < 2 ^ (prefixWord ++ tailWord_334248).sum := by decide
  have hdescent : baseEnd_334248 < baseStart_334248 := by decide
  rcases family_descends (prefixWord ++ tailWord_334248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334265 : List Nat := [1, 2, 1, 4, 3, 2, 2, 3, 2]
def baseStart_334265 : Nat := 118140960795 + 334265 * 2 ^ 59
def prefixEnd_334265 : Nat := 4983230072969 + 3 ^ 40 * 334265 * 2
def baseEnd_334265 : Nat := 152567654200213262533555

theorem tailTrace_334265 : CollatzResearch.WordTrace tailWord_334265 prefixEnd_334265 152567654200213262533555 := by
  unfold tailWord_334265
  simp only [CollatzResearch.WordTrace]
  refine ⟨12191646134022467762108249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8127764089348311841405499 12191646134022467762108249)
  ·
    refine ⟨9143734600516850821581187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12191646134022467762108249 9143734600516850821581187)
    ·
      refine ⟨13715601900775276232371781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9143734600516850821581187 13715601900775276232371781)
      ·
        refine ⟨2571675356395364293569709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13715601900775276232371781 2571675356395364293569709)
        ·
          refine ⟨964378258648261610088641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2571675356395364293569709 964378258648261610088641)
          ·
            refine ⟨723283693986196207566481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 964378258648261610088641 723283693986196207566481)
            ·
              refine ⟨542462770489647155674861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723283693986196207566481 542462770489647155674861)
              ·
                refine ⟨203423538933617683378073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 542462770489647155674861 203423538933617683378073)
                ·
                  refine ⟨152567654200213262533555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203423538933617683378073 152567654200213262533555)
                  ·
                    rfl

theorem cell20_334265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_334265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334265 prefixEnd_334265 := by exact prefixLift 334265
  have htrace : WordTrace (prefixWord ++ tailWord_334265) baseStart_334265 baseEnd_334265 := by
    simpa [prefixWord, tailWord_334265, baseEnd_334265] using wordTrace_append hprefix tailTrace_334265
  have hstable : (prefixWord ++ tailWord_334265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334265).length < 2 ^ (prefixWord ++ tailWord_334265).sum := by decide
  have hdescent : baseEnd_334265 < baseStart_334265 := by decide
  rcases family_descends (prefixWord ++ tailWord_334265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334279 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 3]
def baseStart_334279 : Nat := 118140960795 + 334279 * 2 ^ 59
def prefixEnd_334279 : Nat := 4983230072969 + 3 ^ 40 * 334279 * 2
def baseEnd_334279 : Nat := 152574044181691436066831

theorem tailTrace_334279 : CollatzResearch.WordTrace tailWord_334279 prefixEnd_334279 152574044181691436066831 := by
  unfold tailWord_334279
  simp only [CollatzResearch.WordTrace]
  refine ⟨12192156755971748153117891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8128104503981165435411927 12192156755971748153117891)
  ·
    refine ⟨18288235133957622229676837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12192156755971748153117891 18288235133957622229676837)
    ·
      refine ⟨3429044087617054168064407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18288235133957622229676837 3429044087617054168064407)
      ·
        refine ⟨5143566131425581252096611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3429044087617054168064407 5143566131425581252096611)
        ·
          refine ⟨7715349197138371878144917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5143566131425581252096611 7715349197138371878144917)
          ·
            refine ⟨361656993615861181788043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7715349197138371878144917 361656993615861181788043)
            ·
              refine ⟨542485490423791772682065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361656993615861181788043 542485490423791772682065)
              ·
                refine ⟨406864117817843829511549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542485490423791772682065 406864117817843829511549)
                ·
                  refine ⟨152574044181691436066831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 406864117817843829511549 152574044181691436066831)
                  ·
                    rfl

theorem cell20_334279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 3].length) (baseStart_334279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334279 prefixEnd_334279 := by exact prefixLift 334279
  have htrace : WordTrace (prefixWord ++ tailWord_334279) baseStart_334279 baseEnd_334279 := by
    simpa [prefixWord, tailWord_334279, baseEnd_334279] using wordTrace_append hprefix tailTrace_334279
  have hstable : (prefixWord ++ tailWord_334279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334279).length < 2 ^ (prefixWord ++ tailWord_334279).sum := by decide
  have hdescent : baseEnd_334279 < baseStart_334279 := by decide
  rcases family_descends (prefixWord ++ tailWord_334279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334306 : List Nat := [3, 3, 3, 2, 1, 2, 2, 4]
def baseStart_334306 : Nat := 118140960795 + 334306 * 2 ^ 59
def prefixEnd_334306 : Nat := 4983230072969 + 3 ^ 40 * 334306 * 2
def baseEnd_334306 : Nat := 50862122572466447388907

theorem tailTrace_334306 : CollatzResearch.WordTrace tailWord_334306 prefixEnd_334306 50862122572466447388907 := by
  unfold tailWord_334306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048285381718482941087693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8128761017915954509567181 3048285381718482941087693)
  ·
    refine ⟨1143107018144431102907885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3048285381718482941087693 1143107018144431102907885)
    ·
      refine ⟨428665131804161663590457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1143107018144431102907885 428665131804161663590457)
      ·
        refine ⟨321498848853121247692843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428665131804161663590457 321498848853121247692843)
        ·
          refine ⟨482248273279681871539265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321498848853121247692843 482248273279681871539265)
          ·
            refine ⟨361686204959761403654449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482248273279681871539265 361686204959761403654449)
            ·
              refine ⟨271264653719821052740837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361686204959761403654449 271264653719821052740837)
              ·
                refine ⟨50862122572466447388907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 271264653719821052740837 50862122572466447388907)
                ·
                  rfl

theorem cell20_334306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_334306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334306 prefixEnd_334306 := by exact prefixLift 334306
  have htrace : WordTrace (prefixWord ++ tailWord_334306) baseStart_334306 baseEnd_334306 := by
    simpa [prefixWord, tailWord_334306, baseEnd_334306] using wordTrace_append hprefix tailTrace_334306
  have hstable : (prefixWord ++ tailWord_334306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334306).length < 2 ^ (prefixWord ++ tailWord_334306).sum := by decide
  have hdescent : baseEnd_334306 < baseStart_334306 := by decide
  rcases family_descends (prefixWord ++ tailWord_334306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334321 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_334321 : Nat := 118140960795 + 334321 * 2 ^ 59
def prefixEnd_334321 : Nat := 4983230072969 + 3 ^ 40 * 334321 * 2
def baseEnd_334321 : Nat := 152593214126125956666659

theorem tailTrace_334321 : CollatzResearch.WordTrace tailWord_334321 prefixEnd_334321 152593214126125956666659 := by
  unfold tailWord_334321
  simp only [CollatzResearch.WordTrace]
  refine ⟨12193688621819589326146817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8129125747879726217431211 12193688621819589326146817)
  ·
    refine ⟨9145266466364691994610113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12193688621819589326146817 9145266466364691994610113)
    ·
      refine ⟨6858949849773518995957585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9145266466364691994610113 6858949849773518995957585)
      ·
        refine ⟨5144212387330139246968189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6858949849773518995957585 5144212387330139246968189)
        ·
          refine ⟨1929079645248802217613071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5144212387330139246968189 1929079645248802217613071)
          ·
            refine ⟨2893619467873203326419607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929079645248802217613071 2893619467873203326419607)
            ·
              refine ⟨4340429201809804989629411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2893619467873203326419607 4340429201809804989629411)
              ·
                refine ⟨6510643802714707484444117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340429201809804989629411 6510643802714707484444117)
                ·
                  refine ⟨152593214126125956666659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6510643802714707484444117 152593214126125956666659)
                  ·
                    rfl

theorem cell20_334321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_334321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334321 prefixEnd_334321 := by exact prefixLift 334321
  have htrace : WordTrace (prefixWord ++ tailWord_334321) baseStart_334321 baseEnd_334321 := by
    simpa [prefixWord, tailWord_334321, baseEnd_334321] using wordTrace_append hprefix tailTrace_334321
  have hstable : (prefixWord ++ tailWord_334321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334321).length < 2 ^ (prefixWord ++ tailWord_334321).sum := by decide
  have hdescent : baseEnd_334321 < baseStart_334321 := by decide
  rcases family_descends (prefixWord ++ tailWord_334321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334396 : List Nat := [2, 2, 2, 2, 3, 3, 2, 2, 2]
def baseStart_334396 : Nat := 118140960795 + 334396 * 2 ^ 59
def prefixEnd_334396 : Nat := 4983230072969 + 3 ^ 40 * 334396 * 2
def baseEnd_334396 : Nat := 152627446169759029166353

theorem tailTrace_334396 : CollatzResearch.WordTrace tailWord_334396 prefixEnd_334396 152627446169759029166353 := by
  unfold tailWord_334396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6098212048273938567563521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8130949397698584756751361 6098212048273938567563521)
  ·
    refine ⟨4573659036205453925672641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6098212048273938567563521 4573659036205453925672641)
    ·
      refine ⟨3430244277154090444254481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4573659036205453925672641 3430244277154090444254481)
      ·
        refine ⟨2572683207865567833190861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3430244277154090444254481 2572683207865567833190861)
        ·
          refine ⟨964756202949587937446573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2572683207865567833190861 964756202949587937446573)
          ·
            refine ⟨361783576106095476542465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 964756202949587937446573 361783576106095476542465)
            ·
              refine ⟨271337682079571607406849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361783576106095476542465 271337682079571607406849)
              ·
                refine ⟨203503261559678705555137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271337682079571607406849 203503261559678705555137)
                ·
                  refine ⟨152627446169759029166353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203503261559678705555137 152627446169759029166353)
                  ·
                    rfl

theorem cell20_334396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_334396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334396 prefixEnd_334396 := by exact prefixLift 334396
  have htrace : WordTrace (prefixWord ++ tailWord_334396) baseStart_334396 baseEnd_334396 := by
    simpa [prefixWord, tailWord_334396, baseEnd_334396] using wordTrace_append hprefix tailTrace_334396
  have hstable : (prefixWord ++ tailWord_334396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334396).length < 2 ^ (prefixWord ++ tailWord_334396).sum := by decide
  have hdescent : baseEnd_334396 < baseStart_334396 := by decide
  rcases family_descends (prefixWord ++ tailWord_334396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334407 : List Nat := [1, 1, 4, 1, 4, 3, 1, 5]
def baseStart_334407 : Nat := 118140960795 + 334407 * 2 ^ 59
def prefixEnd_334407 : Nat := 4983230072969 + 3 ^ 40 * 334407 * 2
def baseEnd_334407 : Nat := 50877488956497293266547

theorem tailTrace_334407 : CollatzResearch.WordTrace tailWord_334407 prefixEnd_334407 50877488956497293266547 := by
  unfold tailWord_334407
  simp only [CollatzResearch.WordTrace]
  refine ⟨12196825299508026013777475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8131216866338684009184983 12196825299508026013777475)
  ·
    refine ⟨18295237949262039020666213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12196825299508026013777475 18295237949262039020666213)
    ·
      refine ⟨3430357115486632316374915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18295237949262039020666213 3430357115486632316374915)
      ·
        refine ⟨5145535673229948474562373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3430357115486632316374915 5145535673229948474562373)
        ·
          refine ⟨964787938730615338980445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5145535673229948474562373 964787938730615338980445)
          ·
            refine ⟨361795477023980752117667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 964787938730615338980445 361795477023980752117667)
            ·
              refine ⟨542693215535971128176501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361795477023980752117667 542693215535971128176501)
              ·
                refine ⟨50877488956497293266547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 542693215535971128176501 50877488956497293266547)
                ·
                  rfl

theorem cell20_334407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 5].length) (baseStart_334407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334407 prefixEnd_334407 := by exact prefixLift 334407
  have htrace : WordTrace (prefixWord ++ tailWord_334407) baseStart_334407 baseEnd_334407 := by
    simpa [prefixWord, tailWord_334407, baseEnd_334407] using wordTrace_append hprefix tailTrace_334407
  have hstable : (prefixWord ++ tailWord_334407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334407).length < 2 ^ (prefixWord ++ tailWord_334407).sum := by decide
  have hdescent : baseEnd_334407 < baseStart_334407 := by decide
  rcases family_descends (prefixWord ++ tailWord_334407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_334414 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_334414 : Nat := 118140960795 + 334414 * 2 ^ 59
def prefixEnd_334414 : Nat := 4983230072969 + 3 ^ 40 * 334414 * 2
def baseEnd_334414 : Nat := 152635661860230966566279

theorem tailTrace_334414 : CollatzResearch.WordTrace tailWord_334414 prefixEnd_334414 152635661860230966566279 := by
  unfold tailWord_334414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524635076310333276160287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8131387073655110806188197 1524635076310333276160287)
  ·
    refine ⟨2286952614465499914240431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1524635076310333276160287 2286952614465499914240431)
    ·
      refine ⟨3430428921698249871360647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2286952614465499914240431 3430428921698249871360647)
      ·
        refine ⟨5145643382547374807040971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3430428921698249871360647 5145643382547374807040971)
        ·
          refine ⟨7718465073821062210561457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5145643382547374807040971 7718465073821062210561457)
          ·
            refine ⟨5788848805365796657921093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7718465073821062210561457 5788848805365796657921093)
            ·
              refine ⟨1085409151006086873360205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5788848805365796657921093 1085409151006086873360205)
              ·
                refine ⟨407028431627282577510077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1085409151006086873360205 407028431627282577510077)
                ·
                  refine ⟨152635661860230966566279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 407028431627282577510077 152635661860230966566279)
                  ·
                    rfl

theorem cell20_334414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_334414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_334414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_334414 prefixEnd_334414 := by exact prefixLift 334414
  have htrace : WordTrace (prefixWord ++ tailWord_334414) baseStart_334414 baseEnd_334414 := by
    simpa [prefixWord, tailWord_334414, baseEnd_334414] using wordTrace_append hprefix tailTrace_334414
  have hstable : (prefixWord ++ tailWord_334414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_334414).length < 2 ^ (prefixWord ++ tailWord_334414).sum := by decide
  have hdescent : baseEnd_334414 < baseStart_334414 := by decide
  rcases family_descends (prefixWord ++ tailWord_334414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
