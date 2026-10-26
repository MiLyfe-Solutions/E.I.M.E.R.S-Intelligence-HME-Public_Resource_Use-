import V185TrunkScan20Chunk021

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_134100 : List Nat := [2, 4, 1, 2, 1, 2, 1, 7]
def baseStart_134100 : Nat := 118140960795 + 134100 * 2 ^ 59
def prefixEnd_134100 : Nat := 4983230072969 + 3 ^ 40 * 134100 * 2
def baseEnd_134100 : Nat := 20402298005342390172827

theorem tailTrace_134100 : CollatzResearch.WordTrace tailWord_134100 prefixEnd_134100 20402298005342390172827 := by
  unfold tailWord_134100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2445514407093038650875877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3260685876124051534501169 2445514407093038650875877)
  ·
    refine ⟨458533951329944747039227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2445514407093038650875877 458533951329944747039227)
    ·
      refine ⟨687800926994917120558841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458533951329944747039227 687800926994917120558841)
      ·
        refine ⟨515850695246187840419131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687800926994917120558841 515850695246187840419131)
        ·
          refine ⟨773776042869281760628697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515850695246187840419131 773776042869281760628697)
          ·
            refine ⟨580332032151961320471523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 773776042869281760628697 580332032151961320471523)
            ·
              refine ⟨870498048227941980707285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580332032151961320471523 870498048227941980707285)
              ·
                refine ⟨20402298005342390172827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 870498048227941980707285 20402298005342390172827)
                ·
                  rfl

theorem cell20_134100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_134100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134100 prefixEnd_134100 := by exact prefixLift 134100
  have htrace : WordTrace (prefixWord ++ tailWord_134100) baseStart_134100 baseEnd_134100 := by
    simpa [prefixWord, tailWord_134100, baseEnd_134100] using wordTrace_append hprefix tailTrace_134100
  have hstable : (prefixWord ++ tailWord_134100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134100).length < 2 ^ (prefixWord ++ tailWord_134100).sum := by decide
  have hdescent : baseEnd_134100 < baseStart_134100 := by decide
  rcases family_descends (prefixWord ++ tailWord_134100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134196 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 3]
def baseStart_134196 : Nat := 118140960795 + 134196 * 2 ^ 59
def prefixEnd_134196 : Nat := 4983230072969 + 3 ^ 40 * 134196 * 2
def baseEnd_134196 : Nat := 61250711031877503318089

theorem tailTrace_134196 : CollatzResearch.WordTrace tailWord_134196 prefixEnd_134196 61250711031877503318089 := by
  unfold tailWord_134196
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447265110919142848623221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3263020147892190464830961 2447265110919142848623221)
  ·
    refine ⟨229431104148669642058427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2447265110919142848623221 229431104148669642058427)
    ·
      refine ⟨344146656223004463087641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229431104148669642058427 344146656223004463087641)
      ·
        refine ⟨258109992167253347315731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344146656223004463087641 258109992167253347315731)
        ·
          refine ⟨387164988250880020973597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258109992167253347315731 387164988250880020973597)
          ·
            refine ⟨145186870594080007865099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387164988250880020973597 145186870594080007865099)
            ·
              refine ⟨217780305891120011797649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145186870594080007865099 217780305891120011797649)
              ·
                refine ⟨163335229418340008848237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217780305891120011797649 163335229418340008848237)
                ·
                  refine ⟨61250711031877503318089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163335229418340008848237 61250711031877503318089)
                  ·
                    rfl

theorem cell20_134196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_134196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134196 prefixEnd_134196 := by exact prefixLift 134196
  have htrace : WordTrace (prefixWord ++ tailWord_134196) baseStart_134196 baseEnd_134196 := by
    simpa [prefixWord, tailWord_134196, baseEnd_134196] using wordTrace_append hprefix tailTrace_134196
  have hstable : (prefixWord ++ tailWord_134196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134196).length < 2 ^ (prefixWord ++ tailWord_134196).sum := by decide
  have hdescent : baseEnd_134196 < baseStart_134196 := by decide
  rcases family_descends (prefixWord ++ tailWord_134196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134200 : List Nat := [2, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_134200 : Nat := 118140960795 + 134200 * 2 ^ 59
def prefixEnd_134200 : Nat := 4983230072969 + 3 ^ 40 * 134200 * 2
def baseEnd_134200 : Nat := 61252536740871267184739

theorem tailTrace_134200 : CollatzResearch.WordTrace tailWord_134200 prefixEnd_134200 61252536740871267184739 := by
  unfold tailWord_134200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2447338056911897190196027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3263117409215862920261369 2447338056911897190196027)
  ·
    refine ⟨3671007085367845785294041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2447338056911897190196027 3671007085367845785294041)
    ·
      refine ⟨2753255314025884338970531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3671007085367845785294041 2753255314025884338970531)
      ·
        refine ⟨4129882971038826508455797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753255314025884338970531 4129882971038826508455797)
        ·
          refine ⟨387176528534889985167731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4129882971038826508455797 387176528534889985167731)
          ·
            refine ⟨580764792802334977751597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387176528534889985167731 580764792802334977751597)
            ·
              refine ⟨217786797300875616656849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580764792802334977751597 217786797300875616656849)
              ·
                refine ⟨163340097975656712492637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217786797300875616656849 163340097975656712492637)
                ·
                  refine ⟨61252536740871267184739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163340097975656712492637 61252536740871267184739)
                  ·
                    rfl

theorem cell20_134200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_134200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134200 prefixEnd_134200 := by exact prefixLift 134200
  have htrace : WordTrace (prefixWord ++ tailWord_134200) baseStart_134200 baseEnd_134200 := by
    simpa [prefixWord, tailWord_134200, baseEnd_134200] using wordTrace_append hprefix tailTrace_134200
  have hstable : (prefixWord ++ tailWord_134200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134200).length < 2 ^ (prefixWord ++ tailWord_134200).sum := by decide
  have hdescent : baseEnd_134200 < baseStart_134200 := by decide
  rcases family_descends (prefixWord ++ tailWord_134200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134237 : List Nat := [1, 4, 4, 1, 3, 1, 1, 3, 2]
def baseStart_134237 : Nat := 118140960795 + 134237 * 2 ^ 59
def prefixEnd_134237 : Nat := 4983230072969 + 3 ^ 40 * 134237 * 2
def baseEnd_134237 : Nat := 61269424549063582951255

theorem tailTrace_134237 : CollatzResearch.WordTrace tailWord_134237 prefixEnd_134237 61269424549063582951255 := by
  unfold tailWord_134237
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896025614689749699488965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3264017076459833132992643 4896025614689749699488965)
  ·
    refine ⟨918004802754328068654181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4896025614689749699488965 918004802754328068654181)
    ·
      refine ⟨172125900516436512872659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 918004802754328068654181 172125900516436512872659)
      ·
        refine ⟨258188850774654769308989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172125900516436512872659 258188850774654769308989)
        ·
          refine ⟨96820819040495538490871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258188850774654769308989 96820819040495538490871)
          ·
            refine ⟨145231228560743307736307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96820819040495538490871 145231228560743307736307)
            ·
              refine ⟨217846842841114961604461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145231228560743307736307 217846842841114961604461)
              ·
                refine ⟨81692566065418110601673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217846842841114961604461 81692566065418110601673)
                ·
                  refine ⟨61269424549063582951255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81692566065418110601673 61269424549063582951255)
                  ·
                    rfl

theorem cell20_134237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_134237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134237 prefixEnd_134237 := by exact prefixLift 134237
  have htrace : WordTrace (prefixWord ++ tailWord_134237) baseStart_134237 baseEnd_134237 := by
    simpa [prefixWord, tailWord_134237, baseEnd_134237] using wordTrace_append hprefix tailTrace_134237
  have hstable : (prefixWord ++ tailWord_134237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134237).length < 2 ^ (prefixWord ++ tailWord_134237).sum := by decide
  have hdescent : baseEnd_134237 < baseStart_134237 := by decide
  rcases family_descends (prefixWord ++ tailWord_134237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134248 : List Nat := [2, 1, 4, 4, 2, 1, 6]
def baseStart_134248 : Nat := 118140960795 + 134248 * 2 ^ 59
def prefixEnd_134248 : Nat := 4983230072969 + 3 ^ 40 * 134248 * 2
def baseEnd_134248 : Nat := 6808271694310714842727

theorem tailTrace_134248 : CollatzResearch.WordTrace tailWord_134248 prefixEnd_134248 6808271694310714842727 := by
  unfold tailWord_134248
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448213408824949289069699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3264284545099932385426265 2448213408824949289069699)
  ·
    refine ⟨3672320113237423933604549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2448213408824949289069699 3672320113237423933604549)
    ·
      refine ⟨688560021232016987550853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3672320113237423933604549 688560021232016987550853)
      ·
        refine ⟨129105003981003185165785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 688560021232016987550853 129105003981003185165785)
        ·
          refine ⟨96828752985752388874339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129105003981003185165785 96828752985752388874339)
          ·
            refine ⟨145243129478628583311509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96828752985752388874339 145243129478628583311509)
            ·
              refine ⟨6808271694310714842727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145243129478628583311509 6808271694310714842727)
              ·
                rfl

theorem cell20_134248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 6].length) (baseStart_134248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134248 prefixEnd_134248 := by exact prefixLift 134248
  have htrace : WordTrace (prefixWord ++ tailWord_134248) baseStart_134248 baseEnd_134248 := by
    simpa [prefixWord, tailWord_134248, baseEnd_134248] using wordTrace_append hprefix tailTrace_134248
  have hstable : (prefixWord ++ tailWord_134248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134248).length < 2 ^ (prefixWord ++ tailWord_134248).sum := by decide
  have hdescent : baseEnd_134248 < baseStart_134248 := by decide
  rcases family_descends (prefixWord ++ tailWord_134248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134276 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_134276 : Nat := 118140960795 + 134276 * 2 ^ 59
def prefixEnd_134276 : Nat := 4983230072969 + 3 ^ 40 * 134276 * 2
def baseEnd_134276 : Nat := 61287225211752780651095

theorem tailTrace_134276 : CollatzResearch.WordTrace tailWord_134276 prefixEnd_134276 61287225211752780651095 := by
  unfold tailWord_134276
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448724030774229680079341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3264965374365639573439121 2448724030774229680079341)
  ·
    refine ⟨918271511540336130029753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2448724030774229680079341 918271511540336130029753)
    ·
      refine ⟨688703633655252097522315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 918271511540336130029753 688703633655252097522315)
      ·
        refine ⟨1033055450482878146283473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688703633655252097522315 1033055450482878146283473)
        ·
          refine ⟨774791587862158609712605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1033055450482878146283473 774791587862158609712605)
          ·
            refine ⟨290546845448309478642227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 774791587862158609712605 290546845448309478642227)
            ·
              refine ⟨435820268172464217963341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290546845448309478642227 435820268172464217963341)
              ·
                refine ⟨163432600564674081736253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435820268172464217963341 163432600564674081736253)
                ·
                  refine ⟨61287225211752780651095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163432600564674081736253 61287225211752780651095)
                  ·
                    rfl

theorem cell20_134276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_134276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134276 prefixEnd_134276 := by exact prefixLift 134276
  have htrace : WordTrace (prefixWord ++ tailWord_134276) baseStart_134276 baseEnd_134276 := by
    simpa [prefixWord, tailWord_134276, baseEnd_134276] using wordTrace_append hprefix tailTrace_134276
  have hstable : (prefixWord ++ tailWord_134276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134276).length < 2 ^ (prefixWord ++ tailWord_134276).sum := by decide
  have hdescent : baseEnd_134276 < baseStart_134276 := by decide
  rcases family_descends (prefixWord ++ tailWord_134276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134290 : List Nat := [3, 2, 3, 1, 1, 2, 2, 6]
def baseStart_134290 : Nat := 118140960795 + 134290 * 2 ^ 59
def prefixEnd_134290 : Nat := 4983230072969 + 3 ^ 40 * 134290 * 2
def baseEnd_134290 : Nat := 20431205064410318061457

theorem tailTrace_134290 : CollatzResearch.WordTrace tailWord_134290 prefixEnd_134290 20431205064410318061457 := by
  unfold tailWord_134290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1224489670874434937792081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3265305788998493167445549 1224489670874434937792081)
  ·
    refine ⟨918367253155826203344061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1224489670874434937792081 918367253155826203344061)
    ·
      refine ⟨344387719933434826254023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 918367253155826203344061 344387719933434826254023)
      ·
        refine ⟨516581579900152239381035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344387719933434826254023 516581579900152239381035)
        ·
          refine ⟨774872369850228359071553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516581579900152239381035 774872369850228359071553)
          ·
            refine ⟨581154277387671269303665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774872369850228359071553 581154277387671269303665)
            ·
              refine ⟨435865708040753451977749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581154277387671269303665 435865708040753451977749)
              ·
                refine ⟨20431205064410318061457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 435865708040753451977749 20431205064410318061457)
                ·
                  rfl

theorem cell20_134290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_134290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134290 prefixEnd_134290 := by exact prefixLift 134290
  have htrace : WordTrace (prefixWord ++ tailWord_134290) baseStart_134290 baseEnd_134290 := by
    simpa [prefixWord, tailWord_134290, baseEnd_134290] using wordTrace_append hprefix tailTrace_134290
  have hstable : (prefixWord ++ tailWord_134290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134290).length < 2 ^ (prefixWord ++ tailWord_134290).sum := by decide
  have hdescent : baseEnd_134290 < baseStart_134290 := by decide
  rcases family_descends (prefixWord ++ tailWord_134290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134317 : List Nat := [1, 5, 2, 1, 3, 1, 1, 4, 2]
def baseStart_134317 : Nat := 118140960795 + 134317 * 2 ^ 59
def prefixEnd_134317 : Nat := 4983230072969 + 3 ^ 40 * 134317 * 2
def baseEnd_134317 : Nat := 61305938728938860284261

theorem tailTrace_134317 : CollatzResearch.WordTrace tailWord_134317 prefixEnd_134317 61305938728938860284261 := by
  unfold tailWord_134317
  simp only [CollatzResearch.WordTrace]
  refine ⟨4898943454399923362401205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3265962302933282241600803 4898943454399923362401205)
  ·
    refine ⟨459275948849992815225113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4898943454399923362401205 459275948849992815225113)
    ·
      refine ⟨344456961637494611418835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 459275948849992815225113 344456961637494611418835)
      ·
        refine ⟨516685442456241917128253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344456961637494611418835 516685442456241917128253)
        ·
          refine ⟨193757040921090718923095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 516685442456241917128253 193757040921090718923095)
          ·
            refine ⟨290635561381636078384643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193757040921090718923095 290635561381636078384643)
            ·
              refine ⟨435953342072454117576965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290635561381636078384643 435953342072454117576965)
              ·
                refine ⟨81741251638585147045681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435953342072454117576965 81741251638585147045681)
                ·
                  refine ⟨61305938728938860284261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81741251638585147045681 61305938728938860284261)
                  ·
                    rfl

theorem cell20_134317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_134317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134317 prefixEnd_134317 := by exact prefixLift 134317
  have htrace : WordTrace (prefixWord ++ tailWord_134317) baseStart_134317 baseEnd_134317 := by
    simpa [prefixWord, tailWord_134317, baseEnd_134317] using wordTrace_append hprefix tailTrace_134317
  have hstable : (prefixWord ++ tailWord_134317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134317).length < 2 ^ (prefixWord ++ tailWord_134317).sum := by decide
  have hdescent : baseEnd_134317 < baseStart_134317 := by decide
  rcases family_descends (prefixWord ++ tailWord_134317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134335 : List Nat := [1, 1, 2, 2, 2, 2, 4, 3, 3]
def baseStart_134335 : Nat := 118140960795 + 134335 * 2 ^ 59
def prefixEnd_134335 : Nat := 4983230072969 + 3 ^ 40 * 134335 * 2
def baseEnd_134335 : Nat := 61314154419410797684187

theorem tailTrace_134335 : CollatzResearch.WordTrace tailWord_134335 prefixEnd_134335 61314154419410797684187 := by
  unfold tailWord_134335
  simp only [CollatzResearch.WordTrace]
  refine ⟨4899599968334712436556459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3266399978889808291037639 4899599968334712436556459)
  ·
    refine ⟨7349399952502068654834689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4899599968334712436556459 7349399952502068654834689)
    ·
      refine ⟨5512049964376551491126017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7349399952502068654834689 5512049964376551491126017)
      ·
        refine ⟨4134037473282413618344513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5512049964376551491126017 4134037473282413618344513)
        ·
          refine ⟨3100528104961810213758385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4134037473282413618344513 3100528104961810213758385)
          ·
            refine ⟨2325396078721357660318789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3100528104961810213758385 2325396078721357660318789)
            ·
              refine ⟨436011764760254561309773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2325396078721357660318789 436011764760254561309773)
              ·
                refine ⟨163504411785095460491165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 436011764760254561309773 163504411785095460491165)
                ·
                  refine ⟨61314154419410797684187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163504411785095460491165 61314154419410797684187)
                  ·
                    rfl

theorem cell20_134335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_134335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134335 prefixEnd_134335 := by exact prefixLift 134335
  have htrace : WordTrace (prefixWord ++ tailWord_134335) baseStart_134335 baseEnd_134335 := by
    simpa [prefixWord, tailWord_134335, baseEnd_134335] using wordTrace_append hprefix tailTrace_134335
  have hstable : (prefixWord ++ tailWord_134335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134335).length < 2 ^ (prefixWord ++ tailWord_134335).sum := by decide
  have hdescent : baseEnd_134335 < baseStart_134335 := by decide
  rcases family_descends (prefixWord ++ tailWord_134335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134359 : List Nat := [1, 1, 3, 2, 1, 2, 3, 5, 2]
def baseStart_134359 : Nat := 118140960795 + 134359 * 2 ^ 59
def prefixEnd_134359 : Nat := 4983230072969 + 3 ^ 40 * 134359 * 2
def baseEnd_134359 : Nat := 61325108673373380884089

theorem tailTrace_134359 : CollatzResearch.WordTrace tailWord_134359 prefixEnd_134359 61325108673373380884089 := by
  unfold tailWord_134359
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900475320247764535430131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3266983546831843023620087 4900475320247764535430131)
  ·
    refine ⟨7350712980371646803145197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4900475320247764535430131 7350712980371646803145197)
    ·
      refine ⟨2756517367639367551179449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7350712980371646803145197 2756517367639367551179449)
      ·
        refine ⟨2067388025729525663384587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2756517367639367551179449 2067388025729525663384587)
        ·
          refine ⟨3101082038594288495076881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2067388025729525663384587 3101082038594288495076881)
          ·
            refine ⟨2325811528945716371307661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3101082038594288495076881 2325811528945716371307661)
            ·
              refine ⟨872179323354643639240373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2325811528945716371307661 872179323354643639240373)
              ·
                refine ⟨81766811564497841178785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 872179323354643639240373 81766811564497841178785)
                ·
                  refine ⟨61325108673373380884089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81766811564497841178785 61325108673373380884089)
                  ·
                    rfl

theorem cell20_134359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 5, 2].length) (baseStart_134359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134359 prefixEnd_134359 := by exact prefixLift 134359
  have htrace : WordTrace (prefixWord ++ tailWord_134359) baseStart_134359 baseEnd_134359 := by
    simpa [prefixWord, tailWord_134359, baseEnd_134359] using wordTrace_append hprefix tailTrace_134359
  have hstable : (prefixWord ++ tailWord_134359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134359).length < 2 ^ (prefixWord ++ tailWord_134359).sum := by decide
  have hdescent : baseEnd_134359 < baseStart_134359 := by decide
  rcases family_descends (prefixWord ++ tailWord_134359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134380 : List Nat := [2, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_134380 : Nat := 118140960795 + 134380 * 2 ^ 59
def prefixEnd_134380 : Nat := 4983230072969 + 3 ^ 40 * 134380 * 2
def baseEnd_134380 : Nat := 61334693645590641184003

theorem tailTrace_134380 : CollatzResearch.WordTrace tailWord_134380 prefixEnd_134380 61334693645590641184003 := by
  unfold tailWord_134380
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450620626585842560972297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3267494168781123414629729 2450620626585842560972297)
  ·
    refine ⟨1837965469939381920729223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2450620626585842560972297 1837965469939381920729223)
    ·
      refine ⟨2756948204909072881093835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1837965469939381920729223 2756948204909072881093835)
      ·
        refine ⟨4135422307363609321640753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2756948204909072881093835 4135422307363609321640753)
        ·
          refine ⟨3101566730522706991230565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4135422307363609321640753 3101566730522706991230565)
          ·
            refine ⟨581543761973007560855731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3101566730522706991230565 581543761973007560855731)
            ·
              refine ⟨872315642959511341283597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581543761973007560855731 872315642959511341283597)
              ·
                refine ⟨327118366109816752981349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 872315642959511341283597 327118366109816752981349)
                ·
                  refine ⟨61334693645590641184003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327118366109816752981349 61334693645590641184003)
                  ·
                    rfl

theorem cell20_134380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_134380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134380 prefixEnd_134380 := by exact prefixLift 134380
  have htrace : WordTrace (prefixWord ++ tailWord_134380) baseStart_134380 baseEnd_134380 := by
    simpa [prefixWord, tailWord_134380, baseEnd_134380] using wordTrace_append hprefix tailTrace_134380
  have hstable : (prefixWord ++ tailWord_134380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134380).length < 2 ^ (prefixWord ++ tailWord_134380).sum := by decide
  have hdescent : baseEnd_134380 < baseStart_134380 := by decide
  rcases family_descends (prefixWord ++ tailWord_134380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134404 : List Nat := [2, 3, 2, 2, 2, 2, 1, 6]
def baseStart_134404 : Nat := 118140960795 + 134404 * 2 ^ 59
def prefixEnd_134404 : Nat := 4983230072969 + 3 ^ 40 * 134404 * 2
def baseEnd_134404 : Nat := 20448549299851074794635

theorem tailTrace_134404 : CollatzResearch.WordTrace tailWord_134404 prefixEnd_134404 20448549299851074794635 := by
  unfold tailWord_134404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451058302542368610409133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3268077736723158147212177 2451058302542368610409133)
  ·
    refine ⟨919146863453388228903425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2451058302542368610409133 919146863453388228903425)
    ·
      refine ⟨689360147590041171677569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 919146863453388228903425 689360147590041171677569)
      ·
        refine ⟨517020110692530878758177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 689360147590041171677569 517020110692530878758177)
        ·
          refine ⟨387765083019398159068633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517020110692530878758177 387765083019398159068633)
          ·
            refine ⟨290823812264548619301475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387765083019398159068633 290823812264548619301475)
            ·
              refine ⟨436235718396822928952213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290823812264548619301475 436235718396822928952213)
              ·
                refine ⟨20448549299851074794635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 436235718396822928952213 20448549299851074794635)
                ·
                  rfl

theorem cell20_134404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_134404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134404 prefixEnd_134404 := by exact prefixLift 134404
  have htrace : WordTrace (prefixWord ++ tailWord_134404) baseStart_134404 baseEnd_134404 := by
    simpa [prefixWord, tailWord_134404, baseEnd_134404] using wordTrace_append hprefix tailTrace_134404
  have hstable : (prefixWord ++ tailWord_134404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134404).length < 2 ^ (prefixWord ++ tailWord_134404).sum := by decide
  have hdescent : baseEnd_134404 < baseStart_134404 := by decide
  rcases family_descends (prefixWord ++ tailWord_134404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134414 : List Nat := [4, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_134414 : Nat := 118140960795 + 134414 * 2 ^ 59
def prefixEnd_134414 : Nat := 4983230072969 + 3 ^ 40 * 134414 * 2
def baseEnd_134414 : Nat := 61350212172037634050531

theorem tailTrace_134414 : CollatzResearch.WordTrace tailWord_134414 prefixEnd_134414 61350212172037634050531 := by
  unfold tailWord_134414
  simp only [CollatzResearch.WordTrace]
  refine ⟨612810166881063616085287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3268320890032339285788197 612810166881063616085287)
  ·
    refine ⟨919215250321595424127931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 612810166881063616085287 919215250321595424127931)
    ·
      refine ⟨1378822875482393136191897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919215250321595424127931 1378822875482393136191897)
      ·
        refine ⟨1034117156611794852143923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1378822875482393136191897 1034117156611794852143923)
        ·
          refine ⟨1551175734917692278215885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034117156611794852143923 1551175734917692278215885)
          ·
            refine ⟨581690900594134604330957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1551175734917692278215885 581690900594134604330957)
            ·
              refine ⟨218134087722800476624109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 581690900594134604330957 218134087722800476624109)
              ·
                refine ⟨81800282896050178734041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218134087722800476624109 81800282896050178734041)
                ·
                  refine ⟨61350212172037634050531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81800282896050178734041 61350212172037634050531)
                  ·
                    rfl

theorem cell20_134414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_134414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134414 prefixEnd_134414 := by exact prefixLift 134414
  have htrace : WordTrace (prefixWord ++ tailWord_134414) baseStart_134414 baseEnd_134414 := by
    simpa [prefixWord, tailWord_134414, baseEnd_134414] using wordTrace_append hprefix tailTrace_134414
  have hstable : (prefixWord ++ tailWord_134414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134414).length < 2 ^ (prefixWord ++ tailWord_134414).sum := by decide
  have hdescent : baseEnd_134414 < baseStart_134414 := by decide
  rcases family_descends (prefixWord ++ tailWord_134414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134431 : List Nat := [1, 1, 2, 4, 4, 1, 3, 2, 2]
def baseStart_134431 : Nat := 118140960795 + 134431 * 2 ^ 59
def prefixEnd_134431 : Nat := 4983230072969 + 3 ^ 40 * 134431 * 2
def baseEnd_134431 : Nat := 61357971435261130483795

theorem tailTrace_134431 : CollatzResearch.WordTrace tailWord_134431 prefixEnd_134431 61357971435261130483795 := by
  unfold tailWord_134431
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903101375986920832051147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3268734250657947221367431 4903101375986920832051147)
  ·
    refine ⟨7354652063980381248076721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4903101375986920832051147 7354652063980381248076721)
    ·
      refine ⟨5515989047985285936057541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7354652063980381248076721 5515989047985285936057541)
      ·
        refine ⟨1034247946497241113010789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5515989047985285936057541 1034247946497241113010789)
        ·
          refine ⟨193921489968232708689523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1034247946497241113010789 193921489968232708689523)
          ·
            refine ⟨290882234952349063034285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193921489968232708689523 290882234952349063034285)
            ·
              refine ⟨109080838107130898637857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290882234952349063034285 109080838107130898637857)
              ·
                refine ⟨81810628580348173978393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109080838107130898637857 81810628580348173978393)
                ·
                  refine ⟨61357971435261130483795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81810628580348173978393 61357971435261130483795)
                  ·
                    rfl

theorem cell20_134431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 2].length) (baseStart_134431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134431 prefixEnd_134431 := by exact prefixLift 134431
  have htrace : WordTrace (prefixWord ++ tailWord_134431) baseStart_134431 baseEnd_134431 := by
    simpa [prefixWord, tailWord_134431, baseEnd_134431] using wordTrace_append hprefix tailTrace_134431
  have hstable : (prefixWord ++ tailWord_134431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134431).length < 2 ^ (prefixWord ++ tailWord_134431).sum := by decide
  have hdescent : baseEnd_134431 < baseStart_134431 := by decide
  rcases family_descends (prefixWord ++ tailWord_134431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134435 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 4]
def baseStart_134435 : Nat := 118140960795 + 134435 * 2 ^ 59
def prefixEnd_134435 : Nat := 4983230072969 + 3 ^ 40 * 134435 * 2
def baseEnd_134435 : Nat := 61359797144254894350445

theorem tailTrace_134435 : CollatzResearch.WordTrace tailWord_134435 prefixEnd_134435 61359797144254894350445 := by
  unfold tailWord_134435
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903247267972429515196759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3268831511981619676797839 4903247267972429515196759)
  ·
    refine ⟨7354870901958644272795139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4903247267972429515196759 7354870901958644272795139)
    ·
      refine ⟨11032306352937966409192709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7354870901958644272795139 11032306352937966409192709)
      ·
        refine ⟨2068557441175868701723633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11032306352937966409192709 2068557441175868701723633)
        ·
          refine ⟨1551418080881901526292725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2068557441175868701723633 1551418080881901526292725)
          ·
            refine ⟨145445445082678268089943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1551418080881901526292725 145445445082678268089943)
            ·
              refine ⟨218168167624017402134915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145445445082678268089943 218168167624017402134915)
              ·
                refine ⟨327252251436026103202373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218168167624017402134915 327252251436026103202373)
                ·
                  refine ⟨61359797144254894350445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327252251436026103202373 61359797144254894350445)
                  ·
                    rfl

theorem cell20_134435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 4].length) (baseStart_134435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134435 prefixEnd_134435 := by exact prefixLift 134435
  have htrace : WordTrace (prefixWord ++ tailWord_134435) baseStart_134435 baseEnd_134435 := by
    simpa [prefixWord, tailWord_134435, baseEnd_134435] using wordTrace_append hprefix tailTrace_134435
  have hstable : (prefixWord ++ tailWord_134435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134435).length < 2 ^ (prefixWord ++ tailWord_134435).sum := by decide
  have hdescent : baseEnd_134435 < baseStart_134435 := by decide
  rcases family_descends (prefixWord ++ tailWord_134435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134442 : List Nat := [3, 1, 4, 2, 1, 1, 1, 7]
def baseStart_134442 : Nat := 118140960795 + 134442 * 2 ^ 59
def prefixEnd_134442 : Nat := 4983230072969 + 3 ^ 40 * 134442 * 2
def baseEnd_134442 : Nat := 20454330711664660372361

theorem tailTrace_134442 : CollatzResearch.WordTrace tailWord_134442 prefixEnd_134442 20454330711664660372361 := by
  unfold tailWord_134442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225875644736767427675395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3269001719298046473801053 1225875644736767427675395)
  ·
    refine ⟨1838813467105151141513093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1225875644736767427675395 1838813467105151141513093)
    ·
      refine ⟨344777525082215839033705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1838813467105151141513093 344777525082215839033705)
      ·
        refine ⟨258583143811661879275279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344777525082215839033705 258583143811661879275279)
        ·
          refine ⟨387874715717492818912919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258583143811661879275279 387874715717492818912919)
          ·
            refine ⟨581812073576239228369379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387874715717492818912919 581812073576239228369379)
            ·
              refine ⟨872718110364358842554069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581812073576239228369379 872718110364358842554069)
              ·
                refine ⟨20454330711664660372361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 872718110364358842554069 20454330711664660372361)
                ·
                  rfl

theorem cell20_134442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_134442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134442 prefixEnd_134442 := by exact prefixLift 134442
  have htrace : WordTrace (prefixWord ++ tailWord_134442) baseStart_134442 baseEnd_134442 := by
    simpa [prefixWord, tailWord_134442, baseEnd_134442] using wordTrace_append hprefix tailTrace_134442
  have hstable : (prefixWord ++ tailWord_134442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134442).length < 2 ^ (prefixWord ++ tailWord_134442).sum := by decide
  have hdescent : baseEnd_134442 < baseStart_134442 := by decide
  rcases family_descends (prefixWord ++ tailWord_134442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134445 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 3]
def baseStart_134445 : Nat := 118140960795 + 134445 * 2 ^ 59
def prefixEnd_134445 : Nat := 4983230072969 + 3 ^ 40 * 134445 * 2
def baseEnd_134445 : Nat := 61364361416739304017071

theorem tailTrace_134445 : CollatzResearch.WordTrace tailWord_134445 prefixEnd_134445 61364361416739304017071 := by
  unfold tailWord_134445
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903611997936201223060789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3269074665290800815373859 4903611997936201223060789)
  ·
    refine ⟨459713624806518864661949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4903611997936201223060789 459713624806518864661949)
    ·
      refine ⟨172392609302444574248231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 459713624806518864661949 172392609302444574248231)
      ·
        refine ⟨258588913953666861372347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172392609302444574248231 258588913953666861372347)
        ·
          refine ⟨387883370930500292058521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258588913953666861372347 387883370930500292058521)
          ·
            refine ⟨290912528197875219043891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387883370930500292058521 290912528197875219043891)
            ·
              refine ⟨436368792296812828565837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290912528197875219043891 436368792296812828565837)
              ·
                refine ⟨163638297111304810712189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 436368792296812828565837 163638297111304810712189)
                ·
                  refine ⟨61364361416739304017071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163638297111304810712189 61364361416739304017071)
                  ·
                    rfl

theorem cell20_134445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_134445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134445 prefixEnd_134445 := by exact prefixLift 134445
  have htrace : WordTrace (prefixWord ++ tailWord_134445) baseStart_134445 baseEnd_134445 := by
    simpa [prefixWord, tailWord_134445, baseEnd_134445] using wordTrace_append hprefix tailTrace_134445
  have hstable : (prefixWord ++ tailWord_134445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134445).length < 2 ^ (prefixWord ++ tailWord_134445).sum := by decide
  have hdescent : baseEnd_134445 < baseStart_134445 := by decide
  rcases family_descends (prefixWord ++ tailWord_134445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134463 : List Nat := [1, 1, 2, 2, 4, 2, 2, 6]
def baseStart_134463 : Nat := 118140960795 + 134463 * 2 ^ 59
def prefixEnd_134463 : Nat := 4983230072969 + 3 ^ 40 * 134463 * 2
def baseEnd_134463 : Nat := 20457525702403747138999

theorem tailTrace_134463 : CollatzResearch.WordTrace tailWord_134463 prefixEnd_134463 20457525702403747138999 := by
  unfold tailWord_134463
  simp only [CollatzResearch.WordTrace]
  refine ⟨4904268511870990297216043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3269512341247326864810695 4904268511870990297216043)
  ·
    refine ⟨7356402767806485445824065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4904268511870990297216043 7356402767806485445824065)
    ·
      refine ⟨5517302075854864084368049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7356402767806485445824065 5517302075854864084368049)
      ·
        refine ⟨4137976556891148063276037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5517302075854864084368049 4137976556891148063276037)
        ·
          refine ⟨775870604417090261864257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4137976556891148063276037 775870604417090261864257)
          ·
            refine ⟨581902953312817696398193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775870604417090261864257 581902953312817696398193)
            ·
              refine ⟨436427214984613272298645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581902953312817696398193 436427214984613272298645)
              ·
                refine ⟨20457525702403747138999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 436427214984613272298645 20457525702403747138999)
                ·
                  rfl

theorem cell20_134463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_134463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134463 prefixEnd_134463 := by exact prefixLift 134463
  have htrace : WordTrace (prefixWord ++ tailWord_134463) baseStart_134463 baseEnd_134463 := by
    simpa [prefixWord, tailWord_134463, baseEnd_134463] using wordTrace_append hprefix tailTrace_134463
  have hstable : (prefixWord ++ tailWord_134463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134463).length < 2 ^ (prefixWord ++ tailWord_134463).sum := by decide
  have hdescent : baseEnd_134463 < baseStart_134463 := by decide
  rcases family_descends (prefixWord ++ tailWord_134463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134487 : List Nat := [1, 1, 3, 2, 3, 2, 1, 4, 3]
def baseStart_134487 : Nat := 118140960795 + 134487 * 2 ^ 59
def prefixEnd_134487 : Nat := 4983230072969 + 3 ^ 40 * 134487 * 2
def baseEnd_134487 : Nat := 61383531361173824616899

theorem tailTrace_134487 : CollatzResearch.WordTrace tailWord_134487 prefixEnd_134487 61383531361173824616899 := by
  unfold tailWord_134487
  simp only [CollatzResearch.WordTrace]
  refine ⟨4905143863784042396089715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3270095909189361597393143 4905143863784042396089715)
  ·
    refine ⟨7357715795676063594134573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4905143863784042396089715 7357715795676063594134573)
    ·
      refine ⟨2759143423378523847800465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7357715795676063594134573 2759143423378523847800465)
      ·
        refine ⟨2069357567533892885850349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2759143423378523847800465 2069357567533892885850349)
        ·
          refine ⟨776009087825209832193881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2069357567533892885850349 776009087825209832193881)
          ·
            refine ⟨582006815868907374145411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776009087825209832193881 582006815868907374145411)
            ·
              refine ⟨873010223803361061218117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582006815868907374145411 873010223803361061218117)
              ·
                refine ⟨163689416963130198978397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 873010223803361061218117 163689416963130198978397)
                ·
                  refine ⟨61383531361173824616899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163689416963130198978397 61383531361173824616899)
                  ·
                    rfl

theorem cell20_134487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_134487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134487 prefixEnd_134487 := by exact prefixLift 134487
  have htrace : WordTrace (prefixWord ++ tailWord_134487) baseStart_134487 baseEnd_134487 := by
    simpa [prefixWord, tailWord_134487, baseEnd_134487] using wordTrace_append hprefix tailTrace_134487
  have hstable : (prefixWord ++ tailWord_134487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134487).length < 2 ^ (prefixWord ++ tailWord_134487).sum := by decide
  have hdescent : baseEnd_134487 < baseStart_134487 := by decide
  rcases family_descends (prefixWord ++ tailWord_134487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134490 : List Nat := [3, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_134490 : Nat := 118140960795 + 134490 * 2 ^ 59
def prefixEnd_134490 : Nat := 4983230072969 + 3 ^ 40 * 134490 * 2
def baseEnd_134490 : Nat := 61384900642919147516887

theorem tailTrace_134490 : CollatzResearch.WordTrace tailWord_134490 prefixEnd_134490 61384900642919147516887 := by
  unfold tailWord_134490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226313320693293477112231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3270168855182115938965949 1226313320693293477112231)
  ·
    refine ⟨1839469981039940215668347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1226313320693293477112231 1839469981039940215668347)
    ·
      refine ⟨2759204971559910323502521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1839469981039940215668347 2759204971559910323502521)
      ·
        refine ⟨2069403728669932742626891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2759204971559910323502521 2069403728669932742626891)
        ·
          refine ⟨3104105593004899113940337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069403728669932742626891 3104105593004899113940337)
          ·
            refine ⟨2328079194753674335455253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3104105593004899113940337 2328079194753674335455253)
            ·
              refine ⟨109128712254078484474465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2328079194753674335455253 109128712254078484474465)
              ·
                refine ⟨81846534190558863355849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109128712254078484474465 81846534190558863355849)
                ·
                  refine ⟨61384900642919147516887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81846534190558863355849 61384900642919147516887)
                  ·
                    rfl

theorem cell20_134490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_134490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134490 prefixEnd_134490 := by exact prefixLift 134490
  have htrace : WordTrace (prefixWord ++ tailWord_134490) baseStart_134490 baseEnd_134490 := by
    simpa [prefixWord, tailWord_134490, baseEnd_134490] using wordTrace_append hprefix tailTrace_134490
  have hstable : (prefixWord ++ tailWord_134490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134490).length < 2 ^ (prefixWord ++ tailWord_134490).sum := by decide
  have hdescent : baseEnd_134490 < baseStart_134490 := by decide
  rcases family_descends (prefixWord ++ tailWord_134490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134493 : List Nat := [1, 4, 5, 1, 1, 2, 1, 5]
def baseStart_134493 : Nat := 118140960795 + 134493 * 2 ^ 59
def prefixEnd_134493 : Nat := 4983230072969 + 3 ^ 40 * 134493 * 2
def baseEnd_134493 : Nat := 20462089974888156805625

theorem tailTrace_134493 : CollatzResearch.WordTrace tailWord_134493 prefixEnd_134493 20462089974888156805625 := by
  unfold tailWord_134493
  simp only [CollatzResearch.WordTrace]
  refine ⟨4905362701762305420808133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3270241801174870280538755 4905362701762305420808133)
  ·
    refine ⟨919755506580432266401525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4905362701762305420808133 919755506580432266401525)
    ·
      refine ⟨86227078741915524975143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 919755506580432266401525 86227078741915524975143)
      ·
        refine ⟨129340618112873287462715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86227078741915524975143 129340618112873287462715)
        ·
          refine ⟨194010927169309931194073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129340618112873287462715 194010927169309931194073)
          ·
            refine ⟨145508195376982448395555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194010927169309931194073 145508195376982448395555)
            ·
              refine ⟨218262293065473672593333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145508195376982448395555 218262293065473672593333)
              ·
                refine ⟨20462089974888156805625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218262293065473672593333 20462089974888156805625)
                ·
                  rfl

theorem cell20_134493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 5].length) (baseStart_134493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134493 prefixEnd_134493 := by exact prefixLift 134493
  have htrace : WordTrace (prefixWord ++ tailWord_134493) baseStart_134493 baseEnd_134493 := by
    simpa [prefixWord, tailWord_134493, baseEnd_134493] using wordTrace_append hprefix tailTrace_134493
  have hstable : (prefixWord ++ tailWord_134493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134493).length < 2 ^ (prefixWord ++ tailWord_134493).sum := by decide
  have hdescent : baseEnd_134493 < baseStart_134493 := by decide
  rcases family_descends (prefixWord ++ tailWord_134493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134542 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_134542 : Nat := 118140960795 + 134542 * 2 ^ 59
def prefixEnd_134542 : Nat := 4983230072969 + 3 ^ 40 * 134542 * 2
def baseEnd_134542 : Nat := 61408634859838077783341

theorem tailTrace_134542 : CollatzResearch.WordTrace tailWord_134542 prefixEnd_134542 61408634859838077783341 := by
  unfold tailWord_134542
  simp only [CollatzResearch.WordTrace]
  refine ⟨613393734823098348667735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3271433252389857859561253 613393734823098348667735)
  ·
    refine ⟨920090602234647523001603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 613393734823098348667735 920090602234647523001603)
    ·
      refine ⟨1380135903351971284502405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 920090602234647523001603 1380135903351971284502405)
      ·
        refine ⟨258775481878494615844201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1380135903351971284502405 258775481878494615844201)
        ·
          refine ⟨194081611408870961883151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258775481878494615844201 194081611408870961883151)
          ·
            refine ⟨291122417113306442824727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194081611408870961883151 291122417113306442824727)
            ·
              refine ⟨436683625669959664237091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291122417113306442824727 436683625669959664237091)
              ·
                refine ⟨655025438504939496355637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436683625669959664237091 655025438504939496355637)
                ·
                  refine ⟨61408634859838077783341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 655025438504939496355637 61408634859838077783341)
                  ·
                    rfl

theorem cell20_134542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_134542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134542 prefixEnd_134542 := by exact prefixLift 134542
  have htrace : WordTrace (prefixWord ++ tailWord_134542) baseStart_134542 baseEnd_134542 := by
    simpa [prefixWord, tailWord_134542, baseEnd_134542] using wordTrace_append hprefix tailTrace_134542
  have hstable : (prefixWord ++ tailWord_134542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134542).length < 2 ^ (prefixWord ++ tailWord_134542).sum := by decide
  have hdescent : baseEnd_134542 < baseStart_134542 := by decide
  rcases family_descends (prefixWord ++ tailWord_134542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134549 : List Nat := [1, 3, 2, 1, 1, 2, 4, 4, 2]
def baseStart_134549 : Nat := 118140960795 + 134549 * 2 ^ 59
def prefixEnd_134549 : Nat := 4983230072969 + 3 ^ 40 * 134549 * 2
def baseEnd_134549 : Nat := 61411829850577164549979

theorem tailTrace_134549 : CollatzResearch.WordTrace tailWord_134549 prefixEnd_134549 61411829850577164549979 := by
  unfold tailWord_134549
  simp only [CollatzResearch.WordTrace]
  refine ⟨4907405189559426984846701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3271603459706284656564467 4907405189559426984846701)
  ·
    refine ⟨1840276946084785119317513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4907405189559426984846701 1840276946084785119317513)
    ·
      refine ⟨1380207709563588839488135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1840276946084785119317513 1380207709563588839488135)
      ·
        refine ⟨2070311564345383259232203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380207709563588839488135 2070311564345383259232203)
        ·
          refine ⟨3105467346518074888848305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070311564345383259232203 3105467346518074888848305)
          ·
            refine ⟨2329100509888556166636229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3105467346518074888848305 2329100509888556166636229)
            ·
              refine ⟨436706345604104281244293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2329100509888556166636229 436706345604104281244293)
              ·
                refine ⟨81882439800769552733305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436706345604104281244293 81882439800769552733305)
                ·
                  refine ⟨61411829850577164549979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81882439800769552733305 61411829850577164549979)
                  ·
                    rfl

theorem cell20_134549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_134549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134549 prefixEnd_134549 := by exact prefixLift 134549
  have htrace : WordTrace (prefixWord ++ tailWord_134549) baseStart_134549 baseEnd_134549 := by
    simpa [prefixWord, tailWord_134549, baseEnd_134549] using wordTrace_append hprefix tailTrace_134549
  have hstable : (prefixWord ++ tailWord_134549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134549).length < 2 ^ (prefixWord ++ tailWord_134549).sum := by decide
  have hdescent : baseEnd_134549 < baseStart_134549 := by decide
  rcases family_descends (prefixWord ++ tailWord_134549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134573 : List Nat := [1, 5, 2, 2, 1, 1, 4, 4]
def baseStart_134573 : Nat := 118140960795 + 134573 * 2 ^ 59
def prefixEnd_134573 : Nat := 4983230072969 + 3 ^ 40 * 134573 * 2
def baseEnd_134573 : Nat := 20474261368179915916627

theorem tailTrace_134573 : CollatzResearch.WordTrace tailWord_134573 prefixEnd_134573 20474261368179915916627 := by
  unfold tailWord_134573
  simp only [CollatzResearch.WordTrace]
  refine ⟨4908280541472479083720373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3272187027648319389146915 4908280541472479083720373)
  ·
    refine ⟨460151300763044914098785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4908280541472479083720373 460151300763044914098785)
    ·
      refine ⟨345113475572283685574089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 460151300763044914098785 345113475572283685574089)
      ·
        refine ⟨258835106679212764180567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345113475572283685574089 258835106679212764180567)
        ·
          refine ⟨388252660018819146270851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258835106679212764180567 388252660018819146270851)
          ·
            refine ⟨582378990028228719406277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388252660018819146270851 582378990028228719406277)
            ·
              refine ⟨109196060630292884888677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 582378990028228719406277 109196060630292884888677)
              ·
                refine ⟨20474261368179915916627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109196060630292884888677 20474261368179915916627)
                ·
                  rfl

theorem cell20_134573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 4].length) (baseStart_134573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134573 prefixEnd_134573 := by exact prefixLift 134573
  have htrace : WordTrace (prefixWord ++ tailWord_134573) baseStart_134573 baseEnd_134573 := by
    simpa [prefixWord, tailWord_134573, baseEnd_134573] using wordTrace_append hprefix tailTrace_134573
  have hstable : (prefixWord ++ tailWord_134573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134573).length < 2 ^ (prefixWord ++ tailWord_134573).sum := by decide
  have hdescent : baseEnd_134573 < baseStart_134573 := by decide
  rcases family_descends (prefixWord ++ tailWord_134573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134577 : List Nat := [1, 2, 2, 4, 1, 1, 3, 6]
def baseStart_134577 : Nat := 118140960795 + 134577 * 2 ^ 59
def prefixEnd_134577 : Nat := 4983230072969 + 3 ^ 40 * 134577 * 2
def baseEnd_134577 : Nat := 20474869937844503872177

theorem tailTrace_134577 : CollatzResearch.WordTrace tailWord_134577 prefixEnd_134577 20474869937844503872177 := by
  unfold tailWord_134577
  simp only [CollatzResearch.WordTrace]
  refine ⟨4908426433457987766865985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3272284288971991844577323 4908426433457987766865985)
  ·
    refine ⟨3681319825093490825149489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4908426433457987766865985 3681319825093490825149489)
    ·
      refine ⟨2760989868820118118862117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3681319825093490825149489 2760989868820118118862117)
      ·
        refine ⟨517685600403772147286647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2760989868820118118862117 517685600403772147286647)
        ·
          refine ⟨776528400605658220929971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517685600403772147286647 776528400605658220929971)
          ·
            refine ⟨1164792600908487331394957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776528400605658220929971 1164792600908487331394957)
            ·
              refine ⟨436797225340682749273109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1164792600908487331394957 436797225340682749273109)
              ·
                refine ⟨20474869937844503872177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 436797225340682749273109 20474869937844503872177)
                ·
                  rfl

theorem cell20_134577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_134577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134577 prefixEnd_134577 := by exact prefixLift 134577
  have htrace : WordTrace (prefixWord ++ tailWord_134577) baseStart_134577 baseEnd_134577 := by
    simpa [prefixWord, tailWord_134577, baseEnd_134577] using wordTrace_append hprefix tailTrace_134577
  have hstable : (prefixWord ++ tailWord_134577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134577).length < 2 ^ (prefixWord ++ tailWord_134577).sum := by decide
  have hdescent : baseEnd_134577 < baseStart_134577 := by decide
  rcases family_descends (prefixWord ++ tailWord_134577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134584 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_134584 : Nat := 118140960795 + 134584 * 2 ^ 59
def prefixEnd_134584 : Nat := 4983230072969 + 3 ^ 40 * 134584 * 2
def baseEnd_134584 : Nat := 61427804804272598383169

theorem tailTrace_134584 : CollatzResearch.WordTrace tailWord_134584 prefixEnd_134584 61427804804272598383169 := by
  unfold tailWord_134584
  simp only [CollatzResearch.WordTrace]
  refine ⟨2454340872216313981185403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3272454496288418641580537 2454340872216313981185403)
  ·
    refine ⟨3681511308324470971778105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2454340872216313981185403 3681511308324470971778105)
    ·
      refine ⟨2761133481243353228833579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3681511308324470971778105 2761133481243353228833579)
      ·
        refine ⟨4141700221865029843250369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2761133481243353228833579 4141700221865029843250369)
        ·
          refine ⟨3106275166398772382437777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4141700221865029843250369 3106275166398772382437777)
          ·
            refine ⟨2329706374799079286828333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3106275166398772382437777 2329706374799079286828333)
            ·
              refine ⟨873639890549654732560625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2329706374799079286828333 873639890549654732560625)
              ·
                refine ⟨655229917912241049420469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873639890549654732560625 655229917912241049420469)
                ·
                  refine ⟨61427804804272598383169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 655229917912241049420469 61427804804272598383169)
                  ·
                    rfl

theorem cell20_134584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_134584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134584 prefixEnd_134584 := by exact prefixLift 134584
  have htrace : WordTrace (prefixWord ++ tailWord_134584) baseStart_134584 baseEnd_134584 := by
    simpa [prefixWord, tailWord_134584, baseEnd_134584] using wordTrace_append hprefix tailTrace_134584
  have hstable : (prefixWord ++ tailWord_134584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134584).length < 2 ^ (prefixWord ++ tailWord_134584).sum := by decide
  have hdescent : baseEnd_134584 < baseStart_134584 := by decide
  rcases family_descends (prefixWord ++ tailWord_134584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134591 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_134591 : Nat := 118140960795 + 134591 * 2 ^ 59
def prefixEnd_134591 : Nat := 4983230072969 + 3 ^ 40 * 134591 * 2
def baseEnd_134591 : Nat := 61430999795011685149807

theorem tailTrace_134591 : CollatzResearch.WordTrace tailWord_134591 prefixEnd_134591 61430999795011685149807 := by
  unfold tailWord_134591
  simp only [CollatzResearch.WordTrace]
  refine ⟨4908937055407268157875627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3272624703604845438583751 4908937055407268157875627)
  ·
    refine ⟨7363405583110902236813441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4908937055407268157875627 7363405583110902236813441)
    ·
      refine ⟨5522554187333176677610081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7363405583110902236813441 5522554187333176677610081)
      ·
        refine ⟨4141915640499882508207561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5522554187333176677610081 4141915640499882508207561)
        ·
          refine ⟨3106436730374911881155671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4141915640499882508207561 3106436730374911881155671)
          ·
            refine ⟨4659655095562367821733507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106436730374911881155671 4659655095562367821733507)
            ·
              refine ⟨6989482643343551732600261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4659655095562367821733507 6989482643343551732600261)
              ·
                refine ⟨1310527995626915949862549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6989482643343551732600261 1310527995626915949862549)
                ·
                  refine ⟨61430999795011685149807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1310527995626915949862549 61430999795011685149807)
                  ·
                    rfl

theorem cell20_134591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_134591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134591 prefixEnd_134591 := by exact prefixLift 134591
  have htrace : WordTrace (prefixWord ++ tailWord_134591) baseStart_134591 baseEnd_134591 := by
    simpa [prefixWord, tailWord_134591, baseEnd_134591] using wordTrace_append hprefix tailTrace_134591
  have hstable : (prefixWord ++ tailWord_134591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134591).length < 2 ^ (prefixWord ++ tailWord_134591).sum := by decide
  have hdescent : baseEnd_134591 < baseStart_134591 := by decide
  rcases family_descends (prefixWord ++ tailWord_134591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134614 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_134614 : Nat := 118140960795 + 134614 * 2 ^ 59
def prefixEnd_134614 : Nat := 4983230072969 + 3 ^ 40 * 134614 * 2
def baseEnd_134614 : Nat := 61441497621725827383047

theorem tailTrace_134614 : CollatzResearch.WordTrace tailWord_134614 prefixEnd_134614 61441497621725827383047 := by
  unfold tailWord_134614
  simp only [CollatzResearch.WordTrace]
  refine ⟨306860995895246442872681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3273183956215962057308597 306860995895246442872681)
  ·
    refine ⟨230145746921434832154511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 306860995895246442872681 230145746921434832154511)
    ·
      refine ⟨345218620382152248231767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230145746921434832154511 345218620382152248231767)
      ·
        refine ⟨517827930573228372347651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345218620382152248231767 517827930573228372347651)
        ·
          refine ⟨776741895859842558521477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517827930573228372347651 776741895859842558521477)
          ·
            refine ⟨145639105473720479722777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 776741895859842558521477 145639105473720479722777)
            ·
              refine ⟨109229329105290359792083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145639105473720479722777 109229329105290359792083)
              ·
                refine ⟨163843993657935539688125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109229329105290359792083 163843993657935539688125)
                ·
                  refine ⟨61441497621725827383047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163843993657935539688125 61441497621725827383047)
                  ·
                    rfl

theorem cell20_134614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_134614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134614 prefixEnd_134614 := by exact prefixLift 134614
  have htrace : WordTrace (prefixWord ++ tailWord_134614) baseStart_134614 baseEnd_134614 := by
    simpa [prefixWord, tailWord_134614, baseEnd_134614] using wordTrace_append hprefix tailTrace_134614
  have hstable : (prefixWord ++ tailWord_134614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134614).length < 2 ^ (prefixWord ++ tailWord_134614).sum := by decide
  have hdescent : baseEnd_134614 < baseStart_134614 := by decide
  rcases family_descends (prefixWord ++ tailWord_134614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134618 : List Nat := [3, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_134618 : Nat := 118140960795 + 134618 * 2 ^ 59
def prefixEnd_134618 : Nat := 4983230072969 + 3 ^ 40 * 134618 * 2
def baseEnd_134618 : Nat := 61443323330719591249697

theorem tailTrace_134618 : CollatzResearch.WordTrace tailWord_134618 prefixEnd_134618 61443323330719591249697 := by
  unfold tailWord_134618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1227480456577362942277127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3273281217539634512739005 1227480456577362942277127)
  ·
    refine ⟨1841220684866044413415691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1227480456577362942277127 1841220684866044413415691)
    ·
      refine ⟨2761831027299066620123537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1841220684866044413415691 2761831027299066620123537)
      ·
        refine ⟨2071373270474299965092653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2761831027299066620123537 2071373270474299965092653)
        ·
          refine ⟨776764976427862486909745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2071373270474299965092653 776764976427862486909745)
          ·
            refine ⟨582573732320896865182309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776764976427862486909745 582573732320896865182309)
            ·
              refine ⟨109232574810168162221683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 582573732320896865182309 109232574810168162221683)
              ·
                refine ⟨163848862215252243332525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109232574810168162221683 163848862215252243332525)
                ·
                  refine ⟨61443323330719591249697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163848862215252243332525 61443323330719591249697)
                  ·
                    rfl

theorem cell20_134618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_134618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134618 prefixEnd_134618 := by exact prefixLift 134618
  have htrace : WordTrace (prefixWord ++ tailWord_134618) baseStart_134618 baseEnd_134618 := by
    simpa [prefixWord, tailWord_134618, baseEnd_134618] using wordTrace_append hprefix tailTrace_134618
  have hstable : (prefixWord ++ tailWord_134618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134618).length < 2 ^ (prefixWord ++ tailWord_134618).sum := by decide
  have hdescent : baseEnd_134618 < baseStart_134618 := by decide
  rcases family_descends (prefixWord ++ tailWord_134618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134662 : List Nat := [6, 2, 1, 1, 3, 1, 1, 5]
def baseStart_134662 : Nat := 118140960795 + 134662 * 2 ^ 59
def prefixEnd_134662 : Nat := 4983230072969 + 3 ^ 40 * 134662 * 2
def baseEnd_134662 : Nat := 20487802043216997927617

theorem tailTrace_134662 : CollatzResearch.WordTrace tailWord_134662 prefixEnd_134662 20487802043216997927617 := by
  unfold tailWord_134662
  simp only [CollatzResearch.WordTrace]
  refine ⟨153485207442188977615945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3274351092100031522473493 153485207442188977615945)
  ·
    refine ⟨115113905581641733211959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153485207442188977615945 115113905581641733211959)
    ·
      refine ⟨172670858372462599817939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115113905581641733211959 172670858372462599817939)
      ·
        refine ⟨259006287558693899726909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172670858372462599817939 259006287558693899726909)
        ·
          refine ⟨97127357834510212397591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259006287558693899726909 97127357834510212397591)
          ·
            refine ⟨145691036751765318596387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97127357834510212397591 145691036751765318596387)
            ·
              refine ⟨218536555127647977894581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145691036751765318596387 218536555127647977894581)
              ·
                refine ⟨20487802043216997927617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218536555127647977894581 20487802043216997927617)
                ·
                  rfl

theorem cell20_134662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_134662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134662 prefixEnd_134662 := by exact prefixLift 134662
  have htrace : WordTrace (prefixWord ++ tailWord_134662) baseStart_134662 baseEnd_134662 := by
    simpa [prefixWord, tailWord_134662, baseEnd_134662] using wordTrace_append hprefix tailTrace_134662
  have hstable : (prefixWord ++ tailWord_134662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134662).length < 2 ^ (prefixWord ++ tailWord_134662).sum := by decide
  have hdescent : baseEnd_134662 < baseStart_134662 := by decide
  rcases family_descends (prefixWord ++ tailWord_134662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134677 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 3]
def baseStart_134677 : Nat := 118140960795 + 134677 * 2 ^ 59
def prefixEnd_134677 : Nat := 4983230072969 + 3 ^ 40 * 134677 * 2
def baseEnd_134677 : Nat := 61470252538377608282789

theorem tailTrace_134677 : CollatzResearch.WordTrace tailWord_134677 prefixEnd_134677 61470252538377608282789 := by
  unfold tailWord_134677
  simp only [CollatzResearch.WordTrace]
  refine ⟨4912073733095704845506285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3274715822063803230337523 4912073733095704845506285)
  ·
    refine ⟨1842027649910889317064857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4912073733095704845506285 1842027649910889317064857)
    ·
      refine ⟨1381520737433166987798643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1842027649910889317064857 1381520737433166987798643)
      ·
        refine ⟨2072281106149750481697965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381520737433166987798643 2072281106149750481697965)
        ·
          refine ⟨777105414806156430636737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2072281106149750481697965 777105414806156430636737)
          ·
            refine ⟨582829061104617322977553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 777105414806156430636737 582829061104617322977553)
            ·
              refine ⟨437121795828462992233165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582829061104617322977553 437121795828462992233165)
              ·
                refine ⟨163920673435673622087437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 437121795828462992233165 163920673435673622087437)
                ·
                  refine ⟨61470252538377608282789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163920673435673622087437 61470252538377608282789)
                  ·
                    rfl

theorem cell20_134677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_134677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134677 prefixEnd_134677 := by exact prefixLift 134677
  have htrace : WordTrace (prefixWord ++ tailWord_134677) baseStart_134677 baseEnd_134677 := by
    simpa [prefixWord, tailWord_134677, baseEnd_134677] using wordTrace_append hprefix tailTrace_134677
  have hstable : (prefixWord ++ tailWord_134677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134677).length < 2 ^ (prefixWord ++ tailWord_134677).sum := by decide
  have hdescent : baseEnd_134677 < baseStart_134677 := by decide
  rcases family_descends (prefixWord ++ tailWord_134677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134684 : List Nat := [2, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_134684 : Nat := 118140960795 + 134684 * 2 ^ 59
def prefixEnd_134684 : Nat := 4983230072969 + 3 ^ 40 * 134684 * 2
def baseEnd_134684 : Nat := 61473447529116695049427

theorem tailTrace_134684 : CollatzResearch.WordTrace tailWord_134684 prefixEnd_134684 61473447529116695049427 := by
  unfold tailWord_134684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2456164522035172520505553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3274886029380230027340737 2456164522035172520505553)
  ·
    refine ⟨1842123391526379390379165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2456164522035172520505553 1842123391526379390379165)
    ·
      refine ⟨690796271822392271392187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1842123391526379390379165 690796271822392271392187)
      ·
        refine ⟨1036194407733588407088281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 690796271822392271392187 1036194407733588407088281)
        ·
          refine ⟨777145805800191305316211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1036194407733588407088281 777145805800191305316211)
          ·
            refine ⟨1165718708700286957974317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777145805800191305316211 1165718708700286957974317)
            ·
              refine ⟨437144515762607609240369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1165718708700286957974317 437144515762607609240369)
              ·
                refine ⟨327858386821955706930277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437144515762607609240369 327858386821955706930277)
                ·
                  refine ⟨61473447529116695049427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327858386821955706930277 61473447529116695049427)
                  ·
                    rfl

theorem cell20_134684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_134684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134684 prefixEnd_134684 := by exact prefixLift 134684
  have htrace : WordTrace (prefixWord ++ tailWord_134684) baseStart_134684 baseEnd_134684 := by
    simpa [prefixWord, tailWord_134684, baseEnd_134684] using wordTrace_append hprefix tailTrace_134684
  have hstable : (prefixWord ++ tailWord_134684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134684).length < 2 ^ (prefixWord ++ tailWord_134684).sum := by decide
  have hdescent : baseEnd_134684 < baseStart_134684 := by decide
  rcases family_descends (prefixWord ++ tailWord_134684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134705 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_134705 : Nat := 118140960795 + 134705 * 2 ^ 59
def prefixEnd_134705 : Nat := 4983230072969 + 3 ^ 40 * 134705 * 2
def baseEnd_134705 : Nat := 61483032501333955349341

theorem tailTrace_134705 : CollatzResearch.WordTrace tailWord_134705 prefixEnd_134705 61483032501333955349341 := by
  unfold tailWord_134705
  simp only [CollatzResearch.WordTrace]
  refine ⟨4913094976994265627525569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3275396651329510418350379 4913094976994265627525569)
  ·
    refine ⟨3684821232745699220644177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4913094976994265627525569 3684821232745699220644177)
    ·
      refine ⟨2763615924559274415483133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3684821232745699220644177 2763615924559274415483133)
      ·
        refine ⟨1036355971709727905806175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2763615924559274415483133 1036355971709727905806175)
        ·
          refine ⟨1554533957564591858709263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036355971709727905806175 1554533957564591858709263)
          ·
            refine ⟨2331800936346887788063895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1554533957564591858709263 2331800936346887788063895)
            ·
              refine ⟨3497701404520331682095843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331800936346887788063895 3497701404520331682095843)
              ·
                refine ⟨5246552106780497523143765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497701404520331682095843 5246552106780497523143765)
                ·
                  refine ⟨61483032501333955349341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5246552106780497523143765 61483032501333955349341)
                  ·
                    rfl

theorem cell20_134705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_134705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134705 prefixEnd_134705 := by exact prefixLift 134705
  have htrace : WordTrace (prefixWord ++ tailWord_134705) baseStart_134705 baseEnd_134705 := by
    simpa [prefixWord, tailWord_134705, baseEnd_134705] using wordTrace_append hprefix tailTrace_134705
  have hstable : (prefixWord ++ tailWord_134705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134705).length < 2 ^ (prefixWord ++ tailWord_134705).sum := by decide
  have hdescent : baseEnd_134705 < baseStart_134705 := by decide
  rcases family_descends (prefixWord ++ tailWord_134705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134732 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 3]
def baseStart_134732 : Nat := 118140960795 + 134732 * 2 ^ 59
def prefixEnd_134732 : Nat := 4983230072969 + 3 ^ 40 * 134732 * 2
def baseEnd_134732 : Nat := 61495356037041861449231

theorem tailTrace_134732 : CollatzResearch.WordTrace tailWord_134732 prefixEnd_134732 61495356037041861449231 := by
  unfold tailWord_134732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457039873948224619379225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3276053165264299492505633 2457039873948224619379225)
  ·
    refine ⟨1842779905461168464534419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2457039873948224619379225 1842779905461168464534419)
    ·
      refine ⟨2764169858191752696801629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1842779905461168464534419 2764169858191752696801629)
      ·
        refine ⟨1036563696821907261300611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2764169858191752696801629 1036563696821907261300611)
        ·
          refine ⟨1554845545232860891950917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036563696821907261300611 1554845545232860891950917)
          ·
            refine ⟨291533539731161417240797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1554845545232860891950917 291533539731161417240797)
            ·
              refine ⟨109325077399185531465299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291533539731161417240797 109325077399185531465299)
              ·
                refine ⟨163987616098778297197949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109325077399185531465299 163987616098778297197949)
                ·
                  refine ⟨61495356037041861449231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163987616098778297197949 61495356037041861449231)
                  ·
                    rfl

theorem cell20_134732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_134732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134732 prefixEnd_134732 := by exact prefixLift 134732
  have htrace : WordTrace (prefixWord ++ tailWord_134732) baseStart_134732 baseEnd_134732 := by
    simpa [prefixWord, tailWord_134732, baseEnd_134732] using wordTrace_append hprefix tailTrace_134732
  have hstable : (prefixWord ++ tailWord_134732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134732).length < 2 ^ (prefixWord ++ tailWord_134732).sum := by decide
  have hdescent : baseEnd_134732 < baseStart_134732 := by decide
  rcases family_descends (prefixWord ++ tailWord_134732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134742 : List Nat := [5, 2, 2, 2, 1, 1, 1, 6]
def baseStart_134742 : Nat := 118140960795 + 134742 * 2 ^ 59
def prefixEnd_134742 : Nat := 4983230072969 + 3 ^ 40 * 134742 * 2
def baseEnd_134742 : Nat := 20499973436508757038619

theorem tailTrace_134742 : CollatzResearch.WordTrace tailWord_134742 prefixEnd_134742 20499973436508757038619 := by
  unfold tailWord_134742
  simp only [CollatzResearch.WordTrace]
  refine ⟨307152779866263809163905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3276296318573480631081653 307152779866263809163905)
  ·
    refine ⟨230364584899697856872929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 307152779866263809163905 230364584899697856872929)
    ·
      refine ⟨172773438674773392654697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230364584899697856872929 172773438674773392654697)
      ·
        refine ⟨129580079006080044491023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172773438674773392654697 129580079006080044491023)
        ·
          refine ⟨194370118509120066736535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129580079006080044491023 194370118509120066736535)
          ·
            refine ⟨291555177763680100104803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194370118509120066736535 291555177763680100104803)
            ·
              refine ⟨437332766645520150157205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291555177763680100104803 437332766645520150157205)
              ·
                refine ⟨20499973436508757038619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 437332766645520150157205 20499973436508757038619)
                ·
                  rfl

theorem cell20_134742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_134742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134742 prefixEnd_134742 := by exact prefixLift 134742
  have htrace : WordTrace (prefixWord ++ tailWord_134742) baseStart_134742 baseEnd_134742 := by
    simpa [prefixWord, tailWord_134742, baseEnd_134742] using wordTrace_append hprefix tailTrace_134742
  have hstable : (prefixWord ++ tailWord_134742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134742).length < 2 ^ (prefixWord ++ tailWord_134742).sum := by decide
  have hdescent : baseEnd_134742 < baseStart_134742 := by decide
  rcases family_descends (prefixWord ++ tailWord_134742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134756 : List Nat := [2, 3, 1, 1, 2, 5, 1, 3, 2]
def baseStart_134756 : Nat := 118140960795 + 134756 * 2 ^ 59
def prefixEnd_134756 : Nat := 4983230072969 + 3 ^ 40 * 134756 * 2
def baseEnd_134756 : Nat := 61506310291004444649133

theorem tailTrace_134756 : CollatzResearch.WordTrace tailWord_134756 prefixEnd_134756 61506310291004444649133 := by
  unfold tailWord_134756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457477549904750668816061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3276636733206334225088081 2457477549904750668816061)
  ·
    refine ⟨921554081214281500806023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2457477549904750668816061 921554081214281500806023)
    ·
      refine ⟨1382331121821422251209035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 921554081214281500806023 1382331121821422251209035)
      ·
        refine ⟨2073496682732133376813553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1382331121821422251209035 2073496682732133376813553)
        ·
          refine ⟨1555122512049100032610165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2073496682732133376813553 1555122512049100032610165)
          ·
            refine ⟨145792735504603128057203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1555122512049100032610165 145792735504603128057203)
            ·
              refine ⟨218689103256904692085805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145792735504603128057203 218689103256904692085805)
              ·
                refine ⟨82008413721339259532177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218689103256904692085805 82008413721339259532177)
                ·
                  refine ⟨61506310291004444649133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82008413721339259532177 61506310291004444649133)
                  ·
                    rfl

theorem cell20_134756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_134756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134756 prefixEnd_134756 := by exact prefixLift 134756
  have htrace : WordTrace (prefixWord ++ tailWord_134756) baseStart_134756 baseEnd_134756 := by
    simpa [prefixWord, tailWord_134756, baseEnd_134756] using wordTrace_append hprefix tailTrace_134756
  have hstable : (prefixWord ++ tailWord_134756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134756).length < 2 ^ (prefixWord ++ tailWord_134756).sum := by decide
  have hdescent : baseEnd_134756 < baseStart_134756 := by decide
  rcases family_descends (prefixWord ++ tailWord_134756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134773 : List Nat := [1, 3, 4, 2, 1, 2, 3, 2, 2]
def baseStart_134773 : Nat := 118140960795 + 134773 * 2 ^ 59
def prefixEnd_134773 : Nat := 4983230072969 + 3 ^ 40 * 134773 * 2
def baseEnd_134773 : Nat := 61514069554227941082397

theorem tailTrace_134773 : CollatzResearch.WordTrace tailWord_134773 prefixEnd_134773 61514069554227941082397 := by
  unfold tailWord_134773
  simp only [CollatzResearch.WordTrace]
  refine ⟨4915575140747913241000973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3277050093831942160667315 4915575140747913241000973)
  ·
    refine ⟨1843340677780467465375365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4915575140747913241000973 1843340677780467465375365)
    ·
      refine ⟨345626377083837649757881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1843340677780467465375365 345626377083837649757881)
      ·
        refine ⟨259219782812878237318411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345626377083837649757881 259219782812878237318411)
        ·
          refine ⟨388829674219317355977617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259219782812878237318411 388829674219317355977617)
          ·
            refine ⟨291622255664488016983213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388829674219317355977617 291622255664488016983213)
            ·
              refine ⟨109358345874183006368705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 291622255664488016983213 109358345874183006368705)
              ·
                refine ⟨82018759405637254776529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109358345874183006368705 82018759405637254776529)
                ·
                  refine ⟨61514069554227941082397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82018759405637254776529 61514069554227941082397)
                  ·
                    rfl

theorem cell20_134773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_134773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134773 prefixEnd_134773 := by exact prefixLift 134773
  have htrace : WordTrace (prefixWord ++ tailWord_134773) baseStart_134773 baseEnd_134773 := by
    simpa [prefixWord, tailWord_134773, baseEnd_134773] using wordTrace_append hprefix tailTrace_134773
  have hstable : (prefixWord ++ tailWord_134773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134773).length < 2 ^ (prefixWord ++ tailWord_134773).sum := by decide
  have hdescent : baseEnd_134773 < baseStart_134773 := by decide
  rcases family_descends (prefixWord ++ tailWord_134773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134791 : List Nat := [1, 1, 4, 2, 1, 4, 1, 3, 3]
def baseStart_134791 : Nat := 118140960795 + 134791 * 2 ^ 59
def prefixEnd_134791 : Nat := 4983230072969 + 3 ^ 40 * 134791 * 2
def baseEnd_134791 : Nat := 61522285244699878482323

theorem tailTrace_134791 : CollatzResearch.WordTrace tailWord_134791 prefixEnd_134791 61522285244699878482323 := by
  unfold tailWord_134791
  simp only [CollatzResearch.WordTrace]
  refine ⟨4916231654682702315156227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3277487769788468210104151 4916231654682702315156227)
  ·
    refine ⟨7374347482024053472734341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4916231654682702315156227 7374347482024053472734341)
    ·
      refine ⟨1382690152879510026137689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7374347482024053472734341 1382690152879510026137689)
      ·
        refine ⟨1037017614659632519603267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1382690152879510026137689 1037017614659632519603267)
        ·
          refine ⟨1555526421989448779404901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037017614659632519603267 1555526421989448779404901)
          ·
            refine ⟨291661204123021646138419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1555526421989448779404901 291661204123021646138419)
            ·
              refine ⟨437491806184532469207629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291661204123021646138419 437491806184532469207629)
              ·
                refine ⟨164059427319199675952861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 437491806184532469207629 164059427319199675952861)
                ·
                  refine ⟨61522285244699878482323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164059427319199675952861 61522285244699878482323)
                  ·
                    rfl

theorem cell20_134791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_134791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134791 prefixEnd_134791 := by exact prefixLift 134791
  have htrace : WordTrace (prefixWord ++ tailWord_134791) baseStart_134791 baseEnd_134791 := by
    simpa [prefixWord, tailWord_134791, baseEnd_134791] using wordTrace_append hprefix tailTrace_134791
  have hstable : (prefixWord ++ tailWord_134791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134791).length < 2 ^ (prefixWord ++ tailWord_134791).sum := by decide
  have hdescent : baseEnd_134791 < baseStart_134791 := by decide
  rcases family_descends (prefixWord ++ tailWord_134791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134824 : List Nat := [2, 1, 7, 1, 2, 1, 2, 2, 2]
def baseStart_134824 : Nat := 118140960795 + 134824 * 2 ^ 59
def prefixEnd_134824 : Nat := 4983230072969 + 3 ^ 40 * 134824 * 2
def baseEnd_134824 : Nat := 61537347343898430382189

theorem tailTrace_134824 : CollatzResearch.WordTrace tailWord_134824 prefixEnd_134824 61537347343898430382189 := by
  unfold tailWord_134824
  simp only [CollatzResearch.WordTrace]
  refine ⟨2458717631781574475553763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3278290175708765967405017 2458717631781574475553763)
  ·
    refine ⟨3688076447672361713330645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2458717631781574475553763 3688076447672361713330645)
    ·
      refine ⟨86439291742320977656187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3688076447672361713330645 86439291742320977656187)
      ·
        refine ⟨129658937613481466484281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86439291742320977656187 129658937613481466484281)
        ·
          refine ⟨97244203210111099863211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129658937613481466484281 97244203210111099863211)
          ·
            refine ⟨145866304815166649794817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97244203210111099863211 145866304815166649794817)
            ·
              refine ⟨109399728611374987346113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145866304815166649794817 109399728611374987346113)
              ·
                refine ⟨82049796458531240509585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109399728611374987346113 82049796458531240509585)
                ·
                  refine ⟨61537347343898430382189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82049796458531240509585 61537347343898430382189)
                  ·
                    rfl

theorem cell20_134824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_134824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134824 prefixEnd_134824 := by exact prefixLift 134824
  have htrace : WordTrace (prefixWord ++ tailWord_134824) baseStart_134824 baseEnd_134824 := by
    simpa [prefixWord, tailWord_134824, baseEnd_134824] using wordTrace_append hprefix tailTrace_134824
  have hstable : (prefixWord ++ tailWord_134824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134824).length < 2 ^ (prefixWord ++ tailWord_134824).sum := by decide
  have hdescent : baseEnd_134824 < baseStart_134824 := by decide
  rcases family_descends (prefixWord ++ tailWord_134824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134881 : List Nat := [1, 2, 3, 1, 5, 1, 7]
def baseStart_134881 : Nat := 118140960795 + 134881 * 2 ^ 59
def prefixEnd_134881 : Nat := 4983230072969 + 3 ^ 40 * 134881 * 2
def baseEnd_134881 : Nat := 6840373744117729497995

theorem tailTrace_134881 : CollatzResearch.WordTrace tailWord_134881 prefixEnd_134881 6840373744117729497995 := by
  unfold tailWord_134881
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919514224356647685932497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3279676149571098457288331 4919514224356647685932497)
  ·
    refine ⟨3689635668267485764449373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4919514224356647685932497 3689635668267485764449373)
    ·
      refine ⟨1383613375600307161668515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3689635668267485764449373 1383613375600307161668515)
      ·
        refine ⟨2075420063400460742502773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383613375600307161668515 2075420063400460742502773)
        ·
          refine ⟨194570630943793194609635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2075420063400460742502773 194570630943793194609635)
          ·
            refine ⟨291855946415689791914453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194570630943793194609635 291855946415689791914453)
            ·
              refine ⟨6840373744117729497995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 291855946415689791914453 6840373744117729497995)
              ·
                rfl

theorem cell20_134881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 7].length) (baseStart_134881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134881 prefixEnd_134881 := by exact prefixLift 134881
  have htrace : WordTrace (prefixWord ++ tailWord_134881) baseStart_134881 baseEnd_134881 := by
    simpa [prefixWord, tailWord_134881, baseEnd_134881] using wordTrace_append hprefix tailTrace_134881
  have hstable : (prefixWord ++ tailWord_134881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134881).length < 2 ^ (prefixWord ++ tailWord_134881).sum := by decide
  have hdescent : baseEnd_134881 < baseStart_134881 := by decide
  rcases family_descends (prefixWord ++ tailWord_134881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134926 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_134926 : Nat := 118140960795 + 134926 * 2 ^ 59
def prefixEnd_134926 : Nat := 4983230072969 + 3 ^ 40 * 134926 * 2
def baseEnd_134926 : Nat := 61583902923239408981771

theorem tailTrace_134926 : CollatzResearch.WordTrace tailWord_134926 prefixEnd_134926 61583902923239408981771 := by
  unfold tailWord_134926
  simp only [CollatzResearch.WordTrace]
  refine ⟨615144438649202546415079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3280770339462413580880421 615144438649202546415079)
  ·
    refine ⟨922716657973803819622619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 615144438649202546415079 922716657973803819622619)
    ·
      refine ⟨1384074986960705729433929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922716657973803819622619 1384074986960705729433929)
      ·
        refine ⟨1038056240220529297075447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1384074986960705729433929 1038056240220529297075447)
        ·
          refine ⟨1557084360330793945613171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038056240220529297075447 1557084360330793945613171)
          ·
            refine ⟨2335626540496190918419757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557084360330793945613171 2335626540496190918419757)
            ·
              refine ⟨875859952686071594407409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2335626540496190918419757 875859952686071594407409)
              ·
                refine ⟨656894964514553695805557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875859952686071594407409 656894964514553695805557)
                ·
                  refine ⟨61583902923239408981771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 656894964514553695805557 61583902923239408981771)
                  ·
                    rfl

theorem cell20_134926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_134926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134926 prefixEnd_134926 := by exact prefixLift 134926
  have htrace : WordTrace (prefixWord ++ tailWord_134926) baseStart_134926 baseEnd_134926 := by
    simpa [prefixWord, tailWord_134926, baseEnd_134926] using wordTrace_append hprefix tailTrace_134926
  have hstable : (prefixWord ++ tailWord_134926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134926).length < 2 ^ (prefixWord ++ tailWord_134926).sum := by decide
  have hdescent : baseEnd_134926 < baseStart_134926 := by decide
  rcases family_descends (prefixWord ++ tailWord_134926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134932 : List Nat := [2, 4, 4, 1, 1, 2, 6]
def baseStart_134932 : Nat := 118140960795 + 134932 * 2 ^ 59
def prefixEnd_134932 : Nat := 4983230072969 + 3 ^ 40 * 134932 * 2
def baseEnd_134932 : Nat := 6842960165192228309083

theorem tailTrace_134932 : CollatzResearch.WordTrace tailWord_134932 prefixEnd_134932 6842960165192228309083 := by
  unfold tailWord_134932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460687173585941698019525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3280916231447922264026033 2460687173585941698019525)
  ·
    refine ⟨461378845047364068378661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2460687173585941698019525 461378845047364068378661)
    ·
      refine ⟨86508533446380762820999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 461378845047364068378661 86508533446380762820999)
      ·
        refine ⟨129762800169571144231499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86508533446380762820999 129762800169571144231499)
        ·
          refine ⟨194644200254356716347249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129762800169571144231499 194644200254356716347249)
          ·
            refine ⟨145983150190767537260437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194644200254356716347249 145983150190767537260437)
            ·
              refine ⟨6842960165192228309083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145983150190767537260437 6842960165192228309083)
              ·
                rfl

theorem cell20_134932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 6].length) (baseStart_134932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134932 prefixEnd_134932 := by exact prefixLift 134932
  have htrace : WordTrace (prefixWord ++ tailWord_134932) baseStart_134932 baseEnd_134932 := by
    simpa [prefixWord, tailWord_134932, baseEnd_134932] using wordTrace_append hprefix tailTrace_134932
  have hstable : (prefixWord ++ tailWord_134932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134932).length < 2 ^ (prefixWord ++ tailWord_134932).sum := by decide
  have hdescent : baseEnd_134932 < baseStart_134932 := by decide
  rcases family_descends (prefixWord ++ tailWord_134932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134942 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_134942 : Nat := 118140960795 + 134942 * 2 ^ 59
def prefixEnd_134942 : Nat := 4983230072969 + 3 ^ 40 * 134942 * 2
def baseEnd_134942 : Nat := 61591205759214464448373

theorem tailTrace_134942 : CollatzResearch.WordTrace tailWord_134942 prefixEnd_134942 61591205759214464448373 := by
  unfold tailWord_134942
  simp only [CollatzResearch.WordTrace]
  refine ⟨615217384641956887987885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3281159384757103402602053 615217384641956887987885)
  ·
    refine ⟨230706519240733832995457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 615217384641956887987885 230706519240733832995457)
    ·
      refine ⟨173029889430550374746593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230706519240733832995457 173029889430550374746593)
      ·
        refine ⟨129772417072912781059945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173029889430550374746593 129772417072912781059945)
        ·
          refine ⟨97329312804684585794959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129772417072912781059945 97329312804684585794959)
          ·
            refine ⟨145993969207026878692439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97329312804684585794959 145993969207026878692439)
            ·
              refine ⟨218990953810540318038659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145993969207026878692439 218990953810540318038659)
              ·
                refine ⟨328486430715810477057989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218990953810540318038659 328486430715810477057989)
                ·
                  refine ⟨61591205759214464448373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 328486430715810477057989 61591205759214464448373)
                  ·
                    rfl

theorem cell20_134942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_134942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134942 prefixEnd_134942 := by exact prefixLift 134942
  have htrace : WordTrace (prefixWord ++ tailWord_134942) baseStart_134942 baseEnd_134942 := by
    simpa [prefixWord, tailWord_134942, baseEnd_134942] using wordTrace_append hprefix tailTrace_134942
  have hstable : (prefixWord ++ tailWord_134942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134942).length < 2 ^ (prefixWord ++ tailWord_134942).sum := by decide
  have hdescent : baseEnd_134942 < baseStart_134942 := by decide
  rcases family_descends (prefixWord ++ tailWord_134942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134946 : List Nat := [3, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_134946 : Nat := 118140960795 + 134946 * 2 ^ 59
def prefixEnd_134946 : Nat := 4983230072969 + 3 ^ 40 * 134946 * 2
def baseEnd_134946 : Nat := 61593031468208228315023

theorem tailTrace_134946 : CollatzResearch.WordTrace tailWord_134946 prefixEnd_134946 61593031468208228315023 := by
  unfold tailWord_134946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1230471242280290946762173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3281256646080775858032461 1230471242280290946762173)
  ·
    refine ⟨461426715855109105035815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1230471242280290946762173 461426715855109105035815)
    ·
      refine ⟨692140073782663657553723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461426715855109105035815 692140073782663657553723)
      ·
        refine ⟨1038210110673995486330585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692140073782663657553723 1038210110673995486330585)
        ·
          refine ⟨778657583005496614747939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1038210110673995486330585 778657583005496614747939)
          ·
            refine ⟨1167986374508244922121909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778657583005496614747939 1167986374508244922121909)
            ·
              refine ⟨109498722610147961448929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1167986374508244922121909 109498722610147961448929)
              ·
                refine ⟨82124041957610971086697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109498722610147961448929 82124041957610971086697)
                ·
                  refine ⟨61593031468208228315023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82124041957610971086697 61593031468208228315023)
                  ·
                    rfl

theorem cell20_134946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_134946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_134946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_134946 prefixEnd_134946 := by exact prefixLift 134946
  have htrace : WordTrace (prefixWord ++ tailWord_134946) baseStart_134946 baseEnd_134946 := by
    simpa [prefixWord, tailWord_134946, baseEnd_134946] using wordTrace_append hprefix tailTrace_134946
  have hstable : (prefixWord ++ tailWord_134946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134946).length < 2 ^ (prefixWord ++ tailWord_134946).sum := by decide
  have hdescent : baseEnd_134946 < baseStart_134946 := by decide
  rcases family_descends (prefixWord ++ tailWord_134946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135009 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_135009 : Nat := 118140960795 + 135009 * 2 ^ 59
def prefixEnd_135009 : Nat := 4983230072969 + 3 ^ 40 * 135009 * 2
def baseEnd_135009 : Nat := 61621786384860009214765

theorem tailTrace_135009 : CollatzResearch.WordTrace tailWord_135009 prefixEnd_135009 61621786384860009214765 := by
  unfold tailWord_135009
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924182767892925546592081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3282788511928617031061387 4924182767892925546592081)
  ·
    refine ⟨3693137075919694159944061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4924182767892925546592081 3693137075919694159944061)
    ·
      refine ⟨1384926403469885309979023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3693137075919694159944061 1384926403469885309979023)
      ·
        refine ⟨2077389605204827964968535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384926403469885309979023 2077389605204827964968535)
        ·
          refine ⟨3116084407807241947452803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077389605204827964968535 3116084407807241947452803)
          ·
            refine ⟨4674126611710862921179205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3116084407807241947452803 4674126611710862921179205)
            ·
              refine ⟨876398739695786797721101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4674126611710862921179205 876398739695786797721101)
              ·
                refine ⟨328649527385920049145413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 876398739695786797721101 328649527385920049145413)
                ·
                  refine ⟨61621786384860009214765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 328649527385920049145413 61621786384860009214765)
                  ·
                    rfl

theorem cell20_135009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_135009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135009 prefixEnd_135009 := by exact prefixLift 135009
  have htrace : WordTrace (prefixWord ++ tailWord_135009) baseStart_135009 baseEnd_135009 := by
    simpa [prefixWord, tailWord_135009, baseEnd_135009] using wordTrace_append hprefix tailTrace_135009
  have hstable : (prefixWord ++ tailWord_135009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135009).length < 2 ^ (prefixWord ++ tailWord_135009).sum := by decide
  have hdescent : baseEnd_135009 < baseStart_135009 := by decide
  rcases family_descends (prefixWord ++ tailWord_135009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135012 : List Nat := [2, 3, 1, 1, 5, 2, 1, 5]
def baseStart_135012 : Nat := 118140960795 + 135012 * 2 ^ 59
def prefixEnd_135012 : Nat := 4983230072969 + 3 ^ 40 * 135012 * 2
def baseEnd_135012 : Nat := 20541051888868444038251

theorem tailTrace_135012 : CollatzResearch.WordTrace tailWord_135012 prefixEnd_135012 20541051888868444038251 := by
  unfold tailWord_135012
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462146093441028529475645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3282861457921371372634193 2462146093441028529475645)
  ·
    refine ⟨923304785040385698553367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2462146093441028529475645 923304785040385698553367)
    ·
      refine ⟨1384957177560578547830051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923304785040385698553367 1384957177560578547830051)
      ·
        refine ⟨2077435766340867821745077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384957177560578547830051 2077435766340867821745077)
        ·
          refine ⟨194759603094456358288601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2077435766340867821745077 194759603094456358288601)
          ·
            refine ⟨146069702320842268716451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194759603094456358288601 146069702320842268716451)
            ·
              refine ⟨219104553481263403074677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146069702320842268716451 219104553481263403074677)
              ·
                refine ⟨20541051888868444038251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 219104553481263403074677 20541051888868444038251)
                ·
                  rfl

theorem cell20_135012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_135012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135012 prefixEnd_135012 := by exact prefixLift 135012
  have htrace : WordTrace (prefixWord ++ tailWord_135012) baseStart_135012 baseEnd_135012 := by
    simpa [prefixWord, tailWord_135012, baseEnd_135012] using wordTrace_append hprefix tailTrace_135012
  have hstable : (prefixWord ++ tailWord_135012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135012).length < 2 ^ (prefixWord ++ tailWord_135012).sum := by decide
  have hdescent : baseEnd_135012 < baseStart_135012 := by decide
  rcases family_descends (prefixWord ++ tailWord_135012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135023 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_135023 : Nat := 118140960795 + 135023 * 2 ^ 59
def prefixEnd_135023 : Nat := 4983230072969 + 3 ^ 40 * 135023 * 2
def baseEnd_135023 : Nat := 61628176366338182748041

theorem tailTrace_135023 : CollatzResearch.WordTrace tailWord_135023 prefixEnd_135023 61628176366338182748041 := by
  unfold tailWord_135023
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924693389842205937601723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3283128926561470625067815 4924693389842205937601723)
  ·
    refine ⟨7387040084763308906402585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4924693389842205937601723 7387040084763308906402585)
    ·
      refine ⟨5540280063572481679801939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7387040084763308906402585 5540280063572481679801939)
      ·
        refine ⟨8310420095358722519702909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5540280063572481679801939 8310420095358722519702909)
        ·
          refine ⟨3116407535759520944888591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8310420095358722519702909 3116407535759520944888591)
          ·
            refine ⟨4674611303639281417332887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3116407535759520944888591 4674611303639281417332887)
            ·
              refine ⟨7011916955458922125999331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4674611303639281417332887 7011916955458922125999331)
              ·
                refine ⟨10517875433188383188998997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7011916955458922125999331 10517875433188383188998997)
                ·
                  refine ⟨61628176366338182748041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10517875433188383188998997 61628176366338182748041)
                  ·
                    rfl

theorem cell20_135023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_135023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135023 prefixEnd_135023 := by exact prefixLift 135023
  have htrace : WordTrace (prefixWord ++ tailWord_135023) baseStart_135023 baseEnd_135023 := by
    simpa [prefixWord, tailWord_135023, baseEnd_135023] using wordTrace_append hprefix tailTrace_135023
  have hstable : (prefixWord ++ tailWord_135023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135023).length < 2 ^ (prefixWord ++ tailWord_135023).sum := by decide
  have hdescent : baseEnd_135023 < baseStart_135023 := by decide
  rcases family_descends (prefixWord ++ tailWord_135023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135033 : List Nat := [1, 2, 1, 3, 2, 2, 5, 4]
def baseStart_135033 : Nat := 118140960795 + 135033 * 2 ^ 59
def prefixEnd_135033 : Nat := 4983230072969 + 3 ^ 40 * 135033 * 2
def baseEnd_135033 : Nat := 20544246879607530804889

theorem tailTrace_135033 : CollatzResearch.WordTrace tailWord_135033 prefixEnd_135033 20544246879607530804889 := by
  unfold tailWord_135033
  simp only [CollatzResearch.WordTrace]
  refine ⟨4925058119805977645465753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3283372079870651763643835 4925058119805977645465753)
  ·
    refine ⟨3693793589854483234099315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4925058119805977645465753 3693793589854483234099315)
    ·
      refine ⟨5540690384781724851148973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3693793589854483234099315 5540690384781724851148973)
      ·
        refine ⟨2077758894293146819180865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5540690384781724851148973 2077758894293146819180865)
        ·
          refine ⟨1558319170719860114385649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2077758894293146819180865 1558319170719860114385649)
          ·
            refine ⟨1168739378039895085789237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558319170719860114385649 1168739378039895085789237)
            ·
              refine ⟨109569316691240164292741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1168739378039895085789237 109569316691240164292741)
              ·
                refine ⟨20544246879607530804889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109569316691240164292741 20544246879607530804889)
                ·
                  rfl

theorem cell20_135033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 4].length) (baseStart_135033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135033 prefixEnd_135033 := by exact prefixLift 135033
  have htrace : WordTrace (prefixWord ++ tailWord_135033) baseStart_135033 baseEnd_135033 := by
    simpa [prefixWord, tailWord_135033, baseEnd_135033] using wordTrace_append hprefix tailTrace_135033
  have hstable : (prefixWord ++ tailWord_135033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135033).length < 2 ^ (prefixWord ++ tailWord_135033).sum := by decide
  have hdescent : baseEnd_135033 < baseStart_135033 := by decide
  rcases family_descends (prefixWord ++ tailWord_135033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135043 : List Nat := [1, 1, 1, 3, 4, 3, 2, 3, 2]
def baseStart_135043 : Nat := 118140960795 + 135043 * 2 ^ 59
def prefixEnd_135043 : Nat := 4983230072969 + 3 ^ 40 * 135043 * 2
def baseEnd_135043 : Nat := 61637304911307002081293

theorem tailTrace_135043 : CollatzResearch.WordTrace tailWord_135043 prefixEnd_135043 61637304911307002081293 := by
  unfold tailWord_135043
  simp only [CollatzResearch.WordTrace]
  refine ⟨4925422849769749353329783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3283615233179832902219855 4925422849769749353329783)
  ·
    refine ⟨7388134274654624029994675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4925422849769749353329783 7388134274654624029994675)
    ·
      refine ⟨11082201411981936044992013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7388134274654624029994675 11082201411981936044992013)
      ·
        refine ⟨4155825529493226016872005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11082201411981936044992013 4155825529493226016872005)
        ·
          refine ⟨779217286779979878163501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4155825529493226016872005 779217286779979878163501)
          ·
            refine ⟨292206482542492454311313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 779217286779979878163501 292206482542492454311313)
            ·
              refine ⟨219154861906869340733485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292206482542492454311313 219154861906869340733485)
              ·
                refine ⟨82183073215076002775057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219154861906869340733485 82183073215076002775057)
                ·
                  refine ⟨61637304911307002081293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82183073215076002775057 61637304911307002081293)
                  ·
                    rfl

theorem cell20_135043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 2].length) (baseStart_135043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135043 prefixEnd_135043 := by exact prefixLift 135043
  have htrace : WordTrace (prefixWord ++ tailWord_135043) baseStart_135043 baseEnd_135043 := by
    simpa [prefixWord, tailWord_135043, baseEnd_135043] using wordTrace_append hprefix tailTrace_135043
  have hstable : (prefixWord ++ tailWord_135043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135043).length < 2 ^ (prefixWord ++ tailWord_135043).sum := by decide
  have hdescent : baseEnd_135043 < baseStart_135043 := by decide
  rcases family_descends (prefixWord ++ tailWord_135043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135070 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_135070 : Nat := 118140960795 + 135070 * 2 ^ 59
def prefixEnd_135070 : Nat := 4983230072969 + 3 ^ 40 * 135070 * 2
def baseEnd_135070 : Nat := 61649628447014908181183

theorem tailTrace_135070 : CollatzResearch.WordTrace tailWord_135070 prefixEnd_135070 61649628447014908181183 := by
  unfold tailWord_135070
  simp only [CollatzResearch.WordTrace]
  refine ⟨615800952583991620570333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3284271747114621976375109 615800952583991620570333)
  ·
    refine ⟨230925357218996857713875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 615800952583991620570333 230925357218996857713875)
    ·
      refine ⟨346388035828495286570813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230925357218996857713875 346388035828495286570813)
      ·
        refine ⟨129895513435685732464055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 346388035828495286570813 129895513435685732464055)
        ·
          refine ⟨194843270153528598696083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129895513435685732464055 194843270153528598696083)
          ·
            refine ⟨292264905230292898044125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194843270153528598696083 292264905230292898044125)
            ·
              refine ⟨109599339461359836766547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 292264905230292898044125 109599339461359836766547)
              ·
                refine ⟨164399009192039755149821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109599339461359836766547 164399009192039755149821)
                ·
                  refine ⟨61649628447014908181183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164399009192039755149821 61649628447014908181183)
                  ·
                    rfl

theorem cell20_135070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_135070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135070 prefixEnd_135070 := by exact prefixLift 135070
  have htrace : WordTrace (prefixWord ++ tailWord_135070) baseStart_135070 baseEnd_135070 := by
    simpa [prefixWord, tailWord_135070, baseEnd_135070] using wordTrace_append hprefix tailTrace_135070
  have hstable : (prefixWord ++ tailWord_135070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135070).length < 2 ^ (prefixWord ++ tailWord_135070).sum := by decide
  have hdescent : baseEnd_135070 < baseStart_135070 := by decide
  rcases family_descends (prefixWord ++ tailWord_135070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135099 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_135099 : Nat := 118140960795 + 135099 * 2 ^ 59
def prefixEnd_135099 : Nat := 4983230072969 + 3 ^ 40 * 135099 * 2
def baseEnd_135099 : Nat := 61662864837219696214397

theorem tailTrace_135099 : CollatzResearch.WordTrace tailWord_135099 prefixEnd_135099 61662864837219696214397 := by
  unfold tailWord_135099
  simp only [CollatzResearch.WordTrace]
  refine ⟨4927465337566870917368351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3284976891711247278245567 4927465337566870917368351)
  ·
    refine ⟨7391198006350306376052527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4927465337566870917368351 7391198006350306376052527)
    ·
      refine ⟨11086797009525459564078791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7391198006350306376052527 11086797009525459564078791)
      ·
        refine ⟨16630195514288189346118187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11086797009525459564078791 16630195514288189346118187)
        ·
          refine ⟨24945293271432284019177281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16630195514288189346118187 24945293271432284019177281)
          ·
            refine ⟨18708969953574213014382961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24945293271432284019177281 18708969953574213014382961)
            ·
              refine ⟨14031727465180659760787221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18708969953574213014382961 14031727465180659760787221)
              ·
                refine ⟨657737224930343426286901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14031727465180659760787221 657737224930343426286901)
                ·
                  refine ⟨61662864837219696214397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 657737224930343426286901 61662864837219696214397)
                  ·
                    rfl

theorem cell20_135099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_135099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135099 prefixEnd_135099 := by exact prefixLift 135099
  have htrace : WordTrace (prefixWord ++ tailWord_135099) baseStart_135099 baseEnd_135099 := by
    simpa [prefixWord, tailWord_135099, baseEnd_135099] using wordTrace_append hprefix tailTrace_135099
  have hstable : (prefixWord ++ tailWord_135099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135099).length < 2 ^ (prefixWord ++ tailWord_135099).sum := by decide
  have hdescent : baseEnd_135099 < baseStart_135099 := by decide
  rcases family_descends (prefixWord ++ tailWord_135099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135116 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_135116 : Nat := 118140960795 + 135116 * 2 ^ 59
def prefixEnd_135116 : Nat := 4983230072969 + 3 ^ 40 * 135116 * 2
def baseEnd_135116 : Nat := 61670624100443192647661

theorem tailTrace_135116 : CollatzResearch.WordTrace tailWord_135116 prefixEnd_135116 61670624100443192647661 := by
  unfold tailWord_135116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2464042689252641410368601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3285390252336855213824801 2464042689252641410368601)
  ·
    refine ⟨1848032016939481057776451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2464042689252641410368601 1848032016939481057776451)
    ·
      refine ⟨2772048025409221586664677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848032016939481057776451 2772048025409221586664677)
      ·
        refine ⟨519759004764229047499627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2772048025409221586664677 519759004764229047499627)
        ·
          refine ⟨779638507146343571249441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519759004764229047499627 779638507146343571249441)
          ·
            refine ⟨584728880359757678437081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779638507146343571249441 584728880359757678437081)
            ·
              refine ⟨438546660269818258827811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584728880359757678437081 438546660269818258827811)
              ·
                refine ⟨657819990404727388241717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438546660269818258827811 657819990404727388241717)
                ·
                  refine ⟨61670624100443192647661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 657819990404727388241717 61670624100443192647661)
                  ·
                    rfl

theorem cell20_135116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_135116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135116 prefixEnd_135116 := by exact prefixLift 135116
  have htrace : WordTrace (prefixWord ++ tailWord_135116) baseStart_135116 baseEnd_135116 := by
    simpa [prefixWord, tailWord_135116, baseEnd_135116] using wordTrace_append hprefix tailTrace_135116
  have hstable : (prefixWord ++ tailWord_135116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135116).length < 2 ^ (prefixWord ++ tailWord_135116).sum := by decide
  have hdescent : baseEnd_135116 < baseStart_135116 := by decide
  rcases family_descends (prefixWord ++ tailWord_135116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135119 : List Nat := [1, 1, 2, 1, 1, 5, 5, 2, 2]
def baseStart_135119 : Nat := 118140960795 + 135119 * 2 ^ 59
def prefixEnd_135119 : Nat := 4983230072969 + 3 ^ 40 * 135119 * 2
def baseEnd_135119 : Nat := 61671993382188515547649

theorem tailTrace_135119 : CollatzResearch.WordTrace tailWord_135119 prefixEnd_135119 61671993382188515547649 := by
  unfold tailWord_135119
  simp only [CollatzResearch.WordTrace]
  refine ⟨4928194797494414333096411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3285463198329609555397607 4928194797494414333096411)
  ·
    refine ⟨7392292196241621499644617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4928194797494414333096411 7392292196241621499644617)
    ·
      refine ⟨5544219147181216124733463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7392292196241621499644617 5544219147181216124733463)
      ·
        refine ⟨8316328720771824187100195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5544219147181216124733463 8316328720771824187100195)
        ·
          refine ⟨12474493081157736280650293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8316328720771824187100195 12474493081157736280650293)
          ·
            refine ⟨1169483726358537776310965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12474493081157736280650293 1169483726358537776310965)
            ·
              refine ⟨109639099346112916529153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1169483726358537776310965 109639099346112916529153)
              ·
                refine ⟨82229324509584687396865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109639099346112916529153 82229324509584687396865)
                ·
                  refine ⟨61671993382188515547649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82229324509584687396865 61671993382188515547649)
                  ·
                    rfl

theorem cell20_135119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 2].length) (baseStart_135119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135119 prefixEnd_135119 := by exact prefixLift 135119
  have htrace : WordTrace (prefixWord ++ tailWord_135119) baseStart_135119 baseEnd_135119 := by
    simpa [prefixWord, tailWord_135119, baseEnd_135119] using wordTrace_append hprefix tailTrace_135119
  have hstable : (prefixWord ++ tailWord_135119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135119).length < 2 ^ (prefixWord ++ tailWord_135119).sum := by decide
  have hdescent : baseEnd_135119 < baseStart_135119 := by decide
  rcases family_descends (prefixWord ++ tailWord_135119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135129 : List Nat := [1, 2, 1, 2, 7, 1, 2, 1, 3]
def baseStart_135129 : Nat := 118140960795 + 135129 * 2 ^ 59
def prefixEnd_135129 : Nat := 4983230072969 + 3 ^ 40 * 135129 * 2
def baseEnd_135129 : Nat := 61676557654672925214275

theorem tailTrace_135129 : CollatzResearch.WordTrace tailWord_135129 prefixEnd_135129 61676557654672925214275 := by
  unfold tailWord_135129
  simp only [CollatzResearch.WordTrace]
  refine ⟨4928559527458186040960441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3285706351638790693973627 4928559527458186040960441)
  ·
    refine ⟨3696419645593639530720331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4928559527458186040960441 3696419645593639530720331)
    ·
      refine ⟨5544629468390459296080497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3696419645593639530720331 5544629468390459296080497)
      ·
        refine ⟨4158472101292844472060373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5544629468390459296080497 4158472101292844472060373)
        ·
          refine ⟨97464189874051042313915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4158472101292844472060373 97464189874051042313915)
          ·
            refine ⟨146196284811076563470873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97464189874051042313915 146196284811076563470873)
            ·
              refine ⟨109647213608307422603155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146196284811076563470873 109647213608307422603155)
              ·
                refine ⟨164470820412461133904733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109647213608307422603155 164470820412461133904733)
                ·
                  refine ⟨61676557654672925214275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164470820412461133904733 61676557654672925214275)
                  ·
                    rfl

theorem cell20_135129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_135129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135129 prefixEnd_135129 := by exact prefixLift 135129
  have htrace : WordTrace (prefixWord ++ tailWord_135129) baseStart_135129 baseEnd_135129 := by
    simpa [prefixWord, tailWord_135129, baseEnd_135129] using wordTrace_append hprefix tailTrace_135129
  have hstable : (prefixWord ++ tailWord_135129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135129).length < 2 ^ (prefixWord ++ tailWord_135129).sum := by decide
  have hdescent : baseEnd_135129 < baseStart_135129 := by decide
  rcases family_descends (prefixWord ++ tailWord_135129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135192 : List Nat := [2, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_135192 : Nat := 118140960795 + 135192 * 2 ^ 59
def prefixEnd_135192 : Nat := 4983230072969 + 3 ^ 40 * 135192 * 2
def baseEnd_135192 : Nat := 61705312571324706114017

theorem tailTrace_135192 : CollatzResearch.WordTrace tailWord_135192 prefixEnd_135192 61705312571324706114017 := by
  unfold tailWord_135192
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465428663114973900251915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3287238217486631867002553 2465428663114973900251915)
  ·
    refine ⟨3698142994672460850377873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2465428663114973900251915 3698142994672460850377873)
    ·
      refine ⟨2773607246004345637783405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3698142994672460850377873 2773607246004345637783405)
      ·
        refine ⟨1040102717251629614168777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2773607246004345637783405 1040102717251629614168777)
        ·
          refine ⟨780077037938722210626583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1040102717251629614168777 780077037938722210626583)
          ·
            refine ⟨1170115556908083315939875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780077037938722210626583 1170115556908083315939875)
            ·
              refine ⟨1755173335362124973909813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170115556908083315939875 1755173335362124973909813)
              ·
                refine ⟨164547500190199216304045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1755173335362124973909813 164547500190199216304045)
                ·
                  refine ⟨61705312571324706114017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164547500190199216304045 61705312571324706114017)
                  ·
                    rfl

theorem cell20_135192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_135192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135192 prefixEnd_135192 := by exact prefixLift 135192
  have htrace : WordTrace (prefixWord ++ tailWord_135192) baseStart_135192 baseEnd_135192 := by
    simpa [prefixWord, tailWord_135192, baseEnd_135192] using wordTrace_append hprefix tailTrace_135192
  have hstable : (prefixWord ++ tailWord_135192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135192).length < 2 ^ (prefixWord ++ tailWord_135192).sum := by decide
  have hdescent : baseEnd_135192 < baseStart_135192 := by decide
  rcases family_descends (prefixWord ++ tailWord_135192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135199 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_135199 : Nat := 118140960795 + 135199 * 2 ^ 59
def prefixEnd_135199 : Nat := 4983230072969 + 3 ^ 40 * 135199 * 2
def baseEnd_135199 : Nat := 61708507562063792880655

theorem tailTrace_135199 : CollatzResearch.WordTrace tailWord_135199 prefixEnd_135199 61708507562063792880655 := by
  unfold tailWord_135199
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931112637204587996008651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3287408424803058664005767 4931112637204587996008651)
  ·
    refine ⟨7396668955806881994012977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4931112637204587996008651 7396668955806881994012977)
    ·
      refine ⟨5547501716855161495509733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7396668955806881994012977 5547501716855161495509733)
      ·
        refine ⟨1040156571910342780408075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5547501716855161495509733 1040156571910342780408075)
        ·
          refine ⟨1560234857865514170612113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040156571910342780408075 1560234857865514170612113)
          ·
            refine ⟨1170176143399135627959085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1560234857865514170612113 1170176143399135627959085)
            ·
              refine ⟨438816053774675860484657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1170176143399135627959085 438816053774675860484657)
              ·
                refine ⟨329112040331006895363493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438816053774675860484657 329112040331006895363493)
                ·
                  refine ⟨61708507562063792880655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329112040331006895363493 61708507562063792880655)
                  ·
                    rfl

theorem cell20_135199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_135199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135199 prefixEnd_135199 := by exact prefixLift 135199
  have htrace : WordTrace (prefixWord ++ tailWord_135199) baseStart_135199 baseEnd_135199 := by
    simpa [prefixWord, tailWord_135199, baseEnd_135199] using wordTrace_append hprefix tailTrace_135199
  have hstable : (prefixWord ++ tailWord_135199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135199).length < 2 ^ (prefixWord ++ tailWord_135199).sum := by decide
  have hdescent : baseEnd_135199 < baseStart_135199 := by decide
  rcases family_descends (prefixWord ++ tailWord_135199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135216 : List Nat := [2, 1, 1, 1, 2, 5, 1, 5, 2]
def baseStart_135216 : Nat := 118140960795 + 135216 * 2 ^ 59
def prefixEnd_135216 : Nat := 4983230072969 + 3 ^ 40 * 135216 * 2
def baseEnd_135216 : Nat := 61716266825287289313919

theorem tailTrace_135216 : CollatzResearch.WordTrace tailWord_135216 prefixEnd_135216 61716266825287289313919 := by
  unfold tailWord_135216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465866339071499949688751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3287821785428666599585001 2465866339071499949688751)
  ·
    refine ⟨3698799508607249924533127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2465866339071499949688751 3698799508607249924533127)
    ·
      refine ⟨5548199262910874886799691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3698799508607249924533127 5548199262910874886799691)
      ·
        refine ⟨8322298894366312330199537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5548199262910874886799691 8322298894366312330199537)
        ·
          refine ⟨6241724170774734247649653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8322298894366312330199537 6241724170774734247649653)
          ·
            refine ⟨585161641010131335717155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6241724170774734247649653 585161641010131335717155)
            ·
              refine ⟨877742461515197003575733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585161641010131335717155 877742461515197003575733)
              ·
                refine ⟨82288355767049719085225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 877742461515197003575733 82288355767049719085225)
                ·
                  refine ⟨61716266825287289313919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82288355767049719085225 61716266825287289313919)
                  ·
                    rfl

theorem cell20_135216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_135216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135216 prefixEnd_135216 := by exact prefixLift 135216
  have htrace : WordTrace (prefixWord ++ tailWord_135216) baseStart_135216 baseEnd_135216 := by
    simpa [prefixWord, tailWord_135216, baseEnd_135216] using wordTrace_append hprefix tailTrace_135216
  have hstable : (prefixWord ++ tailWord_135216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135216).length < 2 ^ (prefixWord ++ tailWord_135216).sum := by decide
  have hdescent : baseEnd_135216 < baseStart_135216 := by decide
  rcases family_descends (prefixWord ++ tailWord_135216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135233 : List Nat := [1, 2, 5, 1, 2, 1, 2, 4, 2]
def baseStart_135233 : Nat := 118140960795 + 135233 * 2 ^ 59
def prefixEnd_135233 : Nat := 4983230072969 + 3 ^ 40 * 135233 * 2
def baseEnd_135233 : Nat := 61724026088510785747183

theorem tailTrace_135233 : CollatzResearch.WordTrace tailWord_135233 prefixEnd_135233 61724026088510785747183 := by
  unfold tailWord_135233
  simp only [CollatzResearch.WordTrace]
  refine ⟨4932352719081411802746353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3288235146054274535164235 4932352719081411802746353)
  ·
    refine ⟨3699264539311058852059765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4932352719081411802746353 3699264539311058852059765)
    ·
      refine ⟨346806050560411767380603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3699264539311058852059765 346806050560411767380603)
      ·
        refine ⟨520209075840617651070905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346806050560411767380603 520209075840617651070905)
        ·
          refine ⟨390156806880463238303179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520209075840617651070905 390156806880463238303179)
          ·
            refine ⟨585235210320694857454769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390156806880463238303179 585235210320694857454769)
            ·
              refine ⟨438926407740521143091077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585235210320694857454769 438926407740521143091077)
              ·
                refine ⟨82298701451347714329577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438926407740521143091077 82298701451347714329577)
                ·
                  refine ⟨61724026088510785747183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82298701451347714329577 61724026088510785747183)
                  ·
                    rfl

theorem cell20_135233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_135233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135233 prefixEnd_135233 := by exact prefixLift 135233
  have htrace : WordTrace (prefixWord ++ tailWord_135233) baseStart_135233 baseEnd_135233 := by
    simpa [prefixWord, tailWord_135233, baseEnd_135233] using wordTrace_append hprefix tailTrace_135233
  have hstable : (prefixWord ++ tailWord_135233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135233).length < 2 ^ (prefixWord ++ tailWord_135233).sum := by decide
  have hdescent : baseEnd_135233 < baseStart_135233 := by decide
  rcases family_descends (prefixWord ++ tailWord_135233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135282 : List Nat := [3, 2, 1, 2, 2, 2, 8]
def baseStart_135282 : Nat := 118140960795 + 135282 * 2 ^ 59
def prefixEnd_135282 : Nat := 4983230072969 + 3 ^ 40 * 135282 * 2
def baseEnd_135282 : Nat := 6860710113742710345961

theorem tailTrace_135282 : CollatzResearch.WordTrace tailWord_135282 prefixEnd_135282 6860710113742710345961 := by
  unfold tailWord_135282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1233534973975973292820025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3289426597269262114186733 1233534973975973292820025)
  ·
    refine ⟨925151230481979969615019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1233534973975973292820025 925151230481979969615019)
    ·
      refine ⟨1387726845722969954422529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 925151230481979969615019 1387726845722969954422529)
      ·
        refine ⟨1040795134292227465816897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1387726845722969954422529 1040795134292227465816897)
        ·
          refine ⟨780596350719170599362673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1040795134292227465816897 780596350719170599362673)
          ·
            refine ⟨585447263039377949522005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 780596350719170599362673 585447263039377949522005)
            ·
              refine ⟨6860710113742710345961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 585447263039377949522005 6860710113742710345961)
              ·
                rfl

theorem cell20_135282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 8].length) (baseStart_135282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135282 prefixEnd_135282 := by exact prefixLift 135282
  have htrace : WordTrace (prefixWord ++ tailWord_135282) baseStart_135282 baseEnd_135282 := by
    simpa [prefixWord, tailWord_135282, baseEnd_135282] using wordTrace_append hprefix tailTrace_135282
  have hstable : (prefixWord ++ tailWord_135282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135282).length < 2 ^ (prefixWord ++ tailWord_135282).sum := by decide
  have hdescent : baseEnd_135282 < baseStart_135282 := by decide
  rcases family_descends (prefixWord ++ tailWord_135282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135292 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 4]
def baseStart_135292 : Nat := 118140960795 + 135292 * 2 ^ 59
def prefixEnd_135292 : Nat := 4983230072969 + 3 ^ 40 * 135292 * 2
def baseEnd_135292 : Nat := 61750955296168802780275

theorem tailTrace_135292 : CollatzResearch.WordTrace tailWord_135292 prefixEnd_135292 61750955296168802780275 := by
  unfold tailWord_135292
  simp only [CollatzResearch.WordTrace]
  refine ⟨2467252312933832439572065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3289669750578443252762753 2467252312933832439572065)
  ·
    refine ⟨1850439234700374329679049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2467252312933832439572065 1850439234700374329679049)
    ·
      refine ⟨1387829426025280747259287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1850439234700374329679049 1387829426025280747259287)
      ·
        refine ⟨2081744139037921120888931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1387829426025280747259287 2081744139037921120888931)
        ·
          refine ⟨3122616208556881681333397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081744139037921120888931 3122616208556881681333397)
          ·
            refine ⟨146372634776103828812503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3122616208556881681333397 146372634776103828812503)
            ·
              refine ⟨219558952164155743218755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146372634776103828812503 219558952164155743218755)
              ·
                refine ⟨329338428246233614828133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219558952164155743218755 329338428246233614828133)
                ·
                  refine ⟨61750955296168802780275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329338428246233614828133 61750955296168802780275)
                  ·
                    rfl

theorem cell20_135292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_135292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135292 prefixEnd_135292 := by exact prefixLift 135292
  have htrace : WordTrace (prefixWord ++ tailWord_135292) baseStart_135292 baseEnd_135292 := by
    simpa [prefixWord, tailWord_135292, baseEnd_135292] using wordTrace_append hprefix tailTrace_135292
  have hstable : (prefixWord ++ tailWord_135292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135292).length < 2 ^ (prefixWord ++ tailWord_135292).sum := by decide
  have hdescent : baseEnd_135292 < baseStart_135292 := by decide
  rcases family_descends (prefixWord ++ tailWord_135292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135395 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 3]
def baseStart_135395 : Nat := 118140960795 + 135395 * 2 ^ 59
def prefixEnd_135395 : Nat := 4983230072969 + 3 ^ 40 * 135395 * 2
def baseEnd_135395 : Nat := 61797967302758222346521

theorem tailTrace_135395 : CollatzResearch.WordTrace tailWord_135395 prefixEnd_135395 61797967302758222346521 := by
  unfold tailWord_135395
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938261344494513470143639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3292174229663008980095759 4938261344494513470143639)
  ·
    refine ⟨7407392016741770205215459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4938261344494513470143639 7407392016741770205215459)
    ·
      refine ⟨11111088025112655307823189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7407392016741770205215459 11111088025112655307823189)
      ·
        refine ⟨130208062794288929388553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 11111088025112655307823189 130208062794288929388553)
        ·
          refine ⟨97656047095716697041415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130208062794288929388553 97656047095716697041415)
          ·
            refine ⟨146484070643575045562123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97656047095716697041415 146484070643575045562123)
            ·
              refine ⟨219726105965362568343185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146484070643575045562123 219726105965362568343185)
              ·
                refine ⟨164794579474021926257389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219726105965362568343185 164794579474021926257389)
                ·
                  refine ⟨61797967302758222346521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164794579474021926257389 61797967302758222346521)
                  ·
                    rfl

theorem cell20_135395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 3].length) (baseStart_135395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135395 prefixEnd_135395 := by exact prefixLift 135395
  have htrace : WordTrace (prefixWord ++ tailWord_135395) baseStart_135395 baseEnd_135395 := by
    simpa [prefixWord, tailWord_135395, baseEnd_135395] using wordTrace_append hprefix tailTrace_135395
  have hstable : (prefixWord ++ tailWord_135395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135395).length < 2 ^ (prefixWord ++ tailWord_135395).sum := by decide
  have hdescent : baseEnd_135395 < baseStart_135395 := by decide
  rcases family_descends (prefixWord ++ tailWord_135395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135399 : List Nat := [1, 1, 5, 3, 1, 1, 3, 2, 3]
def baseStart_135399 : Nat := 118140960795 + 135399 * 2 ^ 59
def prefixEnd_135399 : Nat := 4983230072969 + 3 ^ 40 * 135399 * 2
def baseEnd_135399 : Nat := 61799793011751986213171

theorem tailTrace_135399 : CollatzResearch.WordTrace tailWord_135399 prefixEnd_135399 61799793011751986213171 := by
  unfold tailWord_135399
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938407236480022153289251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3292271490986681435526167 4938407236480022153289251)
  ·
    refine ⟨7407610854720033229933877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4938407236480022153289251 7407610854720033229933877)
    ·
      refine ⟨694463517630003115306301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7407610854720033229933877 694463517630003115306301)
      ·
        refine ⟨260423819111251168239863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 694463517630003115306301 260423819111251168239863)
        ·
          refine ⟨390635728666876752359795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260423819111251168239863 390635728666876752359795)
          ·
            refine ⟨585953593000315128539693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390635728666876752359795 585953593000315128539693)
            ·
              refine ⟨219732597375118173202385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 585953593000315128539693 219732597375118173202385)
              ·
                refine ⟨164799448031338629901789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219732597375118173202385 164799448031338629901789)
                ·
                  refine ⟨61799793011751986213171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164799448031338629901789 61799793011751986213171)
                  ·
                    rfl

theorem cell20_135399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_135399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135399 prefixEnd_135399 := by exact prefixLift 135399
  have htrace : WordTrace (prefixWord ++ tailWord_135399) baseStart_135399 baseEnd_135399 := by
    simpa [prefixWord, tailWord_135399, baseEnd_135399] using wordTrace_append hprefix tailTrace_135399
  have hstable : (prefixWord ++ tailWord_135399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135399).length < 2 ^ (prefixWord ++ tailWord_135399).sum := by decide
  have hdescent : baseEnd_135399 < baseStart_135399 := by decide
  rcases family_descends (prefixWord ++ tailWord_135399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135403 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_135403 : Nat := 118140960795 + 135403 * 2 ^ 59
def prefixEnd_135403 : Nat := 4983230072969 + 3 ^ 40 * 135403 * 2
def baseEnd_135403 : Nat := 61801618720745750079821

theorem tailTrace_135403 : CollatzResearch.WordTrace tailWord_135403 prefixEnd_135403 61801618720745750079821 := by
  unfold tailWord_135403
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938553128465530836434863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3292368752310353890956575 4938553128465530836434863)
  ·
    refine ⟨7407829692698296254652295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4938553128465530836434863 7407829692698296254652295)
    ·
      refine ⟨11111744539047444381978443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7407829692698296254652295 11111744539047444381978443)
      ·
        refine ⟨16667616808571166572967665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11111744539047444381978443 16667616808571166572967665)
        ·
          refine ⟨12500712606428374929725749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16667616808571166572967665 12500712606428374929725749)
          ·
            refine ⟨1171941806852660149661789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12500712606428374929725749 1171941806852660149661789)
            ·
              refine ⟨439478177569747556123171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1171941806852660149661789 439478177569747556123171)
              ·
                refine ⟨659217266354621334184757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439478177569747556123171 659217266354621334184757)
                ·
                  refine ⟨61801618720745750079821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 659217266354621334184757 61801618720745750079821)
                  ·
                    rfl

theorem cell20_135403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_135403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135403 prefixEnd_135403 := by exact prefixLift 135403
  have htrace : WordTrace (prefixWord ++ tailWord_135403) baseStart_135403 baseEnd_135403 := by
    simpa [prefixWord, tailWord_135403, baseEnd_135403] using wordTrace_append hprefix tailTrace_135403
  have hstable : (prefixWord ++ tailWord_135403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135403).length < 2 ^ (prefixWord ++ tailWord_135403).sum := by decide
  have hdescent : baseEnd_135403 < baseStart_135403 := by decide
  rcases family_descends (prefixWord ++ tailWord_135403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135441 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_135441 : Nat := 118140960795 + 135441 * 2 ^ 59
def prefixEnd_135441 : Nat := 4983230072969 + 3 ^ 40 * 135441 * 2
def baseEnd_135441 : Nat := 61818962956186506812999

theorem tailTrace_135441 : CollatzResearch.WordTrace tailWord_135441 prefixEnd_135441 61818962956186506812999 := by
  unfold tailWord_135441
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939939102327863326318177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3293292734885242217545451 4939939102327863326318177)
  ·
    refine ⟨3704954326745897494738633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4939939102327863326318177 3704954326745897494738633)
    ·
      refine ⟨2778715745059423121053975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3704954326745897494738633 2778715745059423121053975)
      ·
        refine ⟨4168073617589134681580963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778715745059423121053975 4168073617589134681580963)
        ·
          refine ⟨6252110426383702022371445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4168073617589134681580963 6252110426383702022371445)
          ·
            refine ⟨586135352473472064597323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6252110426383702022371445 586135352473472064597323)
            ·
              refine ⟨879203028710208096895985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586135352473472064597323 879203028710208096895985)
              ·
                refine ⟨659402271532656072671989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879203028710208096895985 659402271532656072671989)
                ·
                  refine ⟨61818962956186506812999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 659402271532656072671989 61818962956186506812999)
                  ·
                    rfl

theorem cell20_135441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_135441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135441 prefixEnd_135441 := by exact prefixLift 135441
  have htrace : WordTrace (prefixWord ++ tailWord_135441) baseStart_135441 baseEnd_135441 := by
    simpa [prefixWord, tailWord_135441, baseEnd_135441] using wordTrace_append hprefix tailTrace_135441
  have hstable : (prefixWord ++ tailWord_135441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135441).length < 2 ^ (prefixWord ++ tailWord_135441).sum := by decide
  have hdescent : baseEnd_135441 < baseStart_135441 := by decide
  rcases family_descends (prefixWord ++ tailWord_135441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135458 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_135458 : Nat := 118140960795 + 135458 * 2 ^ 59
def prefixEnd_135458 : Nat := 4983230072969 + 3 ^ 40 * 135458 * 2
def baseEnd_135458 : Nat := 61826722219410003246263

theorem tailTrace_135458 : CollatzResearch.WordTrace tailWord_135458 prefixEnd_135458 61826722219410003246263 := by
  unfold tailWord_135458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235139785816568807421757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3293706095510850153124685 1235139785816568807421757)
  ·
    refine ⟨463177419681213302783159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1235139785816568807421757 463177419681213302783159)
    ·
      refine ⟨694766129521819954174739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463177419681213302783159 694766129521819954174739)
      ·
        refine ⟨1042149194282729931262109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694766129521819954174739 1042149194282729931262109)
        ·
          refine ⟨390805947856023724223291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1042149194282729931262109 390805947856023724223291)
          ·
            refine ⟨586208921784035586334937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390805947856023724223291 586208921784035586334937)
            ·
              refine ⟨439656691338026689751203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586208921784035586334937 439656691338026689751203)
              ·
                refine ⟨659485037007040034626805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439656691338026689751203 659485037007040034626805)
                ·
                  refine ⟨61826722219410003246263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 659485037007040034626805 61826722219410003246263)
                  ·
                    rfl

theorem cell20_135458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_135458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135458 prefixEnd_135458 := by exact prefixLift 135458
  have htrace : WordTrace (prefixWord ++ tailWord_135458) baseStart_135458 baseEnd_135458 := by
    simpa [prefixWord, tailWord_135458, baseEnd_135458] using wordTrace_append hprefix tailTrace_135458
  have hstable : (prefixWord ++ tailWord_135458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135458).length < 2 ^ (prefixWord ++ tailWord_135458).sum := by decide
  have hdescent : baseEnd_135458 < baseStart_135458 := by decide
  rcases family_descends (prefixWord ++ tailWord_135458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135461 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 4]
def baseStart_135461 : Nat := 118140960795 + 135461 * 2 ^ 59
def prefixEnd_135461 : Nat := 4983230072969 + 3 ^ 40 * 135461 * 2
def baseEnd_135461 : Nat := 61828091501155326146251

theorem tailTrace_135461 : CollatzResearch.WordTrace tailWord_135461 prefixEnd_135461 61828091501155326146251 := by
  unfold tailWord_135461
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940668562255406742046237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3293779041503604494697491 4940668562255406742046237)
  ·
    refine ⟨1852750710845777528267339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4940668562255406742046237 1852750710845777528267339)
    ·
      refine ⟨2779126066268666292401009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1852750710845777528267339 2779126066268666292401009)
      ·
        refine ⟨2084344549701499719300757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2779126066268666292401009 2084344549701499719300757)
        ·
          refine ⟨97703650767257799342223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2084344549701499719300757 97703650767257799342223)
          ·
            refine ⟨146555476150886699013335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97703650767257799342223 146555476150886699013335)
            ·
              refine ⟨219833214226330048520003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146555476150886699013335 219833214226330048520003)
              ·
                refine ⟨329749821339495072780005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219833214226330048520003 329749821339495072780005)
                ·
                  refine ⟨61828091501155326146251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329749821339495072780005 61828091501155326146251)
                  ·
                    rfl

theorem cell20_135461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_135461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135461 prefixEnd_135461 := by exact prefixLift 135461
  have htrace : WordTrace (prefixWord ++ tailWord_135461) baseStart_135461 baseEnd_135461 := by
    simpa [prefixWord, tailWord_135461, baseEnd_135461] using wordTrace_append hprefix tailTrace_135461
  have hstable : (prefixWord ++ tailWord_135461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135461).length < 2 ^ (prefixWord ++ tailWord_135461).sum := by decide
  have hdescent : baseEnd_135461 < baseStart_135461 := by decide
  rcases family_descends (prefixWord ++ tailWord_135461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135516 : List Nat := [2, 2, 4, 3, 1, 1, 1, 4, 2]
def baseStart_135516 : Nat := 118140960795 + 135516 * 2 ^ 59
def prefixEnd_135516 : Nat := 4983230072969 + 3 ^ 40 * 135516 * 2
def baseEnd_135516 : Nat := 61853194999819579312693

theorem tailTrace_135516 : CollatzResearch.WordTrace tailWord_135516 prefixEnd_135516 61853194999819579312693 := by
  unfold tailWord_135516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2471337288528075567649201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3295116384704100756865601 2471337288528075567649201)
  ·
    refine ⟨1853502966396056675736901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2471337288528075567649201 1853502966396056675736901)
    ·
      refine ⟨347531806199260626700669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1853502966396056675736901 347531806199260626700669)
      ·
        refine ⟨130324427324722735012751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347531806199260626700669 130324427324722735012751)
        ·
          refine ⟨195486640987084102519127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130324427324722735012751 195486640987084102519127)
          ·
            refine ⟨293229961480626153778691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195486640987084102519127 293229961480626153778691)
            ·
              refine ⟨439844942220939230668037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293229961480626153778691 439844942220939230668037)
              ·
                refine ⟨82470926666426105750257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 439844942220939230668037 82470926666426105750257)
                ·
                  refine ⟨61853194999819579312693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82470926666426105750257 61853194999819579312693)
                  ·
                    rfl

theorem cell20_135516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_135516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135516 prefixEnd_135516 := by exact prefixLift 135516
  have htrace : WordTrace (prefixWord ++ tailWord_135516) baseStart_135516 baseEnd_135516 := by
    simpa [prefixWord, tailWord_135516, baseEnd_135516] using wordTrace_append hprefix tailTrace_135516
  have hstable : (prefixWord ++ tailWord_135516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135516).length < 2 ^ (prefixWord ++ tailWord_135516).sum := by decide
  have hdescent : baseEnd_135516 < baseStart_135516 := by decide
  rcases family_descends (prefixWord ++ tailWord_135516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135527 : List Nat := [1, 1, 5, 1, 3, 3, 1, 5]
def baseStart_135527 : Nat := 118140960795 + 135527 * 2 ^ 59
def prefixEnd_135527 : Nat := 4983230072969 + 3 ^ 40 * 135527 * 2
def baseEnd_135527 : Nat := 20619405233184143315327

theorem tailTrace_135527 : CollatzResearch.WordTrace tailWord_135527 prefixEnd_135527 20619405233184143315327 := by
  unfold tailWord_135527
  simp only [CollatzResearch.WordTrace]
  refine ⟨4943075780016300013948835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3295383853344200009299223 4943075780016300013948835)
  ·
    refine ⟨7414613670024450020923253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4943075780016300013948835 7414613670024450020923253)
    ·
      refine ⟨695120031564792189461555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7414613670024450020923253 695120031564792189461555)
      ·
        refine ⟨1042680047347188284192333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695120031564792189461555 1042680047347188284192333)
        ·
          refine ⟨391005017755195606572125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1042680047347188284192333 391005017755195606572125)
          ·
            refine ⟨146626881658198352464547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 391005017755195606572125 146626881658198352464547)
            ·
              refine ⟨219940322487297528696821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146626881658198352464547 219940322487297528696821)
              ·
                refine ⟨20619405233184143315327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 219940322487297528696821 20619405233184143315327)
                ·
                  rfl

theorem cell20_135527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 5].length) (baseStart_135527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135527 prefixEnd_135527 := by exact prefixLift 135527
  have htrace : WordTrace (prefixWord ++ tailWord_135527) baseStart_135527 baseEnd_135527 := by
    simpa [prefixWord, tailWord_135527, baseEnd_135527] using wordTrace_append hprefix tailTrace_135527
  have hstable : (prefixWord ++ tailWord_135527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135527).length < 2 ^ (prefixWord ++ tailWord_135527).sum := by decide
  have hdescent : baseEnd_135527 < baseStart_135527 := by decide
  rcases family_descends (prefixWord ++ tailWord_135527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135541 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_135541 : Nat := 118140960795 + 135541 * 2 ^ 59
def prefixEnd_135541 : Nat := 4983230072969 + 3 ^ 40 * 135541 * 2
def baseEnd_135541 : Nat := 61864605681030603479257

theorem tailTrace_135541 : CollatzResearch.WordTrace tailWord_135541 prefixEnd_135541 61864605681030603479257 := by
  unfold tailWord_135541
  simp only [CollatzResearch.WordTrace]
  refine ⟨4943586401965580404958477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3295724267977053603305651 4943586401965580404958477)
  ·
    refine ⟨1853844900737092651859429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4943586401965580404958477 1853844900737092651859429)
    ·
      refine ⟨347595918888204872223643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1853844900737092651859429 347595918888204872223643)
      ·
        refine ⟨521393878332307308335465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347595918888204872223643 521393878332307308335465)
        ·
          refine ⟨391045408749230481251599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 521393878332307308335465 391045408749230481251599)
          ·
            refine ⟨586568113123845721877399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391045408749230481251599 586568113123845721877399)
            ·
              refine ⟨879852169685768582816099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586568113123845721877399 879852169685768582816099)
              ·
                refine ⟨1319778254528652874224149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879852169685768582816099 1319778254528652874224149)
                ·
                  refine ⟨61864605681030603479257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1319778254528652874224149 61864605681030603479257)
                  ·
                    rfl

theorem cell20_135541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_135541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135541 prefixEnd_135541 := by exact prefixLift 135541
  have htrace : WordTrace (prefixWord ++ tailWord_135541) baseStart_135541 baseEnd_135541 := by
    simpa [prefixWord, tailWord_135541, baseEnd_135541] using wordTrace_append hprefix tailTrace_135541
  have hstable : (prefixWord ++ tailWord_135541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135541).length < 2 ^ (prefixWord ++ tailWord_135541).sum := by decide
  have hdescent : baseEnd_135541 < baseStart_135541 := by decide
  rcases family_descends (prefixWord ++ tailWord_135541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135586 : List Nat := [3, 3, 1, 2, 1, 1, 2, 7]
def baseStart_135586 : Nat := 118140960795 + 135586 * 2 ^ 59
def prefixEnd_135586 : Nat := 4983230072969 + 3 ^ 40 * 135586 * 2
def baseEnd_135586 : Nat := 20628381635736815659691

theorem tailTrace_135586 : CollatzResearch.WordTrace tailWord_135586 prefixEnd_135586 20628381635736815659691 := by
  unfold tailWord_135586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1236306921700638272586653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3296818457868368726897741 1236306921700638272586653)
  ·
    refine ⟨463615095637739352219995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1236306921700638272586653 463615095637739352219995)
    ·
      refine ⟨695422643456609028329993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463615095637739352219995 695422643456609028329993)
      ·
        refine ⟨521566982592456771247495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 695422643456609028329993 521566982592456771247495)
        ·
          refine ⟨782350473888685156871243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521566982592456771247495 782350473888685156871243)
          ·
            refine ⟨1173525710833027735306865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782350473888685156871243 1173525710833027735306865)
            ·
              refine ⟨880144283124770801480149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173525710833027735306865 880144283124770801480149)
              ·
                refine ⟨20628381635736815659691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 880144283124770801480149 20628381635736815659691)
                ·
                  rfl

theorem cell20_135586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_135586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135586 prefixEnd_135586 := by exact prefixLift 135586
  have htrace : WordTrace (prefixWord ++ tailWord_135586) baseStart_135586 baseEnd_135586 := by
    simpa [prefixWord, tailWord_135586, baseEnd_135586] using wordTrace_append hprefix tailTrace_135586
  have hstable : (prefixWord ++ tailWord_135586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135586).length < 2 ^ (prefixWord ++ tailWord_135586).sum := by decide
  have hdescent : baseEnd_135586 < baseStart_135586 := by decide
  rcases family_descends (prefixWord ++ tailWord_135586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135593 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 3]
def baseStart_135593 : Nat := 118140960795 + 135593 * 2 ^ 59
def prefixEnd_135593 : Nat := 4983230072969 + 3 ^ 40 * 135593 * 2
def baseEnd_135593 : Nat := 61888339897949533745711

theorem tailTrace_135593 : CollatzResearch.WordTrace tailWord_135593 prefixEnd_135593 61888339897949533745711 := by
  unfold tailWord_135593
  simp only [CollatzResearch.WordTrace]
  refine ⟨4945482997777193285851433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3296988665184795523900955 4945482997777193285851433)
  ·
    refine ⟨3709112248332894964388575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4945482997777193285851433 3709112248332894964388575)
    ·
      refine ⟨5563668372499342446582863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3709112248332894964388575 5563668372499342446582863)
      ·
        refine ⟨8345502558749013669874295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5563668372499342446582863 8345502558749013669874295)
        ·
          refine ⟨12518253838123520504811443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8345502558749013669874295 12518253838123520504811443)
          ·
            refine ⟨18777380757185280757217165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12518253838123520504811443 18777380757185280757217165)
            ·
              refine ⟨7041517783944480283956437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18777380757185280757217165 7041517783944480283956437)
              ·
                refine ⟨165035573061198756655229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7041517783944480283956437 165035573061198756655229)
                ·
                  refine ⟨61888339897949533745711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165035573061198756655229 61888339897949533745711)
                  ·
                    rfl

theorem cell20_135593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_135593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135593 prefixEnd_135593 := by exact prefixLift 135593
  have htrace : WordTrace (prefixWord ++ tailWord_135593) baseStart_135593 baseEnd_135593 := by
    simpa [prefixWord, tailWord_135593, baseEnd_135593] using wordTrace_append hprefix tailTrace_135593
  have hstable : (prefixWord ++ tailWord_135593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135593).length < 2 ^ (prefixWord ++ tailWord_135593).sum := by decide
  have hdescent : baseEnd_135593 < baseStart_135593 := by decide
  rcases family_descends (prefixWord ++ tailWord_135593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135613 : List Nat := [1, 4, 1, 2, 2, 4, 1, 3, 2]
def baseStart_135613 : Nat := 118140960795 + 135613 * 2 ^ 59
def prefixEnd_135613 : Nat := 4983230072969 + 3 ^ 40 * 135613 * 2
def baseEnd_135613 : Nat := 61897468442918353078963

theorem tailTrace_135613 : CollatzResearch.WordTrace tailWord_135613 prefixEnd_135613 61897468442918353078963 := by
  unfold tailWord_135613
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946212457704736701579493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3297474971803157801052995 4946212457704736701579493)
  ·
    refine ⟨927414835819638131546155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4946212457704736701579493 927414835819638131546155)
    ·
      refine ⟨1391122253729457197319233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 927414835819638131546155 1391122253729457197319233)
      ·
        refine ⟨1043341690297092897989425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1391122253729457197319233 1043341690297092897989425)
        ·
          refine ⟨782506267722819673492069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1043341690297092897989425 782506267722819673492069)
          ·
            refine ⟨146719925198028688779763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 782506267722819673492069 146719925198028688779763)
            ·
              refine ⟨220079887797043033169645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146719925198028688779763 220079887797043033169645)
              ·
                refine ⟨82529957923891137438617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220079887797043033169645 82529957923891137438617)
                ·
                  refine ⟨61897468442918353078963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82529957923891137438617 61897468442918353078963)
                  ·
                    rfl

theorem cell20_135613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_135613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135613 prefixEnd_135613 := by exact prefixLift 135613
  have htrace : WordTrace (prefixWord ++ tailWord_135613) baseStart_135613 baseEnd_135613 := by
    simpa [prefixWord, tailWord_135613, baseEnd_135613] using wordTrace_append hprefix tailTrace_135613
  have hstable : (prefixWord ++ tailWord_135613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135613).length < 2 ^ (prefixWord ++ tailWord_135613).sum := by decide
  have hdescent : baseEnd_135613 < baseStart_135613 := by decide
  rcases family_descends (prefixWord ++ tailWord_135613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135620 : List Nat := [2, 3, 3, 2, 3, 1, 6]
def baseStart_135620 : Nat := 118140960795 + 135620 * 2 ^ 59
def prefixEnd_135620 : Nat := 4983230072969 + 3 ^ 40 * 135620 * 2
def baseEnd_135620 : Nat := 6877851492628604427289

theorem tailTrace_135620 : CollatzResearch.WordTrace tailWord_135620 prefixEnd_135620 6877851492628604427289 := by
  unfold tailWord_135620
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473233884339688448542157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3297645179119584598056209 2473233884339688448542157)
  ·
    refine ⟨927462706627383168203309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2473233884339688448542157 927462706627383168203309)
    ·
      refine ⟨347798514985268688076241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 927462706627383168203309 347798514985268688076241)
      ·
        refine ⟨260848886238951516057181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347798514985268688076241 260848886238951516057181)
        ·
          refine ⟨97818332339606818521443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260848886238951516057181 97818332339606818521443)
          ·
            refine ⟨146727498509410227782165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97818332339606818521443 146727498509410227782165)
            ·
              refine ⟨6877851492628604427289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146727498509410227782165 6877851492628604427289)
              ·
                rfl

theorem cell20_135620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 6].length) (baseStart_135620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135620 prefixEnd_135620 := by exact prefixLift 135620
  have htrace : WordTrace (prefixWord ++ tailWord_135620) baseStart_135620 baseEnd_135620 := by
    simpa [prefixWord, tailWord_135620, baseEnd_135620] using wordTrace_append hprefix tailTrace_135620
  have hstable : (prefixWord ++ tailWord_135620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135620).length < 2 ^ (prefixWord ++ tailWord_135620).sum := by decide
  have hdescent : baseEnd_135620 < baseStart_135620 := by decide
  rcases family_descends (prefixWord ++ tailWord_135620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135624 : List Nat := [2, 1, 3, 1, 3, 4, 6]
def baseStart_135624 : Nat := 118140960795 + 135624 * 2 ^ 59
def prefixEnd_135624 : Nat := 4983230072969 + 3 ^ 40 * 135624 * 2
def baseEnd_135624 : Nat := 6878054349183467079139

theorem tailTrace_135624 : CollatzResearch.WordTrace tailWord_135624 prefixEnd_135624 6878054349183467079139 := by
  unfold tailWord_135624
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473306830332442790114963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3297742440443257053486617 2473306830332442790114963)
  ·
    refine ⟨3709960245498664185172445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2473306830332442790114963 3709960245498664185172445)
    ·
      refine ⟨1391235092061999069439667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3709960245498664185172445 1391235092061999069439667)
      ·
        refine ⟨2086852638092998604159501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391235092061999069439667 2086852638092998604159501)
        ·
          refine ⟨782569739284874476559813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2086852638092998604159501 782569739284874476559813)
          ·
            refine ⟨146731826115913964354965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 782569739284874476559813 146731826115913964354965)
            ·
              refine ⟨6878054349183467079139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146731826115913964354965 6878054349183467079139)
              ·
                rfl

theorem cell20_135624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 6].length) (baseStart_135624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135624 prefixEnd_135624 := by exact prefixLift 135624
  have htrace : WordTrace (prefixWord ++ tailWord_135624) baseStart_135624 baseEnd_135624 := by
    simpa [prefixWord, tailWord_135624, baseEnd_135624] using wordTrace_append hprefix tailTrace_135624
  have hstable : (prefixWord ++ tailWord_135624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135624).length < 2 ^ (prefixWord ++ tailWord_135624).sum := by decide
  have hdescent : baseEnd_135624 < baseStart_135624 := by decide
  rcases family_descends (prefixWord ++ tailWord_135624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135631 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 3]
def baseStart_135631 : Nat := 118140960795 + 135631 * 2 ^ 59
def prefixEnd_135631 : Nat := 4983230072969 + 3 ^ 40 * 135631 * 2
def baseEnd_135631 : Nat := 61905684133390290478889

theorem tailTrace_135631 : CollatzResearch.WordTrace tailWord_135631 prefixEnd_135631 61905684133390290478889 := by
  unfold tailWord_135631
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946868971639525775734747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3297912647759683850489831 4946868971639525775734747)
  ·
    refine ⟨7420303457459288663602121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4946868971639525775734747 7420303457459288663602121)
    ·
      refine ⟨5565227593094466497701591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7420303457459288663602121 5565227593094466497701591)
      ·
        refine ⟨8347841389641699746552387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5565227593094466497701591 8347841389641699746552387)
        ·
          refine ⟨12521762084462549619828581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8347841389641699746552387 12521762084462549619828581)
          ·
            refine ⟨2347830390836728053717859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12521762084462549619828581 2347830390836728053717859)
            ·
              refine ⟨3521745586255092080576789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347830390836728053717859 3521745586255092080576789)
              ·
                refine ⟨165081824355707441277037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3521745586255092080576789 165081824355707441277037)
                ·
                  refine ⟨61905684133390290478889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165081824355707441277037 61905684133390290478889)
                  ·
                    rfl

theorem cell20_135631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_135631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135631 prefixEnd_135631 := by exact prefixLift 135631
  have htrace : WordTrace (prefixWord ++ tailWord_135631) baseStart_135631 baseEnd_135631 := by
    simpa [prefixWord, tailWord_135631, baseEnd_135631] using wordTrace_append hprefix tailTrace_135631
  have hstable : (prefixWord ++ tailWord_135631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135631).length < 2 ^ (prefixWord ++ tailWord_135631).sum := by decide
  have hdescent : baseEnd_135631 < baseStart_135631 := by decide
  rcases family_descends (prefixWord ++ tailWord_135631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135662 : List Nat := [4, 1, 2, 1, 2, 2, 2, 6]
def baseStart_135662 : Nat := 118140960795 + 135662 * 2 ^ 59
def prefixEnd_135662 : Nat := 4983230072969 + 3 ^ 40 * 135662 * 2
def baseEnd_135662 : Nat := 20639944459363986815143

theorem tailTrace_135662 : CollatzResearch.WordTrace tailWord_135662 prefixEnd_135662 20639944459363986815143 := by
  unfold tailWord_135662
  simp only [CollatzResearch.WordTrace]
  refine ⟨618499954315902258764155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3298666423018145380075493 618499954315902258764155)
  ·
    refine ⟨927749931473853388146233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618499954315902258764155 927749931473853388146233)
    ·
      refine ⟨695812448605390041109675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 927749931473853388146233 695812448605390041109675)
      ·
        refine ⟨1043718672908085061664513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695812448605390041109675 1043718672908085061664513)
        ·
          refine ⟨782789004681063796248385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1043718672908085061664513 782789004681063796248385)
          ·
            refine ⟨587091753510797847186289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782789004681063796248385 587091753510797847186289)
            ·
              refine ⟨440318815133098385389717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587091753510797847186289 440318815133098385389717)
              ·
                refine ⟨20639944459363986815143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 440318815133098385389717 20639944459363986815143)
                ·
                  rfl

theorem cell20_135662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_135662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135662 prefixEnd_135662 := by exact prefixLift 135662
  have htrace : WordTrace (prefixWord ++ tailWord_135662) baseStart_135662 baseEnd_135662 := by
    simpa [prefixWord, tailWord_135662, baseEnd_135662] using wordTrace_append hprefix tailTrace_135662
  have hstable : (prefixWord ++ tailWord_135662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135662).length < 2 ^ (prefixWord ++ tailWord_135662).sum := by decide
  have hdescent : baseEnd_135662 < baseStart_135662 := by decide
  rcases family_descends (prefixWord ++ tailWord_135662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135682 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_135682 : Nat := 118140960795 + 135682 * 2 ^ 59
def prefixEnd_135682 : Nat := 4983230072969 + 3 ^ 40 * 135682 * 2
def baseEnd_135682 : Nat := 61928961923060779778681

theorem tailTrace_135682 : CollatzResearch.WordTrace tailWord_135682 prefixEnd_135682 61928961923060779778681 := by
  unfold tailWord_135682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237182273613690371460325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3299152729636507657227533 1237182273613690371460325)
  ·
    refine ⟨231971676302566944648811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1237182273613690371460325 231971676302566944648811)
    ·
      refine ⟨347957514453850416973217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231971676302566944648811 347957514453850416973217)
      ·
        refine ⟨260968135840387812729913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347957514453850416973217 260968135840387812729913)
        ·
          refine ⟨195726101880290859547435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260968135840387812729913 195726101880290859547435)
          ·
            refine ⟨293589152820436289321153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195726101880290859547435 293589152820436289321153)
            ·
              refine ⟨220191864615327216990865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293589152820436289321153 220191864615327216990865)
              ·
                refine ⟨165143898461495412743149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220191864615327216990865 165143898461495412743149)
                ·
                  refine ⟨61928961923060779778681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165143898461495412743149 61928961923060779778681)
                  ·
                    rfl

theorem cell20_135682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_135682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135682 prefixEnd_135682 := by exact prefixLift 135682
  have htrace : WordTrace (prefixWord ++ tailWord_135682) baseStart_135682 baseEnd_135682 := by
    simpa [prefixWord, tailWord_135682, baseEnd_135682] using wordTrace_append hprefix tailTrace_135682
  have hstable : (prefixWord ++ tailWord_135682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135682).length < 2 ^ (prefixWord ++ tailWord_135682).sum := by decide
  have hdescent : baseEnd_135682 < baseStart_135682 := by decide
  rcases family_descends (prefixWord ++ tailWord_135682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135741 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 3]
def baseStart_135741 : Nat := 118140960795 + 135741 * 2 ^ 59
def prefixEnd_135741 : Nat := 4983230072969 + 3 ^ 40 * 135741 * 2
def baseEnd_135741 : Nat := 61955891130718796811773

theorem tailTrace_135741 : CollatzResearch.WordTrace tailWord_135741 prefixEnd_135741 61955891130718796811773 := by
  unfold tailWord_135741
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950881001241014562239077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3300587334160676374826051 4950881001241014562239077)
  ·
    refine ⟨928290187732690230419827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4950881001241014562239077 928290187732690230419827)
    ·
      refine ⟨1392435281599035345629741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928290187732690230419827 1392435281599035345629741)
      ·
        refine ⟨522163230599638254611153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1392435281599035345629741 522163230599638254611153)
        ·
          refine ⟨391622422949728690958365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522163230599638254611153 391622422949728690958365)
          ·
            refine ⟨146858408606148259109387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 391622422949728690958365 146858408606148259109387)
            ·
              refine ⟨220287612909222388664081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146858408606148259109387 220287612909222388664081)
              ·
                refine ⟨165215709681916791498061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220287612909222388664081 165215709681916791498061)
                ·
                  refine ⟨61955891130718796811773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165215709681916791498061 61955891130718796811773)
                  ·
                    rfl

theorem cell20_135741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_135741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135741 prefixEnd_135741 := by exact prefixLift 135741
  have htrace : WordTrace (prefixWord ++ tailWord_135741) baseStart_135741 baseEnd_135741 := by
    simpa [prefixWord, tailWord_135741, baseEnd_135741] using wordTrace_append hprefix tailTrace_135741
  have hstable : (prefixWord ++ tailWord_135741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135741).length < 2 ^ (prefixWord ++ tailWord_135741).sum := by decide
  have hdescent : baseEnd_135741 < baseStart_135741 := by decide
  rcases family_descends (prefixWord ++ tailWord_135741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135772 : List Nat := [2, 2, 4, 1, 3, 2, 2, 4]
def baseStart_135772 : Nat := 118140960795 + 135772 * 2 ^ 59
def prefixEnd_135772 : Nat := 4983230072969 + 3 ^ 40 * 135772 * 2
def baseEnd_135772 : Nat := 20656680125140155592771

theorem tailTrace_135772 : CollatzResearch.WordTrace tailWord_135772 prefixEnd_135772 20656680125140155592771 := by
  unfold tailWord_135772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476005832064353428308785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3301341109419137904411713 2476005832064353428308785)
  ·
    refine ⟨1857004374048265071231589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2476005832064353428308785 1857004374048265071231589)
    ·
      refine ⟨348188320134049700855923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1857004374048265071231589 348188320134049700855923)
      ·
        refine ⟨522282480201074551283885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348188320134049700855923 522282480201074551283885)
        ·
          refine ⟨195855930075402956731457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 522282480201074551283885 195855930075402956731457)
          ·
            refine ⟨146891947556552217548593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195855930075402956731457 146891947556552217548593)
            ·
              refine ⟨110168960667414163161445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146891947556552217548593 110168960667414163161445)
              ·
                refine ⟨20656680125140155592771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110168960667414163161445 20656680125140155592771)
                ·
                  rfl

theorem cell20_135772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_135772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135772 prefixEnd_135772 := by exact prefixLift 135772
  have htrace : WordTrace (prefixWord ++ tailWord_135772) baseStart_135772 baseEnd_135772 := by
    simpa [prefixWord, tailWord_135772, baseEnd_135772] using wordTrace_append hprefix tailTrace_135772
  have hstable : (prefixWord ++ tailWord_135772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135772).length < 2 ^ (prefixWord ++ tailWord_135772).sum := by decide
  have hdescent : baseEnd_135772 < baseStart_135772 := by decide
  rcases family_descends (prefixWord ++ tailWord_135772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135776 : List Nat := [2, 1, 1, 3, 2, 1, 6, 4]
def baseStart_135776 : Nat := 118140960795 + 135776 * 2 ^ 59
def prefixEnd_135776 : Nat := 4983230072969 + 3 ^ 40 * 135776 * 2
def baseEnd_135776 : Nat := 20657288694804743548321

theorem tailTrace_135776 : CollatzResearch.WordTrace tailWord_135776 prefixEnd_135776 20657288694804743548321 := by
  unfold tailWord_135776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476078778057107769881591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3301438370742810359842121 2476078778057107769881591)
  ·
    refine ⟨3714118167085661654822387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2476078778057107769881591 3714118167085661654822387)
    ·
      refine ⟨5571177250628492482233581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3714118167085661654822387 5571177250628492482233581)
      ·
        refine ⟨2089191468985684680837593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5571177250628492482233581 2089191468985684680837593)
        ·
          refine ⟨1566893601739263510628195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2089191468985684680837593 1566893601739263510628195)
          ·
            refine ⟨2350340402608895265942293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566893601739263510628195 2350340402608895265942293)
            ·
              refine ⟨110172206372291965591045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2350340402608895265942293 110172206372291965591045)
              ·
                refine ⟨20657288694804743548321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110172206372291965591045 20657288694804743548321)
                ·
                  rfl

theorem cell20_135776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_135776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135776 prefixEnd_135776 := by exact prefixLift 135776
  have htrace : WordTrace (prefixWord ++ tailWord_135776) baseStart_135776 baseEnd_135776 := by
    simpa [prefixWord, tailWord_135776, baseEnd_135776] using wordTrace_append hprefix tailTrace_135776
  have hstable : (prefixWord ++ tailWord_135776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135776).length < 2 ^ (prefixWord ++ tailWord_135776).sum := by decide
  have hdescent : baseEnd_135776 < baseStart_135776 := by decide
  rcases family_descends (prefixWord ++ tailWord_135776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135845 : List Nat := [1, 3, 1, 2, 1, 2, 1, 7, 2]
def baseStart_135845 : Nat := 118140960795 + 135845 * 2 ^ 59
def prefixEnd_135845 : Nat := 4983230072969 + 3 ^ 40 * 135845 * 2
def baseEnd_135845 : Nat := 62003359564556657344681

theorem tailTrace_135845 : CollatzResearch.WordTrace tailWord_135845 prefixEnd_135845 62003359564556657344681 := by
  unfold tailWord_135845
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954674192864240324024989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3303116128576160216016659 4954674192864240324024989)
  ·
    refine ⟨1858002822324090121509371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4954674192864240324024989 1858002822324090121509371)
    ·
      refine ⟨2787004233486135182264057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1858002822324090121509371 2787004233486135182264057)
      ·
        refine ⟨2090253175114601386698043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2787004233486135182264057 2090253175114601386698043)
        ·
          refine ⟨3135379762671902080047065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090253175114601386698043 3135379762671902080047065)
          ·
            refine ⟨2351534822003926560035299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3135379762671902080047065 2351534822003926560035299)
            ·
              refine ⟨3527302233005889840052949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351534822003926560035299 3527302233005889840052949)
              ·
                refine ⟨82671146086075543126241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3527302233005889840052949 82671146086075543126241)
                ·
                  refine ⟨62003359564556657344681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82671146086075543126241 62003359564556657344681)
                  ·
                    rfl

theorem cell20_135845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_135845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135845 prefixEnd_135845 := by exact prefixLift 135845
  have htrace : WordTrace (prefixWord ++ tailWord_135845) baseStart_135845 baseEnd_135845 := by
    simpa [prefixWord, tailWord_135845, baseEnd_135845] using wordTrace_append hprefix tailTrace_135845
  have hstable : (prefixWord ++ tailWord_135845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135845).length < 2 ^ (prefixWord ++ tailWord_135845).sum := by decide
  have hdescent : baseEnd_135845 < baseStart_135845 := by decide
  rcases family_descends (prefixWord ++ tailWord_135845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135859 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 3]
def baseStart_135859 : Nat := 118140960795 + 135859 * 2 ^ 59
def prefixEnd_135859 : Nat := 4983230072969 + 3 ^ 40 * 135859 * 2
def baseEnd_135859 : Nat := 62009749546034830877957

theorem tailTrace_135859 : CollatzResearch.WordTrace tailWord_135859 prefixEnd_135859 62009749546034830877957 := by
  unfold tailWord_135859
  simp only [CollatzResearch.WordTrace]
  refine ⟨4955184814813520715034631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3303456543209013810023087 4955184814813520715034631)
  ·
    refine ⟨7432777222220281072551947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4955184814813520715034631 7432777222220281072551947)
    ·
      refine ⟨11149165833330421608827921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7432777222220281072551947 11149165833330421608827921)
      ·
        refine ⟨8361874374997816206620941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11149165833330421608827921 8361874374997816206620941)
        ·
          refine ⟨3135702890624181077482853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8361874374997816206620941 3135702890624181077482853)
          ·
            refine ⟨587944291992033952028035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3135702890624181077482853 587944291992033952028035)
            ·
              refine ⟨881916437988050928042053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587944291992033952028035 881916437988050928042053)
              ·
                refine ⟨165359332122759549007885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 881916437988050928042053 165359332122759549007885)
                ·
                  refine ⟨62009749546034830877957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165359332122759549007885 62009749546034830877957)
                  ·
                    rfl

theorem cell20_135859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_135859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135859 prefixEnd_135859 := by exact prefixLift 135859
  have htrace : WordTrace (prefixWord ++ tailWord_135859) baseStart_135859 baseEnd_135859 := by
    simpa [prefixWord, tailWord_135859, baseEnd_135859] using wordTrace_append hprefix tailTrace_135859
  have hstable : (prefixWord ++ tailWord_135859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135859).length < 2 ^ (prefixWord ++ tailWord_135859).sum := by decide
  have hdescent : baseEnd_135859 < baseStart_135859 := by decide
  rcases family_descends (prefixWord ++ tailWord_135859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135866 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_135866 : Nat := 118140960795 + 135866 * 2 ^ 59
def prefixEnd_135866 : Nat := 4983230072969 + 3 ^ 40 * 135866 * 2
def baseEnd_135866 : Nat := 62012944536773917644595

theorem tailTrace_135866 : CollatzResearch.WordTrace tailWord_135866 prefixEnd_135866 62012944536773917644595 := by
  unfold tailWord_135866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238860031447040227634863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3303626750525440607026301 1238860031447040227634863)
  ·
    refine ⟨1858290047170560341452295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1238860031447040227634863 1858290047170560341452295)
    ·
      refine ⟨2787435070755840512178443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1858290047170560341452295 2787435070755840512178443)
      ·
        refine ⟨4181152606133760768267665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2787435070755840512178443 4181152606133760768267665)
        ·
          refine ⟨3135864454600320576200749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4181152606133760768267665 3135864454600320576200749)
          ·
            refine ⟨1175949170475120216075281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3135864454600320576200749 1175949170475120216075281)
            ·
              refine ⟨881961877856340162056461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175949170475120216075281 881961877856340162056461)
              ·
                refine ⟨330735704196127560771173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881961877856340162056461 330735704196127560771173)
                ·
                  refine ⟨62012944536773917644595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330735704196127560771173 62012944536773917644595)
                  ·
                    rfl

theorem cell20_135866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_135866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135866 prefixEnd_135866 := by exact prefixLift 135866
  have htrace : WordTrace (prefixWord ++ tailWord_135866) baseStart_135866 baseEnd_135866 := by
    simpa [prefixWord, tailWord_135866, baseEnd_135866] using wordTrace_append hprefix tailTrace_135866
  have hstable : (prefixWord ++ tailWord_135866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135866).length < 2 ^ (prefixWord ++ tailWord_135866).sum := by decide
  have hdescent : baseEnd_135866 < baseStart_135866 := by decide
  rcases family_descends (prefixWord ++ tailWord_135866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135876 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_135876 : Nat := 118140960795 + 135876 * 2 ^ 59
def prefixEnd_135876 : Nat := 4983230072969 + 3 ^ 40 * 135876 * 2
def baseEnd_135876 : Nat := 62017508809258327311221

theorem tailTrace_135876 : CollatzResearch.WordTrace tailWord_135876 prefixEnd_135876 62017508809258327311221 := by
  unfold tailWord_135876
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477902427875966309201741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3303869903834621745602321 2477902427875966309201741)
  ·
    refine ⟨929213410453487365950653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2477902427875966309201741 929213410453487365950653)
    ·
      refine ⟨348455028920057762231495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 929213410453487365950653 348455028920057762231495)
      ·
        refine ⟨522682543380086643347243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348455028920057762231495 522682543380086643347243)
        ·
          refine ⟨784023815070129965020865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522682543380086643347243 784023815070129965020865)
          ·
            refine ⟨588017861302597473765649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784023815070129965020865 588017861302597473765649)
            ·
              refine ⟨441013395976948105324237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588017861302597473765649 441013395976948105324237)
              ·
                refine ⟨165380023491355539496589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441013395976948105324237 165380023491355539496589)
                ·
                  refine ⟨62017508809258327311221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165380023491355539496589 62017508809258327311221)
                  ·
                    rfl

theorem cell20_135876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_135876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135876 prefixEnd_135876 := by exact prefixLift 135876
  have htrace : WordTrace (prefixWord ++ tailWord_135876) baseStart_135876 baseEnd_135876 := by
    simpa [prefixWord, tailWord_135876, baseEnd_135876] using wordTrace_append hprefix tailTrace_135876
  have hstable : (prefixWord ++ tailWord_135876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135876).length < 2 ^ (prefixWord ++ tailWord_135876).sum := by decide
  have hdescent : baseEnd_135876 < baseStart_135876 := by decide
  rcases family_descends (prefixWord ++ tailWord_135876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135921 : List Nat := [1, 2, 2, 2, 2, 2, 1, 6, 2]
def baseStart_135921 : Nat := 118140960795 + 135921 * 2 ^ 59
def prefixEnd_135921 : Nat := 4983230072969 + 3 ^ 40 * 135921 * 2
def baseEnd_135921 : Nat := 62038048035438170811037

theorem tailTrace_135921 : CollatzResearch.WordTrace tailWord_135921 prefixEnd_135921 62038048035438170811037 := by
  unfold tailWord_135921
  simp only [CollatzResearch.WordTrace]
  refine ⟨4957446140588905303791617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3304964093725936869194411 4957446140588905303791617)
  ·
    refine ⟨3718084605441678977843713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4957446140588905303791617 3718084605441678977843713)
    ·
      refine ⟨2788563454081259233382785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3718084605441678977843713 2788563454081259233382785)
      ·
        refine ⟨2091422590560944425037089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2788563454081259233382785 2091422590560944425037089)
        ·
          refine ⟨1568566942920708318777817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2091422590560944425037089 1568566942920708318777817)
          ·
            refine ⟨1176425207190531239083363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568566942920708318777817 1176425207190531239083363)
            ·
              refine ⟨1764637810785796858625045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176425207190531239083363 1764637810785796858625045)
              ·
                refine ⟨82717397380584227748049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1764637810785796858625045 82717397380584227748049)
                ·
                  refine ⟨62038048035438170811037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82717397380584227748049 62038048035438170811037)
                  ·
                    rfl

theorem cell20_135921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_135921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135921 prefixEnd_135921 := by exact prefixLift 135921
  have htrace : WordTrace (prefixWord ++ tailWord_135921) baseStart_135921 baseEnd_135921 := by
    simpa [prefixWord, tailWord_135921, baseEnd_135921] using wordTrace_append hprefix tailTrace_135921
  have hstable : (prefixWord ++ tailWord_135921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135921).length < 2 ^ (prefixWord ++ tailWord_135921).sum := by decide
  have hdescent : baseEnd_135921 < baseStart_135921 := by decide
  rcases family_descends (prefixWord ++ tailWord_135921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135973 : List Nat := [1, 3, 1, 2, 3, 1, 2, 4, 3]
def baseStart_135973 : Nat := 118140960795 + 135973 * 2 ^ 59
def prefixEnd_135973 : Nat := 4983230072969 + 3 ^ 40 * 135973 * 2
def baseEnd_135973 : Nat := 62061782252357101077491

theorem tailTrace_135973 : CollatzResearch.WordTrace tailWord_135973 prefixEnd_135973 62061782252357101077491 := by
  unfold tailWord_135973
  simp only [CollatzResearch.WordTrace]
  refine ⟨4959342736400518184684573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3306228490933678789789715 4959342736400518184684573)
  ·
    refine ⟨1859753526150194319256715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4959342736400518184684573 1859753526150194319256715)
    ·
      refine ⟨2789630289225291478885073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859753526150194319256715 2789630289225291478885073)
      ·
        refine ⟨2092222716918968609163805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2789630289225291478885073 2092222716918968609163805)
        ·
          refine ⟨784583518844613228436427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2092222716918968609163805 784583518844613228436427)
          ·
            refine ⟨1176875278266919842654641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784583518844613228436427 1176875278266919842654641)
            ·
              refine ⟨882656458700189881990981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176875278266919842654641 882656458700189881990981)
              ·
                refine ⟨165498086006285602873309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 882656458700189881990981 165498086006285602873309)
                ·
                  refine ⟨62061782252357101077491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165498086006285602873309 62061782252357101077491)
                  ·
                    rfl

theorem cell20_135973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_135973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135973 prefixEnd_135973 := by exact prefixLift 135973
  have htrace : WordTrace (prefixWord ++ tailWord_135973) baseStart_135973 baseEnd_135973 := by
    simpa [prefixWord, tailWord_135973, baseEnd_135973] using wordTrace_append hprefix tailTrace_135973
  have hstable : (prefixWord ++ tailWord_135973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135973).length < 2 ^ (prefixWord ++ tailWord_135973).sum := by decide
  have hdescent : baseEnd_135973 < baseStart_135973 := by decide
  rcases family_descends (prefixWord ++ tailWord_135973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135987 : List Nat := [1, 1, 1, 2, 6, 1, 1, 7]
def baseStart_135987 : Nat := 118140960795 + 135987 * 2 ^ 59
def prefixEnd_135987 : Nat := 4983230072969 + 3 ^ 40 * 135987 * 2
def baseEnd_135987 : Nat := 20689390744611758203589

theorem tailTrace_135987 : CollatzResearch.WordTrace tailWord_135987 prefixEnd_135987 20689390744611758203589 := by
  unfold tailWord_135987
  simp only [CollatzResearch.WordTrace]
  refine ⟨4959853358349798575694215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3306568905566532383796143 4959853358349798575694215)
  ·
    refine ⟨7439780037524697863541323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4959853358349798575694215 7439780037524697863541323)
    ·
      refine ⟨11159670056287046795311985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7439780037524697863541323 11159670056287046795311985)
      ·
        refine ⟨8369752542215285096483989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11159670056287046795311985 8369752542215285096483989)
        ·
          refine ⟨392332150416341488897687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8369752542215285096483989 392332150416341488897687)
          ·
            refine ⟨588498225624512233346531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392332150416341488897687 588498225624512233346531)
            ·
              refine ⟨882747338436768350019797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588498225624512233346531 882747338436768350019797)
              ·
                refine ⟨20689390744611758203589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 882747338436768350019797 20689390744611758203589)
                ·
                  rfl

theorem cell20_135987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 7].length) (baseStart_135987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_135987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_135987 prefixEnd_135987 := by exact prefixLift 135987
  have htrace : WordTrace (prefixWord ++ tailWord_135987) baseStart_135987 baseEnd_135987 := by
    simpa [prefixWord, tailWord_135987, baseEnd_135987] using wordTrace_append hprefix tailTrace_135987
  have hstable : (prefixWord ++ tailWord_135987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135987).length < 2 ^ (prefixWord ++ tailWord_135987).sum := by decide
  have hdescent : baseEnd_135987 < baseStart_135987 := by decide
  rcases family_descends (prefixWord ++ tailWord_135987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136028 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_136028 : Nat := 118140960795 + 136028 * 2 ^ 59
def prefixEnd_136028 : Nat := 4983230072969 + 3 ^ 40 * 136028 * 2
def baseEnd_136028 : Nat := 62086885751021354243933

theorem tailTrace_136028 : CollatzResearch.WordTrace tailWord_136028 prefixEnd_136028 62086885751021354243933 := by
  unfold tailWord_136028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480674375600631288968369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3307565834134175051957825 2480674375600631288968369)
  ·
    refine ⟨1860505781700473466726277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2480674375600631288968369 1860505781700473466726277)
    ·
      refine ⟨348844834068838775011177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1860505781700473466726277 348844834068838775011177)
      ·
        refine ⟨261633625551629081258383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348844834068838775011177 261633625551629081258383)
        ·
          refine ⟨392450438327443621887575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261633625551629081258383 392450438327443621887575)
          ·
            refine ⟨588675657491165432831363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392450438327443621887575 588675657491165432831363)
            ·
              refine ⟨883013486236748149247045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588675657491165432831363 883013486236748149247045)
              ·
                refine ⟨165565028669390277983821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 883013486236748149247045 165565028669390277983821)
                ·
                  refine ⟨62086885751021354243933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165565028669390277983821 62086885751021354243933)
                  ·
                    rfl

theorem cell20_136028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_136028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136028 prefixEnd_136028 := by exact prefixLift 136028
  have htrace : WordTrace (prefixWord ++ tailWord_136028) baseStart_136028 baseEnd_136028 := by
    simpa [prefixWord, tailWord_136028, baseEnd_136028] using wordTrace_append hprefix tailTrace_136028
  have hstable : (prefixWord ++ tailWord_136028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136028).length < 2 ^ (prefixWord ++ tailWord_136028).sum := by decide
  have hdescent : baseEnd_136028 < baseStart_136028 := by decide
  rcases family_descends (prefixWord ++ tailWord_136028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136049 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 3]
def baseStart_136049 : Nat := 118140960795 + 136049 * 2 ^ 59
def prefixEnd_136049 : Nat := 4983230072969 + 3 ^ 40 * 136049 * 2
def baseEnd_136049 : Nat := 62096470723238614543847

theorem tailTrace_136049 : CollatzResearch.WordTrace tailWord_136049 prefixEnd_136049 62096470723238614543847 := by
  unfold tailWord_136049
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962114684125183164451201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3308076456083455442967467 4962114684125183164451201)
  ·
    refine ⟨3721586013093887373338401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4962114684125183164451201 3721586013093887373338401)
    ·
      refine ⟨2791189509820415530003801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3721586013093887373338401 2791189509820415530003801)
      ·
        refine ⟨2093392132365311647502851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2791189509820415530003801 2093392132365311647502851)
        ·
          refine ⟨3140088198547967471254277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093392132365311647502851 3140088198547967471254277)
          ·
            refine ⟨588766537227743900860177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3140088198547967471254277 588766537227743900860177)
            ·
              refine ⟨441574902920807925645133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588766537227743900860177 441574902920807925645133)
              ·
                refine ⟨165590588595302972116925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441574902920807925645133 165590588595302972116925)
                ·
                  refine ⟨62096470723238614543847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165590588595302972116925 62096470723238614543847)
                  ·
                    rfl

theorem cell20_136049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_136049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136049 prefixEnd_136049 := by exact prefixLift 136049
  have htrace : WordTrace (prefixWord ++ tailWord_136049) baseStart_136049 baseEnd_136049 := by
    simpa [prefixWord, tailWord_136049, baseEnd_136049] using wordTrace_append hprefix tailTrace_136049
  have hstable : (prefixWord ++ tailWord_136049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136049).length < 2 ^ (prefixWord ++ tailWord_136049).sum := by decide
  have hdescent : baseEnd_136049 < baseStart_136049 := by decide
  rcases family_descends (prefixWord ++ tailWord_136049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136073 : List Nat := [1, 2, 1, 1, 5, 2, 1, 5, 2]
def baseStart_136073 : Nat := 118140960795 + 136073 * 2 ^ 59
def prefixEnd_136073 : Nat := 4983230072969 + 3 ^ 40 * 136073 * 2
def baseEnd_136073 : Nat := 62107424977201197743749

theorem tailTrace_136073 : CollatzResearch.WordTrace tailWord_136073 prefixEnd_136073 62107424977201197743749 := by
  unfold tailWord_136073
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962990036038235263324873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3308660024025490175549915 4962990036038235263324873)
  ·
    refine ⟨3722242527028676447493655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4962990036038235263324873 3722242527028676447493655)
    ·
      refine ⟨5583363790543014671240483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3722242527028676447493655 5583363790543014671240483)
      ·
        refine ⟨8375045685814522006860725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5583363790543014671240483 8375045685814522006860725)
        ·
          refine ⟨785160533045111438143193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8375045685814522006860725 785160533045111438143193)
          ·
            refine ⟨588870399783833578607395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 785160533045111438143193 588870399783833578607395)
            ·
              refine ⟨883305599675750367911093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588870399783833578607395 883305599675750367911093)
              ·
                refine ⟨82809899969601596991665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 883305599675750367911093 82809899969601596991665)
                ·
                  refine ⟨62107424977201197743749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82809899969601596991665 62107424977201197743749)
                  ·
                    rfl

theorem cell20_136073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_136073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136073 prefixEnd_136073 := by exact prefixLift 136073
  have htrace : WordTrace (prefixWord ++ tailWord_136073) baseStart_136073 baseEnd_136073 := by
    simpa [prefixWord, tailWord_136073, baseEnd_136073] using wordTrace_append hprefix tailTrace_136073
  have hstable : (prefixWord ++ tailWord_136073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136073).length < 2 ^ (prefixWord ++ tailWord_136073).sum := by decide
  have hdescent : baseEnd_136073 < baseStart_136073 := by decide
  rcases family_descends (prefixWord ++ tailWord_136073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136086 : List Nat := [5, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_136086 : Nat := 118140960795 + 136086 * 2 ^ 59
def prefixEnd_136086 : Nat := 4983230072969 + 3 ^ 40 * 136086 * 2
def baseEnd_136086 : Nat := 62113358531430930310363

theorem tailTrace_136086 : CollatzResearch.WordTrace tailWord_136086 prefixEnd_136086 62113358531430930310363 := by
  unfold tailWord_136086
  simp only [CollatzResearch.WordTrace]
  refine ⟨310216511561946155221757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3308976123327425655698741 310216511561946155221757)
  ·
    refine ⟨116331191835729808208159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 310216511561946155221757 116331191835729808208159)
    ·
      refine ⟨174496787753594712312239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116331191835729808208159 174496787753594712312239)
      ·
        refine ⟨261745181630392068468359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174496787753594712312239 261745181630392068468359)
        ·
          refine ⟨392617772445588102702539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261745181630392068468359 392617772445588102702539)
          ·
            refine ⟨588926658668382154053809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392617772445588102702539 588926658668382154053809)
            ·
              refine ⟨441694994001286615540357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588926658668382154053809 441694994001286615540357)
              ·
                refine ⟨82817811375241240413817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 441694994001286615540357 82817811375241240413817)
                ·
                  refine ⟨62113358531430930310363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82817811375241240413817 62113358531430930310363)
                  ·
                    rfl

theorem cell20_136086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_136086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136086 prefixEnd_136086 := by exact prefixLift 136086
  have htrace : WordTrace (prefixWord ++ tailWord_136086) baseStart_136086 baseEnd_136086 := by
    simpa [prefixWord, tailWord_136086, baseEnd_136086] using wordTrace_append hprefix tailTrace_136086
  have hstable : (prefixWord ++ tailWord_136086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136086).length < 2 ^ (prefixWord ++ tailWord_136086).sum := by decide
  have hdescent : baseEnd_136086 < baseStart_136086 := by decide
  rcases family_descends (prefixWord ++ tailWord_136086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136115 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_136115 : Nat := 118140960795 + 136115 * 2 ^ 59
def prefixEnd_136115 : Nat := 4983230072969 + 3 ^ 40 * 136115 * 2
def baseEnd_136115 : Nat := 62126594921635718343577

theorem tailTrace_136115 : CollatzResearch.WordTrace tailWord_136115 prefixEnd_136115 62126594921635718343577 := by
  unfold tailWord_136115
  simp only [CollatzResearch.WordTrace]
  refine ⟨4964521901886076436353799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3309681267924050957569199 4964521901886076436353799)
  ·
    refine ⟨7446782852829114654530699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4964521901886076436353799 7446782852829114654530699)
    ·
      refine ⟨11170174279243671981796049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7446782852829114654530699 11170174279243671981796049)
      ·
        refine ⟨8377630709432753986347037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11170174279243671981796049 8377630709432753986347037)
        ·
          refine ⟨3141611516037282744880139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8377630709432753986347037 3141611516037282744880139)
          ·
            refine ⟨4712417274055924117320209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141611516037282744880139 4712417274055924117320209)
            ·
              refine ⟨3534312955541943087990157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4712417274055924117320209 3534312955541943087990157)
              ·
                refine ⟨1325367358328228657996309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3534312955541943087990157 1325367358328228657996309)
                ·
                  refine ⟨62126594921635718343577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1325367358328228657996309 62126594921635718343577)
                  ·
                    rfl

theorem cell20_136115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_136115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136115 prefixEnd_136115 := by exact prefixLift 136115
  have htrace : WordTrace (prefixWord ++ tailWord_136115) baseStart_136115 baseEnd_136115 := by
    simpa [prefixWord, tailWord_136115, baseEnd_136115] using wordTrace_append hprefix tailTrace_136115
  have hstable : (prefixWord ++ tailWord_136115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136115).length < 2 ^ (prefixWord ++ tailWord_136115).sum := by decide
  have hdescent : baseEnd_136115 < baseStart_136115 := by decide
  rcases family_descends (prefixWord ++ tailWord_136115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136128 : List Nat := [2, 1, 1, 2, 3, 5, 1, 3, 2]
def baseStart_136128 : Nat := 118140960795 + 136128 * 2 ^ 59
def prefixEnd_136128 : Nat := 4983230072969 + 3 ^ 40 * 136128 * 2
def baseEnd_136128 : Nat := 62132528475865450910191

theorem tailTrace_136128 : CollatzResearch.WordTrace tailWord_136128 prefixEnd_136128 62132528475865450910191 := by
  unfold tailWord_136128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2482498025419489828288519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3309997367225986437718025 2482498025419489828288519)
  ·
    refine ⟨3723747038129234742432779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2482498025419489828288519 3723747038129234742432779)
    ·
      refine ⟨5585620557193852113649169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3723747038129234742432779 5585620557193852113649169)
      ·
        refine ⟨4189215417895389085236877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5585620557193852113649169 4189215417895389085236877)
        ·
          refine ⟨1570955781710770906963829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4189215417895389085236877 1570955781710770906963829)
          ·
            refine ⟨147277104535384772527859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1570955781710770906963829 147277104535384772527859)
            ·
              refine ⟨220915656803077158791789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147277104535384772527859 220915656803077158791789)
              ·
                refine ⟨82843371301153934546921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220915656803077158791789 82843371301153934546921)
                ·
                  refine ⟨62132528475865450910191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82843371301153934546921 62132528475865450910191)
                  ·
                    rfl

theorem cell20_136128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 2].length) (baseStart_136128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136128 prefixEnd_136128 := by exact prefixLift 136128
  have htrace : WordTrace (prefixWord ++ tailWord_136128) baseStart_136128 baseEnd_136128 := by
    simpa [prefixWord, tailWord_136128, baseEnd_136128] using wordTrace_append hprefix tailTrace_136128
  have hstable : (prefixWord ++ tailWord_136128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136128).length < 2 ^ (prefixWord ++ tailWord_136128).sum := by decide
  have hdescent : baseEnd_136128 < baseStart_136128 := by decide
  rcases family_descends (prefixWord ++ tailWord_136128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136139 : List Nat := [1, 1, 1, 1, 3, 7, 6]
def baseStart_136139 : Nat := 118140960795 + 136139 * 2 ^ 59
def prefixEnd_136139 : Nat := 4983230072969 + 3 ^ 40 * 136139 * 2
def baseEnd_136139 : Nat := 6904172130622033504831

theorem tailTrace_136139 : CollatzResearch.WordTrace tailWord_136139 prefixEnd_136139 6904172130622033504831 := by
  unfold tailWord_136139
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965397253799128535227471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3310264835866085690151647 4965397253799128535227471)
  ·
    refine ⟨7448095880698692802841207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4965397253799128535227471 7448095880698692802841207)
    ·
      refine ⟨11172143821048039204261811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7448095880698692802841207 11172143821048039204261811)
      ·
        refine ⟨16758215731572058806392717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11172143821048039204261811 16758215731572058806392717)
        ·
          refine ⟨6284330899339522052397269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16758215731572058806392717 6284330899339522052397269)
          ·
            refine ⟨147289005453270048103061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 6284330899339522052397269 147289005453270048103061)
            ·
              refine ⟨6904172130622033504831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147289005453270048103061 6904172130622033504831)
              ·
                rfl

theorem cell20_136139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 6].length) (baseStart_136139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136139 prefixEnd_136139 := by exact prefixLift 136139
  have htrace : WordTrace (prefixWord ++ tailWord_136139) baseStart_136139 baseEnd_136139 := by
    simpa [prefixWord, tailWord_136139, baseEnd_136139] using wordTrace_append hprefix tailTrace_136139
  have hstable : (prefixWord ++ tailWord_136139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136139).length < 2 ^ (prefixWord ++ tailWord_136139).sum := by decide
  have hdescent : baseEnd_136139 < baseStart_136139 := by decide
  rcases family_descends (prefixWord ++ tailWord_136139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136141 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 4]
def baseStart_136141 : Nat := 118140960795 + 136141 * 2 ^ 59
def prefixEnd_136141 : Nat := 4983230072969 + 3 ^ 40 * 136141 * 2
def baseEnd_136141 : Nat := 62138462030095183476805

theorem tailTrace_136141 : CollatzResearch.WordTrace tailWord_136141 prefixEnd_136141 62138462030095183476805 := by
  unfold tailWord_136141
  simp only [CollatzResearch.WordTrace]
  refine ⟨4965470199791882876800277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3310313466527921917866851 4965470199791882876800277)
  ·
    refine ⟨232756415615244509850013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4965470199791882876800277 232756415615244509850013)
    ·
      refine ⟨87283655855716691193755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232756415615244509850013 87283655855716691193755)
      ·
        refine ⟨130925483783575036790633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87283655855716691193755 130925483783575036790633)
        ·
          refine ⟨98194112837681277592975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130925483783575036790633 98194112837681277592975)
          ·
            refine ⟨147291169256521916389463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98194112837681277592975 147291169256521916389463)
            ·
              refine ⟨220936753884782874584195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147291169256521916389463 220936753884782874584195)
              ·
                refine ⟨331405130827174311876293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220936753884782874584195 331405130827174311876293)
                ·
                  refine ⟨62138462030095183476805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 331405130827174311876293 62138462030095183476805)
                  ·
                    rfl

theorem cell20_136141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_136141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136141 prefixEnd_136141 := by exact prefixLift 136141
  have htrace : WordTrace (prefixWord ++ tailWord_136141) baseStart_136141 baseEnd_136141 := by
    simpa [prefixWord, tailWord_136141, baseEnd_136141] using wordTrace_append hprefix tailTrace_136141
  have hstable : (prefixWord ++ tailWord_136141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136141).length < 2 ^ (prefixWord ++ tailWord_136141).sum := by decide
  have hdescent : baseEnd_136141 < baseStart_136141 := by decide
  rcases family_descends (prefixWord ++ tailWord_136141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136159 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 3]
def baseStart_136159 : Nat := 118140960795 + 136159 * 2 ^ 59
def prefixEnd_136159 : Nat := 4983230072969 + 3 ^ 40 * 136159 * 2
def baseEnd_136159 : Nat := 62146677720567120876731

theorem tailTrace_136159 : CollatzResearch.WordTrace tailWord_136159 prefixEnd_136159 62146677720567120876731 := by
  unfold tailWord_136159
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966126713726671950955531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3310751142484447967303687 4966126713726671950955531)
  ·
    refine ⟨7449190070590007926433297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4966126713726671950955531 7449190070590007926433297)
    ·
      refine ⟨5586892552942505944824973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7449190070590007926433297 5586892552942505944824973)
      ·
        refine ⟨2095084707353439729309365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5586892552942505944824973 2095084707353439729309365)
        ·
          refine ⟨196414191314384974622753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2095084707353439729309365 196414191314384974622753)
          ·
            refine ⟨147310643485788730967065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196414191314384974622753 147310643485788730967065)
            ·
              refine ⟨110482982614341548225299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147310643485788730967065 110482982614341548225299)
              ·
                refine ⟨165724473921512322337949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110482982614341548225299 165724473921512322337949)
                ·
                  refine ⟨62146677720567120876731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165724473921512322337949 62146677720567120876731)
                  ·
                    rfl

theorem cell20_136159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 3].length) (baseStart_136159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136159 prefixEnd_136159 := by exact prefixLift 136159
  have htrace : WordTrace (prefixWord ++ tailWord_136159) baseStart_136159 baseEnd_136159 := by
    simpa [prefixWord, tailWord_136159, baseEnd_136159] using wordTrace_append hprefix tailTrace_136159
  have hstable : (prefixWord ++ tailWord_136159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136159).length < 2 ^ (prefixWord ++ tailWord_136159).sum := by decide
  have hdescent : baseEnd_136159 < baseStart_136159 := by decide
  rcases family_descends (prefixWord ++ tailWord_136159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136163 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 3]
def baseStart_136163 : Nat := 118140960795 + 136163 * 2 ^ 59
def prefixEnd_136163 : Nat := 4983230072969 + 3 ^ 40 * 136163 * 2
def baseEnd_136163 : Nat := 62148503429560884743381

theorem tailTrace_136163 : CollatzResearch.WordTrace tailWord_136163 prefixEnd_136163 62148503429560884743381 := by
  unfold tailWord_136163
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966272605712180634101143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3310848403808120422734095 4966272605712180634101143)
  ·
    refine ⟨7449408908568270951151715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4966272605712180634101143 7449408908568270951151715)
    ·
      refine ⟨11174113362852406426727573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7449408908568270951151715 11174113362852406426727573)
      ·
        refine ⟨523786563883706551252855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11174113362852406426727573 523786563883706551252855)
        ·
          refine ⟨785679845825559826879283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523786563883706551252855 785679845825559826879283)
          ·
            refine ⟨1178519768738339740318925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785679845825559826879283 1178519768738339740318925)
            ·
              refine ⟨441944913276877402619597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1178519768738339740318925 441944913276877402619597)
              ·
                refine ⟨165729342478829025982349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441944913276877402619597 165729342478829025982349)
                ·
                  refine ⟨62148503429560884743381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165729342478829025982349 62148503429560884743381)
                  ·
                    rfl

theorem cell20_136163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_136163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136163 prefixEnd_136163 := by exact prefixLift 136163
  have htrace : WordTrace (prefixWord ++ tailWord_136163) baseStart_136163 baseEnd_136163 := by
    simpa [prefixWord, tailWord_136163, baseEnd_136163] using wordTrace_append hprefix tailTrace_136163
  have hstable : (prefixWord ++ tailWord_136163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136163).length < 2 ^ (prefixWord ++ tailWord_136163).sum := by decide
  have hdescent : baseEnd_136163 < baseStart_136163 := by decide
  rcases family_descends (prefixWord ++ tailWord_136163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136177 : List Nat := [1, 2, 2, 2, 4, 1, 2, 6]
def baseStart_136177 : Nat := 118140960795 + 136177 * 2 ^ 59
def prefixEnd_136177 : Nat := 4983230072969 + 3 ^ 40 * 136177 * 2
def baseEnd_136177 : Nat := 20718297803679686092219

theorem tailTrace_136177 : CollatzResearch.WordTrace tailWord_136177 prefixEnd_136177 20718297803679686092219 := by
  unfold tailWord_136177
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966783227661461025110785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3311188818440974016740523 4966783227661461025110785)
  ·
    refine ⟨3725087420746095768833089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4966783227661461025110785 3725087420746095768833089)
    ·
      refine ⟨2793815565559571826624817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3725087420746095768833089 2793815565559571826624817)
      ·
        refine ⟨2095361674169678869968613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2793815565559571826624817 2095361674169678869968613)
        ·
          refine ⟨392880313906814788119115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2095361674169678869968613 392880313906814788119115)
          ·
            refine ⟨589320470860222182178673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392880313906814788119115 589320470860222182178673)
            ·
              refine ⟨441990353145166636634005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589320470860222182178673 441990353145166636634005)
              ·
                refine ⟨20718297803679686092219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 441990353145166636634005 20718297803679686092219)
                ·
                  rfl

theorem cell20_136177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_136177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136177 prefixEnd_136177 := by exact prefixLift 136177
  have htrace : WordTrace (prefixWord ++ tailWord_136177) baseStart_136177 baseEnd_136177 := by
    simpa [prefixWord, tailWord_136177, baseEnd_136177] using wordTrace_append hprefix tailTrace_136177
  have hstable : (prefixWord ++ tailWord_136177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136177).length < 2 ^ (prefixWord ++ tailWord_136177).sum := by decide
  have hdescent : baseEnd_136177 < baseStart_136177 := by decide
  rcases family_descends (prefixWord ++ tailWord_136177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136194 : List Nat := [3, 4, 1, 3, 9]
def baseStart_136194 : Nat := 118140960795 + 136194 * 2 ^ 59
def prefixEnd_136194 : Nat := 4983230072969 + 3 ^ 40 * 136194 * 2
def baseEnd_136194 : Nat := 767440156472377218641

theorem tailTrace_136194 : CollatzResearch.WordTrace tailWord_136194 prefixEnd_136194 767440156472377218641 := by
  unfold tailWord_136194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241850817149968232119909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3311602179066581952319757 1241850817149968232119909)
  ·
    refine ⟨232847028215619043522483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1241850817149968232119909 232847028215619043522483)
    ·
      refine ⟨349270542323428565283725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232847028215619043522483 349270542323428565283725)
      ·
        refine ⟨130976453371285711981397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 349270542323428565283725 130976453371285711981397)
        ·
          refine ⟨767440156472377218641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 130976453371285711981397 767440156472377218641)
          ·
            rfl

theorem cell20_136194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 9].length) (baseStart_136194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136194 prefixEnd_136194 := by exact prefixLift 136194
  have htrace : WordTrace (prefixWord ++ tailWord_136194) baseStart_136194 baseEnd_136194 := by
    simpa [prefixWord, tailWord_136194, baseEnd_136194] using wordTrace_append hprefix tailTrace_136194
  have hstable : (prefixWord ++ tailWord_136194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136194).length < 2 ^ (prefixWord ++ tailWord_136194).sum := by decide
  have hdescent : baseEnd_136194 < baseStart_136194 := by decide
  rcases family_descends (prefixWord ++ tailWord_136194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136204 : List Nat := [2, 2, 1, 2, 3, 2, 4, 2, 2]
def baseStart_136204 : Nat := 118140960795 + 136204 * 2 ^ 59
def prefixEnd_136204 : Nat := 4983230072969 + 3 ^ 40 * 136204 * 2
def baseEnd_136204 : Nat := 62167216946746964376547

theorem tailTrace_136204 : CollatzResearch.WordTrace tailWord_136204 prefixEnd_136204 62167216946746964376547 := by
  unfold tailWord_136204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2483883999281822318171833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3311845332375763090895777 2483883999281822318171833)
  ·
    refine ⟨1862912999461366738628875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2483883999281822318171833 1862912999461366738628875)
    ·
      refine ⟨2794369499192050107943313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1862912999461366738628875 2794369499192050107943313)
      ·
        refine ⟨2095777124394037580957485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2794369499192050107943313 2095777124394037580957485)
        ·
          refine ⟨785916421647764092859057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2095777124394037580957485 785916421647764092859057)
          ·
            refine ⟨589437316235823069644293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 785916421647764092859057 589437316235823069644293)
            ·
              refine ⟨110519496794216825558305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 589437316235823069644293 110519496794216825558305)
              ·
                refine ⟨82889622595662619168729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110519496794216825558305 82889622595662619168729)
                ·
                  refine ⟨62167216946746964376547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82889622595662619168729 62167216946746964376547)
                  ·
                    rfl

theorem cell20_136204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_136204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136204 prefixEnd_136204 := by exact prefixLift 136204
  have htrace : WordTrace (prefixWord ++ tailWord_136204) baseStart_136204 baseEnd_136204 := by
    simpa [prefixWord, tailWord_136204, baseEnd_136204] using wordTrace_append hprefix tailTrace_136204
  have hstable : (prefixWord ++ tailWord_136204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136204).length < 2 ^ (prefixWord ++ tailWord_136204).sum := by decide
  have hdescent : baseEnd_136204 < baseStart_136204 := by decide
  rcases family_descends (prefixWord ++ tailWord_136204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136253 : List Nat := [1, 4, 1, 3, 1, 3, 7]
def baseStart_136253 : Nat := 118140960795 + 136253 * 2 ^ 59
def prefixEnd_136253 : Nat := 4983230072969 + 3 ^ 40 * 136253 * 2
def baseEnd_136253 : Nat := 6909953542435619082557

theorem tailTrace_136253 : CollatzResearch.WordTrace tailWord_136253 prefixEnd_136253 6909953542435619082557 := by
  unfold tailWord_136253
  simp only [CollatzResearch.WordTrace]
  refine ⟨4969555175386126004877413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3313036783590750669918275 4969555175386126004877413)
  ·
    refine ⟨931791595384898625914515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4969555175386126004877413 931791595384898625914515)
    ·
      refine ⟨1397687393077347938871773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 931791595384898625914515 1397687393077347938871773)
      ·
        refine ⟨524132772404005477076915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1397687393077347938871773 524132772404005477076915)
        ·
          refine ⟨786199158606008215615373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524132772404005477076915 786199158606008215615373)
          ·
            refine ⟨294824684477253080855765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 786199158606008215615373 294824684477253080855765)
            ·
              refine ⟨6909953542435619082557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 294824684477253080855765 6909953542435619082557)
              ·
                rfl

theorem cell20_136253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 7].length) (baseStart_136253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136253 prefixEnd_136253 := by exact prefixLift 136253
  have htrace : WordTrace (prefixWord ++ tailWord_136253) baseStart_136253 baseEnd_136253 := by
    simpa [prefixWord, tailWord_136253, baseEnd_136253] using wordTrace_append hprefix tailTrace_136253
  have hstable : (prefixWord ++ tailWord_136253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136253).length < 2 ^ (prefixWord ++ tailWord_136253).sum := by decide
  have hdescent : baseEnd_136253 < baseStart_136253 := by decide
  rcases family_descends (prefixWord ++ tailWord_136253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136263 : List Nat := [1, 1, 4, 1, 3, 2, 2, 4, 2]
def baseStart_136263 : Nat := 118140960795 + 136263 * 2 ^ 59
def prefixEnd_136263 : Nat := 4983230072969 + 3 ^ 40 * 136263 * 2
def baseEnd_136263 : Nat := 62194146154404981409639

theorem tailTrace_136263 : CollatzResearch.WordTrace tailWord_136263 prefixEnd_136263 62194146154404981409639 := by
  unfold tailWord_136263
  simp only [CollatzResearch.WordTrace]
  refine ⟨4969919905349897712741443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3313279936899931808494295 4969919905349897712741443)
  ·
    refine ⟨7454879858024846569112165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4969919905349897712741443 7454879858024846569112165)
    ·
      refine ⟨1397789973379658731708531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7454879858024846569112165 1397789973379658731708531)
      ·
        refine ⟨2096684960069488097562797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1397789973379658731708531 2096684960069488097562797)
        ·
          refine ⟨786256860026058036586049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2096684960069488097562797 786256860026058036586049)
          ·
            refine ⟨589692645019543527439537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786256860026058036586049 589692645019543527439537)
            ·
              refine ⟨442269483764657645579653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589692645019543527439537 442269483764657645579653)
              ·
                refine ⟨82925528205873308546185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442269483764657645579653 82925528205873308546185)
                ·
                  refine ⟨62194146154404981409639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82925528205873308546185 62194146154404981409639)
                  ·
                    rfl

theorem cell20_136263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 2].length) (baseStart_136263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136263 prefixEnd_136263 := by exact prefixLift 136263
  have htrace : WordTrace (prefixWord ++ tailWord_136263) baseStart_136263 baseEnd_136263 := by
    simpa [prefixWord, tailWord_136263, baseEnd_136263] using wordTrace_append hprefix tailTrace_136263
  have hstable : (prefixWord ++ tailWord_136263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136263).length < 2 ^ (prefixWord ++ tailWord_136263).sum := by decide
  have hdescent : baseEnd_136263 < baseStart_136263 := by decide
  rcases family_descends (prefixWord ++ tailWord_136263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136284 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_136284 : Nat := 118140960795 + 136284 * 2 ^ 59
def prefixEnd_136284 : Nat := 4983230072969 + 3 ^ 40 * 136284 * 2
def baseEnd_136284 : Nat := 62203731126622241709553

theorem tailTrace_136284 : CollatzResearch.WordTrace tailWord_136284 prefixEnd_136284 62203731126622241709553 := by
  unfold tailWord_136284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485342919136909149627953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3313790558849212199503937 2485342919136909149627953)
  ·
    refine ⟨1864007189352681862220965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2485342919136909149627953 1864007189352681862220965)
    ·
      refine ⟨349501348003627849166431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1864007189352681862220965 349501348003627849166431)
      ·
        refine ⟨524252022005441773749647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349501348003627849166431 524252022005441773749647)
        ·
          refine ⟨786378033008162660624471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524252022005441773749647 786378033008162660624471)
          ·
            refine ⟨1179567049512243990936707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786378033008162660624471 1179567049512243990936707)
            ·
              refine ⟨1769350574268365986405061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179567049512243990936707 1769350574268365986405061)
              ·
                refine ⟨331753232675318622450949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1769350574268365986405061 331753232675318622450949)
                ·
                  refine ⟨62203731126622241709553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 331753232675318622450949 62203731126622241709553)
                  ·
                    rfl

theorem cell20_136284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_136284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136284 prefixEnd_136284 := by exact prefixLift 136284
  have htrace : WordTrace (prefixWord ++ tailWord_136284) baseStart_136284 baseEnd_136284 := by
    simpa [prefixWord, tailWord_136284, baseEnd_136284] using wordTrace_append hprefix tailTrace_136284
  have hstable : (prefixWord ++ tailWord_136284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136284).length < 2 ^ (prefixWord ++ tailWord_136284).sum := by decide
  have hdescent : baseEnd_136284 < baseStart_136284 := by decide
  rcases family_descends (prefixWord ++ tailWord_136284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136312 : List Nat := [2, 1, 2, 1, 1, 1, 12]
def baseStart_136312 : Nat := 118140960795 + 136312 * 2 ^ 59
def prefixEnd_136312 : Nat := 4983230072969 + 3 ^ 40 * 136312 * 2
def baseEnd_136312 : Nat := 6912945676619843197345

theorem tailTrace_136312 : CollatzResearch.WordTrace tailWord_136312 prefixEnd_136312 6912945676619843197345 := by
  unfold tailWord_136312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485853541086189540637595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3314471388114919387516793 2485853541086189540637595)
  ·
    refine ⟨3728780311629284310956393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2485853541086189540637595 3728780311629284310956393)
    ·
      refine ⟨2796585233721963233217295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3728780311629284310956393 2796585233721963233217295)
      ·
        refine ⟨4194877850582944849825943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2796585233721963233217295 4194877850582944849825943)
        ·
          refine ⟨6292316775874417274738915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4194877850582944849825943 6292316775874417274738915)
          ·
            refine ⟨9438475163811625912108373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6292316775874417274738915 9438475163811625912108373)
            ·
              refine ⟨6912945676619843197345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 9438475163811625912108373 6912945676619843197345)
              ·
                rfl

theorem cell20_136312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 12].length) (baseStart_136312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136312 prefixEnd_136312 := by exact prefixLift 136312
  have htrace : WordTrace (prefixWord ++ tailWord_136312) baseStart_136312 baseEnd_136312 := by
    simpa [prefixWord, tailWord_136312, baseEnd_136312] using wordTrace_append hprefix tailTrace_136312
  have hstable : (prefixWord ++ tailWord_136312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136312).length < 2 ^ (prefixWord ++ tailWord_136312).sum := by decide
  have hdescent : baseEnd_136312 < baseStart_136312 := by decide
  rcases family_descends (prefixWord ++ tailWord_136312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136328 : List Nat := [2, 1, 3, 4, 3, 1, 2, 1, 3]
def baseStart_136328 : Nat := 118140960795 + 136328 * 2 ^ 59
def prefixEnd_136328 : Nat := 4983230072969 + 3 ^ 40 * 136328 * 2
def baseEnd_136328 : Nat := 62223813925553644242707

theorem tailTrace_136328 : CollatzResearch.WordTrace tailWord_136328 prefixEnd_136328 62223813925553644242707 := by
  unfold tailWord_136328
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486145325057206906928819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3314860433409609209238425 2486145325057206906928819)
  ·
    refine ⟨3729217987585810360393229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2486145325057206906928819 3729217987585810360393229)
    ·
      refine ⟨1398456745344678885147461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3729217987585810360393229 1398456745344678885147461)
      ·
        refine ⟨262210639752127290965149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1398456745344678885147461 262210639752127290965149)
        ·
          refine ⟨98328989907047734111931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262210639752127290965149 98328989907047734111931)
          ·
            refine ⟨147493484860571601167897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98328989907047734111931 147493484860571601167897)
            ·
              refine ⟨110620113645428700875923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147493484860571601167897 110620113645428700875923)
              ·
                refine ⟨165930170468143051313885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110620113645428700875923 165930170468143051313885)
                ·
                  refine ⟨62223813925553644242707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165930170468143051313885 62223813925553644242707)
                  ·
                    rfl

theorem cell20_136328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_136328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136328 prefixEnd_136328 := by exact prefixLift 136328
  have htrace : WordTrace (prefixWord ++ tailWord_136328) baseStart_136328 baseEnd_136328 := by
    simpa [prefixWord, tailWord_136328, baseEnd_136328] using wordTrace_append hprefix tailTrace_136328
  have hstable : (prefixWord ++ tailWord_136328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136328).length < 2 ^ (prefixWord ++ tailWord_136328).sum := by decide
  have hdescent : baseEnd_136328 < baseStart_136328 := by decide
  rcases family_descends (prefixWord ++ tailWord_136328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136329 : List Nat := [1, 2, 1, 1, 4, 4, 2, 5]
def baseStart_136329 : Nat := 118140960795 + 136329 * 2 ^ 59
def prefixEnd_136329 : Nat := 4983230072969 + 3 ^ 40 * 136329 * 2
def baseEnd_136329 : Nat := 20741423450934028403123

theorem tailTrace_136329 : CollatzResearch.WordTrace tailWord_136329 prefixEnd_136329 20741423450934028403123 := by
  unfold tailWord_136329
  simp only [CollatzResearch.WordTrace]
  refine ⟨4972327123110790984644041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3314884748740527323096027 4972327123110790984644041)
  ·
    refine ⟨3729245342333093238483031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4972327123110790984644041 3729245342333093238483031)
    ·
      refine ⟨5593868013499639857724547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3729245342333093238483031 5593868013499639857724547)
      ·
        refine ⟨8390802020249459786586821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5593868013499639857724547 8390802020249459786586821)
        ·
          refine ⟨1573275378796773709985029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8390802020249459786586821 1573275378796773709985029)
          ·
            refine ⟨294989133524395070622193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1573275378796773709985029 294989133524395070622193)
            ·
              refine ⟨221241850143296302966645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294989133524395070622193 221241850143296302966645)
              ·
                refine ⟨20741423450934028403123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221241850143296302966645 20741423450934028403123)
                ·
                  rfl

theorem cell20_136329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 5].length) (baseStart_136329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136329 prefixEnd_136329 := by exact prefixLift 136329
  have htrace : WordTrace (prefixWord ++ tailWord_136329) baseStart_136329 baseEnd_136329 := by
    simpa [prefixWord, tailWord_136329, baseEnd_136329] using wordTrace_append hprefix tailTrace_136329
  have hstable : (prefixWord ++ tailWord_136329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136329).length < 2 ^ (prefixWord ++ tailWord_136329).sum := by decide
  have hdescent : baseEnd_136329 < baseStart_136329 := by decide
  rcases family_descends (prefixWord ++ tailWord_136329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136377 : List Nat := [1, 2, 1, 4, 1, 4, 1, 4, 2]
def baseStart_136377 : Nat := 118140960795 + 136377 * 2 ^ 59
def prefixEnd_136377 : Nat := 4983230072969 + 3 ^ 40 * 136377 * 2
def baseEnd_136377 : Nat := 62246178860727251609173

theorem tailTrace_136377 : CollatzResearch.WordTrace tailWord_136377 prefixEnd_136377 62246178860727251609173 := by
  unfold tailWord_136377
  simp only [CollatzResearch.WordTrace]
  refine ⟨4974077826936895182391385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3316051884624596788260923 4974077826936895182391385)
  ·
    refine ⟨3730558370202671386793539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4974077826936895182391385 3730558370202671386793539)
    ·
      refine ⟨5595837555304007080190309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3730558370202671386793539 5595837555304007080190309)
      ·
        refine ⟨1049219541619501327535683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5595837555304007080190309 1049219541619501327535683)
        ·
          refine ⟨1573829312429251991303525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049219541619501327535683 1573829312429251991303525)
          ·
            refine ⟨295092996080484748369411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1573829312429251991303525 295092996080484748369411)
            ·
              refine ⟨442639494120727122554117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295092996080484748369411 442639494120727122554117)
              ·
                refine ⟨82994905147636335478897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442639494120727122554117 82994905147636335478897)
                ·
                  refine ⟨62246178860727251609173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82994905147636335478897 62246178860727251609173)
                  ·
                    rfl

theorem cell20_136377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_136377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136377 prefixEnd_136377 := by exact prefixLift 136377
  have htrace : WordTrace (prefixWord ++ tailWord_136377) baseStart_136377 baseEnd_136377 := by
    simpa [prefixWord, tailWord_136377, baseEnd_136377] using wordTrace_append hprefix tailTrace_136377
  have hstable : (prefixWord ++ tailWord_136377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136377).length < 2 ^ (prefixWord ++ tailWord_136377).sum := by decide
  have hdescent : baseEnd_136377 < baseStart_136377 := by decide
  rcases family_descends (prefixWord ++ tailWord_136377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136384 : List Nat := [2, 1, 1, 2, 6, 2, 1, 5]
def baseStart_136384 : Nat := 118140960795 + 136384 * 2 ^ 59
def prefixEnd_136384 : Nat := 4983230072969 + 3 ^ 40 * 136384 * 2
def baseEnd_136384 : Nat := 20749791283822112791937

theorem tailTrace_136384 : CollatzResearch.WordTrace tailWord_136384 prefixEnd_136384 20749791283822112791937 := by
  unfold tailWord_136384
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487166568955767688948103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3316222091941023585264137 2487166568955767688948103)
  ·
    refine ⟨3730749853433651533422155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2487166568955767688948103 3730749853433651533422155)
    ·
      refine ⟨5596124780150477300133233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3730749853433651533422155 5596124780150477300133233)
      ·
        refine ⟨4197093585112857975099925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5596124780150477300133233 4197093585112857975099925)
        ·
          refine ⟨196738761802165217582809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4197093585112857975099925 196738761802165217582809)
          ·
            refine ⟨147554071351623913187107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196738761802165217582809 147554071351623913187107)
            ·
              refine ⟨221331107027435869780661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147554071351623913187107 221331107027435869780661)
              ·
                refine ⟨20749791283822112791937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221331107027435869780661 20749791283822112791937)
                ·
                  rfl

theorem cell20_136384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_136384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136384 prefixEnd_136384 := by exact prefixLift 136384
  have htrace : WordTrace (prefixWord ++ tailWord_136384) baseStart_136384 baseEnd_136384 := by
    simpa [prefixWord, tailWord_136384, baseEnd_136384] using wordTrace_append hprefix tailTrace_136384
  have hstable : (prefixWord ++ tailWord_136384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136384).length < 2 ^ (prefixWord ++ tailWord_136384).sum := by decide
  have hdescent : baseEnd_136384 < baseStart_136384 := by decide
  rcases family_descends (prefixWord ++ tailWord_136384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136429 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_136429 : Nat := 118140960795 + 136429 * 2 ^ 59
def prefixEnd_136429 : Nat := 4983230072969 + 3 ^ 40 * 136429 * 2
def baseEnd_136429 : Nat := 62269913077646181875627

theorem tailTrace_136429 : CollatzResearch.WordTrace tailWord_136429 prefixEnd_136429 62269913077646181875627 := by
  unfold tailWord_136429
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975974422748508063284341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3317316281832338708856227 4975974422748508063284341)
  ·
    refine ⟨466497602132672630932907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4975974422748508063284341 466497602132672630932907)
    ·
      refine ⟨699746403199008946399361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466497602132672630932907 699746403199008946399361)
      ·
        refine ⟨524809802399256709799521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 699746403199008946399361 524809802399256709799521)
        ·
          refine ⟨393607351799442532349641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524809802399256709799521 393607351799442532349641)
          ·
            refine ⟨295205513849581899262231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393607351799442532349641 295205513849581899262231)
            ·
              refine ⟨442808270774372848893347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295205513849581899262231 442808270774372848893347)
              ·
                refine ⟨664212406161559273340021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442808270774372848893347 664212406161559273340021)
                ·
                  refine ⟨62269913077646181875627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 664212406161559273340021 62269913077646181875627)
                  ·
                    rfl

theorem cell20_136429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_136429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136429 prefixEnd_136429 := by exact prefixLift 136429
  have htrace : WordTrace (prefixWord ++ tailWord_136429) baseStart_136429 baseEnd_136429 := by
    simpa [prefixWord, tailWord_136429, baseEnd_136429] using wordTrace_append hprefix tailTrace_136429
  have hstable : (prefixWord ++ tailWord_136429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136429).length < 2 ^ (prefixWord ++ tailWord_136429).sum := by decide
  have hdescent : baseEnd_136429 < baseStart_136429 := by decide
  rcases family_descends (prefixWord ++ tailWord_136429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136457 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_136457 : Nat := 118140960795 + 136457 * 2 ^ 59
def prefixEnd_136457 : Nat := 4983230072969 + 3 ^ 40 * 136457 * 2
def baseEnd_136457 : Nat := 62282693040602528942179

theorem tailTrace_136457 : CollatzResearch.WordTrace tailWord_136457 prefixEnd_136457 62282693040602528942179 := by
  unfold tailWord_136457
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976995666647068845303625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3317997111098045896869083 4976995666647068845303625)
  ·
    refine ⟨3732746749985301633977719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4976995666647068845303625 3732746749985301633977719)
    ·
      refine ⟨5599120124977952450966579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3732746749985301633977719 5599120124977952450966579)
      ·
        refine ⟨8398680187466928676449869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5599120124977952450966579 8398680187466928676449869)
        ·
          refine ⟨3149505070300098253668701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8398680187466928676449869 3149505070300098253668701)
          ·
            refine ⟨1181064401362536845125763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3149505070300098253668701 1181064401362536845125763)
            ·
              refine ⟨1771596602043805267688645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181064401362536845125763 1771596602043805267688645)
              ·
                refine ⟨332174362883213487691621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1771596602043805267688645 332174362883213487691621)
                ·
                  refine ⟨62282693040602528942179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332174362883213487691621 62282693040602528942179)
                  ·
                    rfl

theorem cell20_136457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_136457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136457 prefixEnd_136457 := by exact prefixLift 136457
  have htrace : WordTrace (prefixWord ++ tailWord_136457) baseStart_136457 baseEnd_136457 := by
    simpa [prefixWord, tailWord_136457, baseEnd_136457] using wordTrace_append hprefix tailTrace_136457
  have hstable : (prefixWord ++ tailWord_136457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136457).length < 2 ^ (prefixWord ++ tailWord_136457).sum := by decide
  have hdescent : baseEnd_136457 < baseStart_136457 := by decide
  rcases family_descends (prefixWord ++ tailWord_136457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136460 : List Nat := [2, 2, 1, 2, 2, 5, 2, 4]
def baseStart_136460 : Nat := 118140960795 + 136460 * 2 ^ 59
def prefixEnd_136460 : Nat := 4983230072969 + 3 ^ 40 * 136460 * 2
def baseEnd_136460 : Nat := 20761354107449283947389

theorem tailTrace_136460 : CollatzResearch.WordTrace tailWord_136460 prefixEnd_136460 20761354107449283947389 := by
  unfold tailWord_136460
  simp only [CollatzResearch.WordTrace]
  refine ⟨2488552542818100178831417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3318070057090800238441889 2488552542818100178831417)
  ·
    refine ⟨1866414407113575134123563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2488552542818100178831417 1866414407113575134123563)
    ·
      refine ⟨2799621610670362701185345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866414407113575134123563 2799621610670362701185345)
      ·
        refine ⟨2099716208002772025889009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2799621610670362701185345 2099716208002772025889009)
        ·
          refine ⟨1574787156002079019416757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2099716208002772025889009 1574787156002079019416757)
          ·
            refine ⟨147636295875194908070321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1574787156002079019416757 147636295875194908070321)
            ·
              refine ⟨110727221906396181052741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147636295875194908070321 110727221906396181052741)
              ·
                refine ⟨20761354107449283947389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110727221906396181052741 20761354107449283947389)
                ·
                  rfl

theorem cell20_136460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_136460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136460 prefixEnd_136460 := by exact prefixLift 136460
  have htrace : WordTrace (prefixWord ++ tailWord_136460) baseStart_136460 baseEnd_136460 := by
    simpa [prefixWord, tailWord_136460, baseEnd_136460] using wordTrace_append hprefix tailTrace_136460
  have hstable : (prefixWord ++ tailWord_136460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136460).length < 2 ^ (prefixWord ++ tailWord_136460).sum := by decide
  have hdescent : baseEnd_136460 < baseStart_136460 := by decide
  rcases family_descends (prefixWord ++ tailWord_136460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136466 : List Nat := [3, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_136466 : Nat := 118140960795 + 136466 * 2 ^ 59
def prefixEnd_136466 : Nat := 4983230072969 + 3 ^ 40 * 136466 * 2
def baseEnd_136466 : Nat := 62286800885838497642143

theorem tailTrace_136466 : CollatzResearch.WordTrace tailWord_136466 prefixEnd_136466 62286800885838497642143 := by
  unfold tailWord_136466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1244330980903615845595313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3318215949076308921587501 1244330980903615845595313)
  ·
    refine ⟨933248235677711884196485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1244330980903615845595313 933248235677711884196485)
    ·
      refine ⟨174984044189570978286841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 933248235677711884196485 174984044189570978286841)
      ·
        refine ⟨131238033142178233715131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174984044189570978286841 131238033142178233715131)
        ·
          refine ⟨196857049713267350572697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131238033142178233715131 196857049713267350572697)
          ·
            refine ⟨147642787284950512929523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196857049713267350572697 147642787284950512929523)
            ·
              refine ⟨221464180927425769394285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147642787284950512929523 221464180927425769394285)
              ·
                refine ⟨83049067847784663522857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221464180927425769394285 83049067847784663522857)
                ·
                  refine ⟨62286800885838497642143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83049067847784663522857 62286800885838497642143)
                  ·
                    rfl

theorem cell20_136466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_136466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136466 prefixEnd_136466 := by exact prefixLift 136466
  have htrace : WordTrace (prefixWord ++ tailWord_136466) baseStart_136466 baseEnd_136466 := by
    simpa [prefixWord, tailWord_136466, baseEnd_136466] using wordTrace_append hprefix tailTrace_136466
  have hstable : (prefixWord ++ tailWord_136466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136466).length < 2 ^ (prefixWord ++ tailWord_136466).sum := by decide
  have hdescent : baseEnd_136466 < baseStart_136466 := by decide
  rcases family_descends (prefixWord ++ tailWord_136466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136540 : List Nat := [2, 2, 4, 12]
def baseStart_136540 : Nat := 118140960795 + 136540 * 2 ^ 59
def prefixEnd_136540 : Nat := 4983230072969 + 3 ^ 40 * 136540 * 2
def baseEnd_136540 : Nat := 256463277786926457511

theorem tailTrace_136540 : CollatzResearch.WordTrace tailWord_136540 prefixEnd_136540 256463277786926457511 := by
  unfold tailWord_136540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490011462673187010287537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3320015283564249347050049 2490011462673187010287537)
  ·
    refine ⟨1867508597004890257715653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2490011462673187010287537 1867508597004890257715653)
    ·
      refine ⟨350157861938416923321685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1867508597004890257715653 350157861938416923321685)
      ·
        refine ⟨256463277786926457511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 350157861938416923321685 256463277786926457511)
        ·
          rfl

theorem cell20_136540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 12].length) (baseStart_136540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136540 prefixEnd_136540 := by exact prefixLift 136540
  have htrace : WordTrace (prefixWord ++ tailWord_136540) baseStart_136540 baseEnd_136540 := by
    simpa [prefixWord, tailWord_136540, baseEnd_136540] using wordTrace_append hprefix tailTrace_136540
  have hstable : (prefixWord ++ tailWord_136540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136540).length < 2 ^ (prefixWord ++ tailWord_136540).sum := by decide
  have hdescent : baseEnd_136540 < baseStart_136540 := by decide
  rcases family_descends (prefixWord ++ tailWord_136540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136557 : List Nat := [1, 5, 1, 1, 1, 3, 3, 5]
def baseStart_136557 : Nat := 118140960795 + 136557 * 2 ^ 59
def prefixEnd_136557 : Nat := 4983230072969 + 3 ^ 40 * 136557 * 2
def baseEnd_136557 : Nat := 20776111921815541869479

theorem tailTrace_136557 : CollatzResearch.WordTrace tailWord_136557 prefixEnd_136557 20776111921815541869479 := by
  unfold tailWord_136557
  simp only [CollatzResearch.WordTrace]
  refine ⟨4980642966284785923943925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3320428644189857282629283 4980642966284785923943925)
  ·
    refine ⟨466935278089198680369743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4980642966284785923943925 466935278089198680369743)
    ·
      refine ⟨700402917133798020554615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466935278089198680369743 700402917133798020554615)
      ·
        refine ⟨1050604375700697030831923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700402917133798020554615 1050604375700697030831923)
        ·
          refine ⟨1575906563551045546247885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050604375700697030831923 1575906563551045546247885)
          ·
            refine ⟨590964961331642079842957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1575906563551045546247885 590964961331642079842957)
            ·
              refine ⟨221611860499365779941109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 590964961331642079842957 221611860499365779941109)
              ·
                refine ⟨20776111921815541869479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221611860499365779941109 20776111921815541869479)
                ·
                  rfl

theorem cell20_136557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_136557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136557 prefixEnd_136557 := by exact prefixLift 136557
  have htrace : WordTrace (prefixWord ++ tailWord_136557) baseStart_136557 baseEnd_136557 := by
    simpa [prefixWord, tailWord_136557, baseEnd_136557] using wordTrace_append hprefix tailTrace_136557
  have hstable : (prefixWord ++ tailWord_136557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136557).length < 2 ^ (prefixWord ++ tailWord_136557).sum := by decide
  have hdescent : baseEnd_136557 < baseStart_136557 := by decide
  rcases family_descends (prefixWord ++ tailWord_136557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136571 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_136571 : Nat := 118140960795 + 136571 * 2 ^ 59
def prefixEnd_136571 : Nat := 4983230072969 + 3 ^ 40 * 136571 * 2
def baseEnd_136571 : Nat := 62334725746924799141713

theorem tailTrace_136571 : CollatzResearch.WordTrace tailWord_136571 prefixEnd_136571 62334725746924799141713 := by
  unfold tailWord_136571
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981153588234066314953567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3320769058822710876635711 4981153588234066314953567)
  ·
    refine ⟨7471730382351099472430351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4981153588234066314953567 7471730382351099472430351)
    ·
      refine ⟨11207595573526649208645527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7471730382351099472430351 11207595573526649208645527)
      ·
        refine ⟨16811393360289973812968291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11207595573526649208645527 16811393360289973812968291)
        ·
          refine ⟨25217090040434960719452437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16811393360289973812968291 25217090040434960719452437)
          ·
            refine ⟨1182051095645388783724333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25217090040434960719452437 1182051095645388783724333)
            ·
              refine ⟨443269160867020793896625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1182051095645388783724333 443269160867020793896625)
              ·
                refine ⟨332451870650265595422469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443269160867020793896625 332451870650265595422469)
                ·
                  refine ⟨62334725746924799141713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332451870650265595422469 62334725746924799141713)
                  ·
                    rfl

theorem cell20_136571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_136571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136571 prefixEnd_136571 := by exact prefixLift 136571
  have htrace : WordTrace (prefixWord ++ tailWord_136571) baseStart_136571 baseEnd_136571 := by
    simpa [prefixWord, tailWord_136571, baseEnd_136571] using wordTrace_append hprefix tailTrace_136571
  have hstable : (prefixWord ++ tailWord_136571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136571).length < 2 ^ (prefixWord ++ tailWord_136571).sum := by decide
  have hdescent : baseEnd_136571 < baseStart_136571 := by decide
  rcases family_descends (prefixWord ++ tailWord_136571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136594 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_136594 : Nat := 118140960795 + 136594 * 2 ^ 59
def prefixEnd_136594 : Nat := 4983230072969 + 3 ^ 40 * 136594 * 2
def baseEnd_136594 : Nat := 62345223573638941374953

theorem tailTrace_136594 : CollatzResearch.WordTrace tailWord_136594 prefixEnd_136594 62345223573638941374953 := by
  unfold tailWord_136594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245498116787685310760209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3321328311433827495360557 1245498116787685310760209)
  ·
    refine ⟨934123587590763983070157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1245498116787685310760209 934123587590763983070157)
    ·
      refine ⟨350296345346536493651309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 934123587590763983070157 350296345346536493651309)
      ·
        refine ⟨131361129504951185119241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 350296345346536493651309 131361129504951185119241)
        ·
          refine ⟨98520847128713388839431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131361129504951185119241 98520847128713388839431)
          ·
            refine ⟨147781270693070083259147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98520847128713388839431 147781270693070083259147)
            ·
              refine ⟨221671906039605124888721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147781270693070083259147 221671906039605124888721)
              ·
                refine ⟨166253929529703843666541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221671906039605124888721 166253929529703843666541)
                ·
                  refine ⟨62345223573638941374953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166253929529703843666541 62345223573638941374953)
                  ·
                    rfl

theorem cell20_136594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_136594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136594 prefixEnd_136594 := by exact prefixLift 136594
  have htrace : WordTrace (prefixWord ++ tailWord_136594) baseStart_136594 baseEnd_136594 := by
    simpa [prefixWord, tailWord_136594, baseEnd_136594] using wordTrace_append hprefix tailTrace_136594
  have hstable : (prefixWord ++ tailWord_136594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136594).length < 2 ^ (prefixWord ++ tailWord_136594).sum := by decide
  have hdescent : baseEnd_136594 < baseStart_136594 := by decide
  rcases family_descends (prefixWord ++ tailWord_136594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136602 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_136602 : Nat := 118140960795 + 136602 * 2 ^ 59
def prefixEnd_136602 : Nat := 4983230072969 + 3 ^ 40 * 136602 * 2
def baseEnd_136602 : Nat := 62348874991626469108253

theorem tailTrace_136602 : CollatzResearch.WordTrace tailWord_136602 prefixEnd_136602 62348874991626469108253 := by
  unfold tailWord_136602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245571062780439652333015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3321522834081172406221373 1245571062780439652333015)
  ·
    refine ⟨1868356594170659478499523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1245571062780439652333015 1868356594170659478499523)
    ·
      refine ⟨2802534891255989217749285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868356594170659478499523 2802534891255989217749285)
      ·
        refine ⟨525475292110497978327991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2802534891255989217749285 525475292110497978327991)
        ·
          refine ⟨788212938165746967491987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525475292110497978327991 788212938165746967491987)
          ·
            refine ⟨1182319407248620451237981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788212938165746967491987 1182319407248620451237981)
            ·
              refine ⟨443369777718232669214243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1182319407248620451237981 443369777718232669214243)
              ·
                refine ⟨665054666577349003821365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443369777718232669214243 665054666577349003821365)
                ·
                  refine ⟨62348874991626469108253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 665054666577349003821365 62348874991626469108253)
                  ·
                    rfl

theorem cell20_136602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_136602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136602 prefixEnd_136602 := by exact prefixLift 136602
  have htrace : WordTrace (prefixWord ++ tailWord_136602) baseStart_136602 baseEnd_136602 := by
    simpa [prefixWord, tailWord_136602, baseEnd_136602] using wordTrace_append hprefix tailTrace_136602
  have hstable : (prefixWord ++ tailWord_136602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136602).length < 2 ^ (prefixWord ++ tailWord_136602).sum := by decide
  have hdescent : baseEnd_136602 < baseStart_136602 := by decide
  rcases family_descends (prefixWord ++ tailWord_136602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136605 : List Nat := [1, 4, 2, 1, 3, 1, 2, 4, 2]
def baseStart_136605 : Nat := 118140960795 + 136605 * 2 ^ 59
def prefixEnd_136605 : Nat := 4983230072969 + 3 ^ 40 * 136605 * 2
def baseEnd_136605 : Nat := 62350244273371792008241

theorem tailTrace_136605 : CollatzResearch.WordTrace tailWord_136605 prefixEnd_136605 62350244273371792008241 := by
  unfold tailWord_136605
  simp only [CollatzResearch.WordTrace]
  refine ⟨4982393670110890121691269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3321595780073926747794179 4982393670110890121691269)
  ·
    refine ⟨934198813145791897817113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4982393670110890121691269 934198813145791897817113)
    ·
      refine ⟨700649109859343923362835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 934198813145791897817113 700649109859343923362835)
      ·
        refine ⟨1050973664789015885044253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700649109859343923362835 1050973664789015885044253)
        ·
          refine ⟨394115124295880956891595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1050973664789015885044253 394115124295880956891595)
          ·
            refine ⟨591172686443821435337393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394115124295880956891595 591172686443821435337393)
            ·
              refine ⟨443379514832866076503045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591172686443821435337393 443379514832866076503045)
              ·
                refine ⟨83133659031162389344321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443379514832866076503045 83133659031162389344321)
                ·
                  refine ⟨62350244273371792008241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83133659031162389344321 62350244273371792008241)
                  ·
                    rfl

theorem cell20_136605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_136605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136605 prefixEnd_136605 := by exact prefixLift 136605
  have htrace : WordTrace (prefixWord ++ tailWord_136605) baseStart_136605 baseEnd_136605 := by
    simpa [prefixWord, tailWord_136605, baseEnd_136605] using wordTrace_append hprefix tailTrace_136605
  have hstable : (prefixWord ++ tailWord_136605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136605).length < 2 ^ (prefixWord ++ tailWord_136605).sum := by decide
  have hdescent : baseEnd_136605 < baseStart_136605 := by decide
  rcases family_descends (prefixWord ++ tailWord_136605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136633 : List Nat := [1, 2, 1, 4, 4, 1, 1, 6]
def baseStart_136633 : Nat := 118140960795 + 136633 * 2 ^ 59
def prefixEnd_136633 : Nat := 4983230072969 + 3 ^ 40 * 136633 * 2
def baseEnd_136633 : Nat := 20787674745442713024931

theorem tailTrace_136633 : CollatzResearch.WordTrace tailWord_136633 prefixEnd_136633 20787674745442713024931 := by
  unfold tailWord_136633
  simp only [CollatzResearch.WordTrace]
  refine ⟨4983414914009450903710553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3322276609339633935807035 4983414914009450903710553)
  ·
    refine ⟨3737561185507088177782915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4983414914009450903710553 3737561185507088177782915)
    ·
      refine ⟨5606341778260632266674373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3737561185507088177782915 5606341778260632266674373)
      ·
        refine ⟨1051189083423868550001445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5606341778260632266674373 1051189083423868550001445)
        ·
          refine ⟨197097953141975353125271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1051189083423868550001445 197097953141975353125271)
          ·
            refine ⟨295646929712963029687907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197097953141975353125271 295646929712963029687907)
            ·
              refine ⟨443470394569444544531861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295646929712963029687907 443470394569444544531861)
              ·
                refine ⟨20787674745442713024931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 443470394569444544531861 20787674745442713024931)
                ·
                  rfl

theorem cell20_136633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_136633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136633 prefixEnd_136633 := by exact prefixLift 136633
  have htrace : WordTrace (prefixWord ++ tailWord_136633) baseStart_136633 baseEnd_136633 := by
    simpa [prefixWord, tailWord_136633, baseEnd_136633] using wordTrace_append hprefix tailTrace_136633
  have hstable : (prefixWord ++ tailWord_136633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136633).length < 2 ^ (prefixWord ++ tailWord_136633).sum := by decide
  have hdescent : baseEnd_136633 < baseStart_136633 := by decide
  rcases family_descends (prefixWord ++ tailWord_136633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136654 : List Nat := [4, 1, 1, 1, 2, 1, 10]
def baseStart_136654 : Nat := 118140960795 + 136654 * 2 ^ 59
def prefixEnd_136654 : Nat := 4983230072969 + 3 ^ 40 * 136654 * 2
def baseEnd_136654 : Nat := 6930289912060599930523

theorem tailTrace_136654 : CollatzResearch.WordTrace tailWord_136654 prefixEnd_136654 6930289912060599930523 := by
  unfold tailWord_136654
  simp only [CollatzResearch.WordTrace]
  refine ⟨623022605866671436278127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3322787231288914326816677 623022605866671436278127)
  ·
    refine ⟨934533908800007154417191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 623022605866671436278127 934533908800007154417191)
    ·
      refine ⟨1401800863200010731625787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934533908800007154417191 1401800863200010731625787)
      ·
        refine ⟨2102701294800016097438681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401800863200010731625787 2102701294800016097438681)
        ·
          refine ⟨1577025971100012073079011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2102701294800016097438681 1577025971100012073079011)
          ·
            refine ⟨2365538956650018109618517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577025971100012073079011 2365538956650018109618517)
            ·
              refine ⟨6930289912060599930523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2365538956650018109618517 6930289912060599930523)
              ·
                rfl

theorem cell20_136654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 10].length) (baseStart_136654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136654 prefixEnd_136654 := by exact prefixLift 136654
  have htrace : WordTrace (prefixWord ++ tailWord_136654) baseStart_136654 baseEnd_136654 := by
    simpa [prefixWord, tailWord_136654, baseEnd_136654] using wordTrace_append hprefix tailTrace_136654
  have hstable : (prefixWord ++ tailWord_136654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136654).length < 2 ^ (prefixWord ++ tailWord_136654).sum := by decide
  have hdescent : baseEnd_136654 < baseStart_136654 := by decide
  rcases family_descends (prefixWord ++ tailWord_136654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136660 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 4]
def baseStart_136660 : Nat := 118140960795 + 136660 * 2 ^ 59
def prefixEnd_136660 : Nat := 4983230072969 + 3 ^ 40 * 136660 * 2
def baseEnd_136660 : Nat := 62375347772036045174683

theorem tailTrace_136660 : CollatzResearch.WordTrace tailWord_136660 prefixEnd_136660 62375347772036045174683 := by
  unfold tailWord_136660
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492199842455817257471717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3322933123274423009962289 2492199842455817257471717)
  ·
    refine ⟨467287470460465735775947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2492199842455817257471717 467287470460465735775947)
    ·
      refine ⟨700931205690698603663921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467287470460465735775947 700931205690698603663921)
      ·
        refine ⟨525698404268023952747941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 700931205690698603663921 525698404268023952747941)
        ·
          refine ⟨98568450800254491140239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 525698404268023952747941 98568450800254491140239)
          ·
            refine ⟨147852676200381736710359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98568450800254491140239 147852676200381736710359)
            ·
              refine ⟨221779014300572605065539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147852676200381736710359 221779014300572605065539)
              ·
                refine ⟨332668521450858907598309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221779014300572605065539 332668521450858907598309)
                ·
                  refine ⟨62375347772036045174683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332668521450858907598309 62375347772036045174683)
                  ·
                    rfl

theorem cell20_136660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_136660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136660 prefixEnd_136660 := by exact prefixLift 136660
  have htrace : WordTrace (prefixWord ++ tailWord_136660) baseStart_136660 baseEnd_136660 := by
    simpa [prefixWord, tailWord_136660, baseEnd_136660] using wordTrace_append hprefix tailTrace_136660
  have hstable : (prefixWord ++ tailWord_136660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136660).length < 2 ^ (prefixWord ++ tailWord_136660).sum := by decide
  have hdescent : baseEnd_136660 < baseStart_136660 := by decide
  rcases family_descends (prefixWord ++ tailWord_136660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136664 : List Nat := [2, 1, 2, 2, 2, 1, 2, 6, 2]
def baseStart_136664 : Nat := 118140960795 + 136664 * 2 ^ 59
def prefixEnd_136664 : Nat := 4983230072969 + 3 ^ 40 * 136664 * 2
def baseEnd_136664 : Nat := 62377173481029809041333

theorem tailTrace_136664 : CollatzResearch.WordTrace tailWord_136664 prefixEnd_136664 62377173481029809041333 := by
  unfold tailWord_136664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492272788448571599044523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3323030384598095465392697 2492272788448571599044523)
  ·
    refine ⟨3738409182672857398566785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2492272788448571599044523 3738409182672857398566785)
    ·
      refine ⟨2803806887004643048925089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3738409182672857398566785 2803806887004643048925089)
      ·
        refine ⟨2102855165253482286693817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2803806887004643048925089 2102855165253482286693817)
        ·
          refine ⟨1577141373940111715020363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2102855165253482286693817 1577141373940111715020363)
          ·
            refine ⟨2365712060910167572530545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577141373940111715020363 2365712060910167572530545)
            ·
              refine ⟨1774284045682625679397909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2365712060910167572530545 1774284045682625679397909)
              ·
                refine ⟨83169564641373078721777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1774284045682625679397909 83169564641373078721777)
                ·
                  refine ⟨62377173481029809041333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83169564641373078721777 62377173481029809041333)
                  ·
                    rfl

theorem cell20_136664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_136664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136664 prefixEnd_136664 := by exact prefixLift 136664
  have htrace : WordTrace (prefixWord ++ tailWord_136664) baseStart_136664 baseEnd_136664 := by
    simpa [prefixWord, tailWord_136664, baseEnd_136664] using wordTrace_append hprefix tailTrace_136664
  have hstable : (prefixWord ++ tailWord_136664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136664).length < 2 ^ (prefixWord ++ tailWord_136664).sum := by decide
  have hdescent : baseEnd_136664 < baseStart_136664 := by decide
  rcases family_descends (prefixWord ++ tailWord_136664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136715 : List Nat := [1, 1, 1, 1, 9, 1, 2, 2, 2]
def baseStart_136715 : Nat := 118140960795 + 136715 * 2 ^ 59
def prefixEnd_136715 : Nat := 4983230072969 + 3 ^ 40 * 136715 * 2
def baseEnd_136715 : Nat := 62400451270700298341125

theorem tailTrace_136715 : CollatzResearch.WordTrace tailWord_136715 prefixEnd_136715 62400451270700298341125 := by
  unfold tailWord_136715
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986405699712378908195599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3324270466474919272130399 4986405699712378908195599)
  ·
    refine ⟨7479608549568568362293399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4986405699712378908195599 7479608549568568362293399)
    ·
      refine ⟨11219412824352852543440099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7479608549568568362293399 11219412824352852543440099)
      ·
        refine ⟨16829119236529278815160149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11219412824352852543440099 16829119236529278815160149)
        ·
          refine ⟨98608120526538743057579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 16829119236529278815160149 98608120526538743057579)
          ·
            refine ⟨147912180789808114586369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98608120526538743057579 147912180789808114586369)
            ·
              refine ⟨110934135592356085939777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147912180789808114586369 110934135592356085939777)
              ·
                refine ⟨83200601694267064454833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110934135592356085939777 83200601694267064454833)
                ·
                  refine ⟨62400451270700298341125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83200601694267064454833 62400451270700298341125)
                  ·
                    rfl

theorem cell20_136715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 2].length) (baseStart_136715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136715 prefixEnd_136715 := by exact prefixLift 136715
  have htrace : WordTrace (prefixWord ++ tailWord_136715) baseStart_136715 baseEnd_136715 := by
    simpa [prefixWord, tailWord_136715, baseEnd_136715] using wordTrace_append hprefix tailTrace_136715
  have hstable : (prefixWord ++ tailWord_136715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136715).length < 2 ^ (prefixWord ++ tailWord_136715).sum := by decide
  have hdescent : baseEnd_136715 < baseStart_136715 := by decide
  rcases family_descends (prefixWord ++ tailWord_136715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136757 : List Nat := [1, 3, 3, 1, 1, 4, 2, 3, 2]
def baseStart_136757 : Nat := 118140960795 + 136757 * 2 ^ 59
def prefixEnd_136757 : Nat := 4983230072969 + 3 ^ 40 * 136757 * 2
def baseEnd_136757 : Nat := 62419621215134818940953

theorem tailTrace_136757 : CollatzResearch.WordTrace tailWord_136757 prefixEnd_136757 62419621215134818940953 := by
  unfold tailWord_136757
  simp only [CollatzResearch.WordTrace]
  refine ⟨4987937565560220081224525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3325291710373480054149683 4987937565560220081224525)
  ·
    refine ⟨1870476587085082530459197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4987937565560220081224525 1870476587085082530459197)
    ·
      refine ⟨701428720156905948922199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1870476587085082530459197 701428720156905948922199)
      ·
        refine ⟨1052143080235358923383299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 701428720156905948922199 1052143080235358923383299)
        ·
          refine ⟨1578214620353038385074949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052143080235358923383299 1578214620353038385074949)
          ·
            refine ⟨295915241316194697201553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1578214620353038385074949 295915241316194697201553)
            ·
              refine ⟨221936430987146022901165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295915241316194697201553 221936430987146022901165)
              ·
                refine ⟨83226161620179758587937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221936430987146022901165 83226161620179758587937)
                ·
                  refine ⟨62419621215134818940953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83226161620179758587937 62419621215134818940953)
                  ·
                    rfl

theorem cell20_136757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_136757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136757 prefixEnd_136757 := by exact prefixLift 136757
  have htrace : WordTrace (prefixWord ++ tailWord_136757) baseStart_136757 baseEnd_136757 := by
    simpa [prefixWord, tailWord_136757, baseEnd_136757] using wordTrace_append hprefix tailTrace_136757
  have hstable : (prefixWord ++ tailWord_136757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136757).length < 2 ^ (prefixWord ++ tailWord_136757).sum := by decide
  have hdescent : baseEnd_136757 < baseStart_136757 := by decide
  rcases family_descends (prefixWord ++ tailWord_136757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136774 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_136774 : Nat := 118140960795 + 136774 * 2 ^ 59
def prefixEnd_136774 : Nat := 4983230072969 + 3 ^ 40 * 136774 * 2
def baseEnd_136774 : Nat := 62427380478358315374217

theorem tailTrace_136774 : CollatzResearch.WordTrace tailWord_136774 prefixEnd_136774 62427380478358315374217 := by
  unfold tailWord_136774
  simp only [CollatzResearch.WordTrace]
  refine ⟨155892425203082249518543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3325705070999087989728917 155892425203082249518543)
  ·
    refine ⟨233838637804623374277815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155892425203082249518543 233838637804623374277815)
    ·
      refine ⟨350757956706935061416723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233838637804623374277815 350757956706935061416723)
      ·
        refine ⟨526136935060402592125085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350757956706935061416723 526136935060402592125085)
        ·
          refine ⟨197301350647650972046907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 526136935060402592125085 197301350647650972046907)
          ·
            refine ⟨295952025971476458070361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197301350647650972046907 295952025971476458070361)
            ·
              refine ⟨221964019478607343552771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295952025971476458070361 221964019478607343552771)
              ·
                refine ⟨332946029217911015329157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221964019478607343552771 332946029217911015329157)
                ·
                  refine ⟨62427380478358315374217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332946029217911015329157 62427380478358315374217)
                  ·
                    rfl

theorem cell20_136774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_136774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136774 prefixEnd_136774 := by exact prefixLift 136774
  have htrace : WordTrace (prefixWord ++ tailWord_136774) baseStart_136774 baseEnd_136774 := by
    simpa [prefixWord, tailWord_136774, baseEnd_136774] using wordTrace_append hprefix tailTrace_136774
  have hstable : (prefixWord ++ tailWord_136774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136774).length < 2 ^ (prefixWord ++ tailWord_136774).sum := by decide
  have hdescent : baseEnd_136774 < baseStart_136774 := by decide
  rcases family_descends (prefixWord ++ tailWord_136774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136778 : List Nat := [3, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_136778 : Nat := 118140960795 + 136778 * 2 ^ 59
def prefixEnd_136778 : Nat := 4983230072969 + 3 ^ 40 * 136778 * 2
def baseEnd_136778 : Nat := 62429206187352079240867

theorem tailTrace_136778 : CollatzResearch.WordTrace tailWord_136778 prefixEnd_136778 62429206187352079240867 := by
  unfold tailWord_136778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247175874621035166934747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3325802332322760445159325 1247175874621035166934747)
  ·
    refine ⟨1870763811931552750402121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1247175874621035166934747 1870763811931552750402121)
    ·
      refine ⟨1403072858948664562801591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1870763811931552750402121 1403072858948664562801591)
      ·
        refine ⟨2104609288422996844202387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1403072858948664562801591 2104609288422996844202387)
        ·
          refine ⟨3156913932634495266303581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2104609288422996844202387 3156913932634495266303581)
          ·
            refine ⟨1183842724737935724863843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3156913932634495266303581 1183842724737935724863843)
            ·
              refine ⟨1775764087106903587295765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183842724737935724863843 1775764087106903587295765)
              ·
                refine ⟨83238941583136105654489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1775764087106903587295765 83238941583136105654489)
                ·
                  refine ⟨62429206187352079240867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83238941583136105654489 62429206187352079240867)
                  ·
                    rfl

theorem cell20_136778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_136778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136778 prefixEnd_136778 := by exact prefixLift 136778
  have htrace : WordTrace (prefixWord ++ tailWord_136778) baseStart_136778 baseEnd_136778 := by
    simpa [prefixWord, tailWord_136778, baseEnd_136778] using wordTrace_append hprefix tailTrace_136778
  have hstable : (prefixWord ++ tailWord_136778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136778).length < 2 ^ (prefixWord ++ tailWord_136778).sum := by decide
  have hdescent : baseEnd_136778 < baseStart_136778 := by decide
  rcases family_descends (prefixWord ++ tailWord_136778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136840 : List Nat := [2, 1, 3, 5, 1, 1, 2, 5]
def baseStart_136840 : Nat := 118140960795 + 136840 * 2 ^ 59
def prefixEnd_136840 : Nat := 4983230072969 + 3 ^ 40 * 136840 * 2
def baseEnd_136840 : Nat := 20819168225585139724649

theorem tailTrace_136840 : CollatzResearch.WordTrace tailWord_136840 prefixEnd_136840 20819168225585139724649 := by
  unfold tailWord_136840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495482412129762628247987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3327309882839683504330649 2495482412129762628247987)
  ·
    refine ⟨3743223618194643942371981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495482412129762628247987 3743223618194643942371981)
    ·
      refine ⟨1403708856822991478389493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3743223618194643942371981 1403708856822991478389493)
      ·
        refine ⟨131597705327155451099015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1403708856822991478389493 131597705327155451099015)
        ·
          refine ⟨197396557990733176648523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131597705327155451099015 197396557990733176648523)
          ·
            refine ⟨296094836986099764972785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197396557990733176648523 296094836986099764972785)
            ·
              refine ⟨222071127739574823729589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296094836986099764972785 222071127739574823729589)
              ·
                refine ⟨20819168225585139724649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222071127739574823729589 20819168225585139724649)
                ·
                  rfl

theorem cell20_136840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_136840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136840 prefixEnd_136840 := by exact prefixLift 136840
  have htrace : WordTrace (prefixWord ++ tailWord_136840) baseStart_136840 baseEnd_136840 := by
    simpa [prefixWord, tailWord_136840, baseEnd_136840] using wordTrace_append hprefix tailTrace_136840
  have hstable : (prefixWord ++ tailWord_136840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136840).length < 2 ^ (prefixWord ++ tailWord_136840).sum := by decide
  have hdescent : baseEnd_136840 < baseStart_136840 := by decide
  rcases family_descends (prefixWord ++ tailWord_136840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136844 : List Nat := [2, 2, 1, 2, 1, 1, 6, 5]
def baseStart_136844 : Nat := 118140960795 + 136844 * 2 ^ 59
def prefixEnd_136844 : Nat := 4983230072969 + 3 ^ 40 * 136844 * 2
def baseEnd_136844 : Nat := 20819776795249727680199

theorem tailTrace_136844 : CollatzResearch.WordTrace tailWord_136844 prefixEnd_136844 20819776795249727680199 := by
  unfold tailWord_136844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495555358122516969820793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3327407144163355959761057 2495555358122516969820793)
  ·
    refine ⟨1871666518591887727365595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2495555358122516969820793 1871666518591887727365595)
    ·
      refine ⟨2807499777887831591048393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871666518591887727365595 2807499777887831591048393)
      ·
        refine ⟨2105624833415873693286295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2807499777887831591048393 2105624833415873693286295)
        ·
          refine ⟨3158437250123810539929443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105624833415873693286295 3158437250123810539929443)
          ·
            refine ⟨4737655875185715809894165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3158437250123810539929443 4737655875185715809894165)
            ·
              refine ⟨222077619149330428588789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4737655875185715809894165 222077619149330428588789)
              ·
                refine ⟨20819776795249727680199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222077619149330428588789 20819776795249727680199)
                ·
                  rfl

theorem cell20_136844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_136844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136844 prefixEnd_136844 := by exact prefixLift 136844
  have htrace : WordTrace (prefixWord ++ tailWord_136844) baseStart_136844 baseEnd_136844 := by
    simpa [prefixWord, tailWord_136844, baseEnd_136844] using wordTrace_append hprefix tailTrace_136844
  have hstable : (prefixWord ++ tailWord_136844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136844).length < 2 ^ (prefixWord ++ tailWord_136844).sum := by decide
  have hdescent : baseEnd_136844 < baseStart_136844 := by decide
  rcases family_descends (prefixWord ++ tailWord_136844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136878 : List Nat := [4, 1, 4, 1, 3, 7]
def baseStart_136878 : Nat := 118140960795 + 136878 * 2 ^ 59
def prefixEnd_136878 : Nat := 4983230072969 + 3 ^ 40 * 136878 * 2
def baseEnd_136878 : Nat := 2313883293044302811375

theorem tailTrace_136878 : CollatzResearch.WordTrace tailWord_136878 prefixEnd_136878 2313883293044302811375 := by
  unfold tailWord_136878
  simp only [CollatzResearch.WordTrace]
  refine ⟨624043849765232218297411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3328233865414571830919525 624043849765232218297411)
  ·
    refine ⟨936065774647848327446117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 624043849765232218297411 936065774647848327446117)
    ·
      refine ⟨175512332746471561396147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 936065774647848327446117 175512332746471561396147)
      ·
        refine ⟨263268499119707342094221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175512332746471561396147 263268499119707342094221)
        ·
          refine ⟨98725687169890253285333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263268499119707342094221 98725687169890253285333)
          ·
            refine ⟨2313883293044302811375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 98725687169890253285333 2313883293044302811375)
            ·
              rfl

theorem cell20_136878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 7].length) (baseStart_136878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136878 prefixEnd_136878 := by exact prefixLift 136878
  have htrace : WordTrace (prefixWord ++ tailWord_136878) baseStart_136878 baseEnd_136878 := by
    simpa [prefixWord, tailWord_136878, baseEnd_136878] using wordTrace_append hprefix tailTrace_136878
  have hstable : (prefixWord ++ tailWord_136878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136878).length < 2 ^ (prefixWord ++ tailWord_136878).sum := by decide
  have hdescent : baseEnd_136878 < baseStart_136878 := by decide
  rcases family_descends (prefixWord ++ tailWord_136878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136889 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_136889 : Nat := 118140960795 + 136889 * 2 ^ 59
def prefixEnd_136889 : Nat := 4983230072969 + 3 ^ 40 * 136889 * 2
def baseEnd_136889 : Nat := 62479869611929026540413

theorem tailTrace_136889 : CollatzResearch.WordTrace tailWord_136889 prefixEnd_136889 62479869611929026540413 := by
  unfold tailWord_136889
  simp only [CollatzResearch.WordTrace]
  refine ⟨4992752001082006625029721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3328501334054671083353147 4992752001082006625029721)
  ·
    refine ⟨3744564000811504968772291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4992752001082006625029721 3744564000811504968772291)
    ·
      refine ⟨5616846001217257453158437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744564000811504968772291 5616846001217257453158437)
      ·
        refine ⟨1053158625228235772467207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5616846001217257453158437 1053158625228235772467207)
        ·
          refine ⟨1579737937842353658700811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053158625228235772467207 1579737937842353658700811)
          ·
            refine ⟨2369606906763530488051217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579737937842353658700811 2369606906763530488051217)
            ·
              refine ⟨1777205180072647866038413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369606906763530488051217 1777205180072647866038413)
              ·
                refine ⟨666451942527242949764405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1777205180072647866038413 666451942527242949764405)
                ·
                  refine ⟨62479869611929026540413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 666451942527242949764405 62479869611929026540413)
                  ·
                    rfl

theorem cell20_136889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_136889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136889 prefixEnd_136889 := by exact prefixLift 136889
  have htrace : WordTrace (prefixWord ++ tailWord_136889) baseStart_136889 baseEnd_136889 := by
    simpa [prefixWord, tailWord_136889, baseEnd_136889] using wordTrace_append hprefix tailTrace_136889
  have hstable : (prefixWord ++ tailWord_136889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136889).length < 2 ^ (prefixWord ++ tailWord_136889).sum := by decide
  have hdescent : baseEnd_136889 < baseStart_136889 := by decide
  rcases family_descends (prefixWord ++ tailWord_136889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136909 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 4]
def baseStart_136909 : Nat := 118140960795 + 136909 * 2 ^ 59
def prefixEnd_136909 : Nat := 4983230072969 + 3 ^ 40 * 136909 * 2
def baseEnd_136909 : Nat := 62488998156897845873665

theorem tailTrace_136909 : CollatzResearch.WordTrace tailWord_136909 prefixEnd_136909 62488998156897845873665 := by
  unfold tailWord_136909
  simp only [CollatzResearch.WordTrace]
  refine ⟨4993481461009550040757781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3328987640673033360505187 4993481461009550040757781)
  ·
    refine ⟨234069443484822658160521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4993481461009550040757781 234069443484822658160521)
    ·
      refine ⟨175552082613616993620391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234069443484822658160521 175552082613616993620391)
      ·
        refine ⟨263328123920425490430587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175552082613616993620391 263328123920425490430587)
        ·
          refine ⟨394992185880638235645881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263328123920425490430587 394992185880638235645881)
          ·
            refine ⟨296244139410478676734411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394992185880638235645881 296244139410478676734411)
            ·
              refine ⟨444366209115718015101617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296244139410478676734411 444366209115718015101617)
              ·
                refine ⟨333274656836788511326213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444366209115718015101617 333274656836788511326213)
                ·
                  refine ⟨62488998156897845873665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333274656836788511326213 62488998156897845873665)
                  ·
                    rfl

theorem cell20_136909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_136909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136909 prefixEnd_136909 := by exact prefixLift 136909
  have htrace : WordTrace (prefixWord ++ tailWord_136909) baseStart_136909 baseEnd_136909 := by
    simpa [prefixWord, tailWord_136909, baseEnd_136909] using wordTrace_append hprefix tailTrace_136909
  have hstable : (prefixWord ++ tailWord_136909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136909).length < 2 ^ (prefixWord ++ tailWord_136909).sum := by decide
  have hdescent : baseEnd_136909 < baseStart_136909 := by decide
  rcases family_descends (prefixWord ++ tailWord_136909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136913 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_136913 : Nat := 118140960795 + 136913 * 2 ^ 59
def prefixEnd_136913 : Nat := 4983230072969 + 3 ^ 40 * 136913 * 2
def baseEnd_136913 : Nat := 62490823865891609740315

theorem tailTrace_136913 : CollatzResearch.WordTrace tailWord_136913 prefixEnd_136913 62490823865891609740315 := by
  unfold tailWord_136913
  simp only [CollatzResearch.WordTrace]
  refine ⟨4993627352995058723903393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3329084901996705815935595 4993627352995058723903393)
  ·
    refine ⟨3745220514746294042927545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4993627352995058723903393 3745220514746294042927545)
    ·
      refine ⟨2808915386059720532195659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3745220514746294042927545 2808915386059720532195659)
      ·
        refine ⟨4213373079089580798293489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2808915386059720532195659 4213373079089580798293489)
        ·
          refine ⟨3160029809317185598720117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4213373079089580798293489 3160029809317185598720117)
          ·
            refine ⟨296252794623486149880011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3160029809317185598720117 296252794623486149880011)
            ·
              refine ⟨444379191935229224820017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296252794623486149880011 444379191935229224820017)
              ·
                refine ⟨333284393951421918615013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444379191935229224820017 333284393951421918615013)
                ·
                  refine ⟨62490823865891609740315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333284393951421918615013 62490823865891609740315)
                  ·
                    rfl

theorem cell20_136913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_136913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136913 prefixEnd_136913 := by exact prefixLift 136913
  have htrace : WordTrace (prefixWord ++ tailWord_136913) baseStart_136913 baseEnd_136913 := by
    simpa [prefixWord, tailWord_136913, baseEnd_136913] using wordTrace_append hprefix tailTrace_136913
  have hstable : (prefixWord ++ tailWord_136913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136913).length < 2 ^ (prefixWord ++ tailWord_136913).sum := by decide
  have hdescent : baseEnd_136913 < baseStart_136913 := by decide
  rcases family_descends (prefixWord ++ tailWord_136913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136916 : List Nat := [2, 4, 1, 3, 1, 2, 3, 4]
def baseStart_136916 : Nat := 118140960795 + 136916 * 2 ^ 59
def prefixEnd_136916 : Nat := 4983230072969 + 3 ^ 40 * 136916 * 2
def baseEnd_136916 : Nat := 20830731049212310880101

theorem tailTrace_136916 : CollatzResearch.WordTrace tailWord_136916 prefixEnd_136916 20830731049212310880101 := by
  unfold tailWord_136916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496868385992095118131301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3329157847989460157508401 2496868385992095118131301)
  ·
    refine ⟨468162822373517834649619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2496868385992095118131301 468162822373517834649619)
    ·
      refine ⟨702244233560276751974429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468162822373517834649619 702244233560276751974429)
      ·
        refine ⟨263341587585103781990411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 702244233560276751974429 263341587585103781990411)
        ·
          refine ⟨395012381377655672985617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263341587585103781990411 395012381377655672985617)
          ·
            refine ⟨296259286033241754739213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395012381377655672985617 296259286033241754739213)
            ·
              refine ⟨111097232262465658027205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296259286033241754739213 111097232262465658027205)
              ·
                refine ⟨20830731049212310880101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111097232262465658027205 20830731049212310880101)
                ·
                  rfl

theorem cell20_136916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_136916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136916 prefixEnd_136916 := by exact prefixLift 136916
  have htrace : WordTrace (prefixWord ++ tailWord_136916) baseStart_136916 baseEnd_136916 := by
    simpa [prefixWord, tailWord_136916, baseEnd_136916] using wordTrace_append hprefix tailTrace_136916
  have hstable : (prefixWord ++ tailWord_136916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136916).length < 2 ^ (prefixWord ++ tailWord_136916).sum := by decide
  have hdescent : baseEnd_136916 < baseStart_136916 := by decide
  rcases family_descends (prefixWord ++ tailWord_136916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136927 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_136927 : Nat := 118140960795 + 136927 * 2 ^ 59
def prefixEnd_136927 : Nat := 4983230072969 + 3 ^ 40 * 136927 * 2
def baseEnd_136927 : Nat := 62497213847369783273591

theorem tailTrace_136927 : CollatzResearch.WordTrace tailWord_136927 prefixEnd_136927 62497213847369783273591 := by
  unfold tailWord_136927
  simp only [CollatzResearch.WordTrace]
  refine ⟨4994137974944339114913035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3329425316629559409942023 4994137974944339114913035)
  ·
    refine ⟨7491206962416508672369553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4994137974944339114913035 7491206962416508672369553)
    ·
      refine ⟨5618405221812381504277165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7491206962416508672369553 5618405221812381504277165)
      ·
        refine ⟨2106901958179643064103937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5618405221812381504277165 2106901958179643064103937)
        ·
          refine ⟨1580176468634732298077953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2106901958179643064103937 1580176468634732298077953)
          ·
            refine ⟨1185132351476049223558465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1580176468634732298077953 1185132351476049223558465)
            ·
              refine ⟨888849263607036917668849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1185132351476049223558465 888849263607036917668849)
              ·
                refine ⟨666636947705277688251637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 888849263607036917668849 666636947705277688251637)
                ·
                  refine ⟨62497213847369783273591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 666636947705277688251637 62497213847369783273591)
                  ·
                    rfl

theorem cell20_136927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_136927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136927 prefixEnd_136927 := by exact prefixLift 136927
  have htrace : WordTrace (prefixWord ++ tailWord_136927) baseStart_136927 baseEnd_136927 := by
    simpa [prefixWord, tailWord_136927, baseEnd_136927] using wordTrace_append hprefix tailTrace_136927
  have hstable : (prefixWord ++ tailWord_136927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136927).length < 2 ^ (prefixWord ++ tailWord_136927).sum := by decide
  have hdescent : baseEnd_136927 < baseStart_136927 := by decide
  rcases family_descends (prefixWord ++ tailWord_136927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136996 : List Nat := [2, 3, 1, 3, 2, 1, 8]
def baseStart_136996 : Nat := 118140960795 + 136996 * 2 ^ 59
def prefixEnd_136996 : Nat := 4983230072969 + 3 ^ 40 * 136996 * 2
def baseEnd_136996 : Nat := 6947634147501356663701

theorem tailTrace_136996 : CollatzResearch.WordTrace tailWord_136996 prefixEnd_136996 6947634147501356663701 := by
  unfold tailWord_136996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498327305847181949587421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3331103074462909266116561 2498327305847181949587421)
  ·
    refine ⟨936872739692693231095283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2498327305847181949587421 936872739692693231095283)
    ·
      refine ⟨1405309109539039846642925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 936872739692693231095283 1405309109539039846642925)
      ·
        refine ⟨526990916077139942491097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1405309109539039846642925 526990916077139942491097)
        ·
          refine ⟨395243187057854956868323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526990916077139942491097 395243187057854956868323)
          ·
            refine ⟨592864780586782435302485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395243187057854956868323 592864780586782435302485)
            ·
              refine ⟨6947634147501356663701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 592864780586782435302485 6947634147501356663701)
              ·
                rfl

theorem cell20_136996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 8].length) (baseStart_136996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_136996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_136996 prefixEnd_136996 := by exact prefixLift 136996
  have htrace : WordTrace (prefixWord ++ tailWord_136996) baseStart_136996 baseEnd_136996 := by
    simpa [prefixWord, tailWord_136996, baseEnd_136996] using wordTrace_append hprefix tailTrace_136996
  have hstable : (prefixWord ++ tailWord_136996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136996).length < 2 ^ (prefixWord ++ tailWord_136996).sum := by decide
  have hdescent : baseEnd_136996 < baseStart_136996 := by decide
  rcases family_descends (prefixWord ++ tailWord_136996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137013 : List Nat := [1, 3, 3, 1, 4, 1, 2, 5]
def baseStart_137013 : Nat := 118140960795 + 137013 * 2 ^ 59
def prefixEnd_137013 : Nat := 4983230072969 + 3 ^ 40 * 137013 * 2
def baseEnd_137013 : Nat := 20845488863578568802191

theorem tailTrace_137013 : CollatzResearch.WordTrace tailWord_137013 prefixEnd_137013 20845488863578568802191 := by
  unfold tailWord_137013
  simp only [CollatzResearch.WordTrace]
  refine ⟨4997274652632775802543693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3331516435088517201695795 4997274652632775802543693)
  ·
    refine ⟨1873977994737290925953885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4997274652632775802543693 1873977994737290925953885)
    ·
      refine ⟨702741748026484097232707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1873977994737290925953885 702741748026484097232707)
      ·
        refine ⟨1054112622039726145849061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702741748026484097232707 1054112622039726145849061)
        ·
          refine ⟨197646116632448652346699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1054112622039726145849061 197646116632448652346699)
          ·
            refine ⟨296469174948672978520049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197646116632448652346699 296469174948672978520049)
            ·
              refine ⟨222351881211504733890037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296469174948672978520049 222351881211504733890037)
              ·
                refine ⟨20845488863578568802191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222351881211504733890037 20845488863578568802191)
                ·
                  rfl

theorem cell20_137013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 5].length) (baseStart_137013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137013 prefixEnd_137013 := by exact prefixLift 137013
  have htrace : WordTrace (prefixWord ++ tailWord_137013) baseStart_137013 baseEnd_137013 := by
    simpa [prefixWord, tailWord_137013, baseEnd_137013] using wordTrace_append hprefix tailTrace_137013
  have hstable : (prefixWord ++ tailWord_137013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137013).length < 2 ^ (prefixWord ++ tailWord_137013).sum := by decide
  have hdescent : baseEnd_137013 < baseStart_137013 := by decide
  rcases family_descends (prefixWord ++ tailWord_137013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137030 : List Nat := [6, 1, 1, 2, 1, 1, 2, 6]
def baseStart_137030 : Nat := 118140960795 + 137030 * 2 ^ 59
def prefixEnd_137030 : Nat := 4983230072969 + 3 ^ 40 * 137030 * 2
def baseEnd_137030 : Nat := 20848075284653067613279

theorem tailTrace_137030 : CollatzResearch.WordTrace tailWord_137030 prefixEnd_137030 20848075284653067613279 := by
  unfold tailWord_137030
  simp only [CollatzResearch.WordTrace]
  refine ⟨156184209174099615809767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3331929795714125137275029 156184209174099615809767)
  ·
    refine ⟨234276313761149423714651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156184209174099615809767 234276313761149423714651)
    ·
      refine ⟨351414470641724135571977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234276313761149423714651 351414470641724135571977)
      ·
        refine ⟨263560852981293101678983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351414470641724135571977 263560852981293101678983)
        ·
          refine ⟨395341279471939652518475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263560852981293101678983 395341279471939652518475)
          ·
            refine ⟨593011919207909478777713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395341279471939652518475 593011919207909478777713)
            ·
              refine ⟨444758939405932109083285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593011919207909478777713 444758939405932109083285)
              ·
                refine ⟨20848075284653067613279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 444758939405932109083285 20848075284653067613279)
                ·
                  rfl

theorem cell20_137030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_137030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137030 prefixEnd_137030 := by exact prefixLift 137030
  have htrace : WordTrace (prefixWord ++ tailWord_137030) baseStart_137030 baseEnd_137030 := by
    simpa [prefixWord, tailWord_137030, baseEnd_137030] using wordTrace_append hprefix tailTrace_137030
  have hstable : (prefixWord ++ tailWord_137030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137030).length < 2 ^ (prefixWord ++ tailWord_137030).sum := by decide
  have hdescent : baseEnd_137030 < baseStart_137030 := by decide
  rcases family_descends (prefixWord ++ tailWord_137030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137055 : List Nat := [1, 1, 2, 3, 1, 12]
def baseStart_137055 : Nat := 118140960795 + 137055 * 2 ^ 59
def prefixEnd_137055 : Nat := 4983230072969 + 3 ^ 40 * 137055 * 2
def baseEnd_137055 : Nat := 2316875427228526926163

theorem tailTrace_137055 : CollatzResearch.WordTrace tailWord_137055 prefixEnd_137055 2316875427228526926163 := by
  unfold tailWord_137055
  simp only [CollatzResearch.WordTrace]
  refine ⟨4998806518480616975572619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3332537678987077983715079 4998806518480616975572619)
  ·
    refine ⟨7498209777720925463358929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4998806518480616975572619 7498209777720925463358929)
    ·
      refine ⟨5623657333290694097519197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7498209777720925463358929 5623657333290694097519197)
      ·
        refine ⟨2108871499984010286569699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5623657333290694097519197 2108871499984010286569699)
        ·
          refine ⟨3163307249976015429854549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2108871499984010286569699 3163307249976015429854549)
          ·
            refine ⟨2316875427228526926163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3163307249976015429854549 2316875427228526926163)
            ·
              rfl

theorem cell20_137055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 12].length) (baseStart_137055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137055 prefixEnd_137055 := by exact prefixLift 137055
  have htrace : WordTrace (prefixWord ++ tailWord_137055) baseStart_137055 baseEnd_137055 := by
    simpa [prefixWord, tailWord_137055, baseEnd_137055] using wordTrace_append hprefix tailTrace_137055
  have hstable : (prefixWord ++ tailWord_137055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137055).length < 2 ^ (prefixWord ++ tailWord_137055).sum := by decide
  have hdescent : baseEnd_137055 < baseStart_137055 := by decide
  rcases family_descends (prefixWord ++ tailWord_137055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137140 : List Nat := [2, 5, 2, 1, 3, 1, 2, 4]
def baseStart_137140 : Nat := 118140960795 + 137140 * 2 ^ 59
def prefixEnd_137140 : Nat := 4983230072969 + 3 ^ 40 * 137140 * 2
def baseEnd_137140 : Nat := 20864810950429236390907

theorem tailTrace_137140 : CollatzResearch.WordTrace tailWord_137140 prefixEnd_137140 20864810950429236390907 := by
  unfold tailWord_137140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500953361586338246208437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3334604482115117661611249 2500953361586338246208437)
  ·
    refine ⟨234464377648719210582041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2500953361586338246208437 234464377648719210582041)
    ·
      refine ⟨175848283236539407936531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234464377648719210582041 175848283236539407936531)
      ·
        refine ⟨263772424854809111904797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175848283236539407936531 263772424854809111904797)
        ·
          refine ⟨98914659320553416964299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263772424854809111904797 98914659320553416964299)
          ·
            refine ⟨148371988980830125446449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98914659320553416964299 148371988980830125446449)
            ·
              refine ⟨111278991735622594084837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148371988980830125446449 111278991735622594084837)
              ·
                refine ⟨20864810950429236390907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111278991735622594084837 20864810950429236390907)
                ·
                  rfl

theorem cell20_137140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_137140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137140 prefixEnd_137140 := by exact prefixLift 137140
  have htrace : WordTrace (prefixWord ++ tailWord_137140) baseStart_137140 baseEnd_137140 := by
    simpa [prefixWord, tailWord_137140, baseEnd_137140] using wordTrace_append hprefix tailTrace_137140
  have hstable : (prefixWord ++ tailWord_137140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137140).length < 2 ^ (prefixWord ++ tailWord_137140).sum := by decide
  have hdescent : baseEnd_137140 < baseStart_137140 := by decide
  rcases family_descends (prefixWord ++ tailWord_137140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137141 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_137141 : Nat := 118140960795 + 137141 * 2 ^ 59
def prefixEnd_137141 : Nat := 4983230072969 + 3 ^ 40 * 137141 * 2
def baseEnd_137141 : Nat := 62594889278536150139383

theorem tailTrace_137141 : CollatzResearch.WordTrace tailWord_137141 prefixEnd_137141 62594889278536150139383 := by
  unfold tailWord_137141
  simp only [CollatzResearch.WordTrace]
  refine ⟨5001943196169053663203277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3334628797446035775468851 5001943196169053663203277)
  ·
    refine ⟨1875728698563395123701229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5001943196169053663203277 1875728698563395123701229)
    ·
      refine ⟨703398261961273171387961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1875728698563395123701229 703398261961273171387961)
      ·
        refine ⟨527548696470954878540971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 703398261961273171387961 527548696470954878540971)
        ·
          refine ⟨791323044706432317811457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527548696470954878540971 791323044706432317811457)
          ·
            refine ⟨593492283529824238358593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 791323044706432317811457 593492283529824238358593)
            ·
              refine ⟨445119212647368178768945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593492283529824238358593 445119212647368178768945)
              ·
                refine ⟨333839409485526134076709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445119212647368178768945 333839409485526134076709)
                ·
                  refine ⟨62594889278536150139383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333839409485526134076709 62594889278536150139383)
                  ·
                    rfl

theorem cell20_137141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_137141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137141 prefixEnd_137141 := by exact prefixLift 137141
  have htrace : WordTrace (prefixWord ++ tailWord_137141) baseStart_137141 baseEnd_137141 := by
    simpa [prefixWord, tailWord_137141, baseEnd_137141] using wordTrace_append hprefix tailTrace_137141
  have hstable : (prefixWord ++ tailWord_137141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137141).length < 2 ^ (prefixWord ++ tailWord_137141).sum := by decide
  have hdescent : baseEnd_137141 < baseStart_137141 := by decide
  rcases family_descends (prefixWord ++ tailWord_137141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137162 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_137162 : Nat := 118140960795 + 137162 * 2 ^ 59
def prefixEnd_137162 : Nat := 4983230072969 + 3 ^ 40 * 137162 * 2
def baseEnd_137162 : Nat := 62604474250753410439297

theorem tailTrace_137162 : CollatzResearch.WordTrace tailWord_137162 prefixEnd_137162 62604474250753410439297 := by
  unfold tailWord_137162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250677282273243562429435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3335139419395316166478493 1250677282273243562429435)
  ·
    refine ⟨1876015923409865343644153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1250677282273243562429435 1876015923409865343644153)
    ·
      refine ⟨1407011942557399007733115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1876015923409865343644153 1407011942557399007733115)
      ·
        refine ⟨2110517913836098511599673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407011942557399007733115 2110517913836098511599673)
        ·
          refine ⟨1582888435377073883699755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2110517913836098511599673 1582888435377073883699755)
          ·
            refine ⟨2374332653065610825549633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582888435377073883699755 2374332653065610825549633)
            ·
              refine ⟨1780749489799208119162225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374332653065610825549633 1780749489799208119162225)
              ·
                refine ⟨1335562117349406089371669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780749489799208119162225 1335562117349406089371669)
                ·
                  refine ⟨62604474250753410439297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1335562117349406089371669 62604474250753410439297)
                  ·
                    rfl

theorem cell20_137162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_137162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137162 prefixEnd_137162 := by exact prefixLift 137162
  have htrace : WordTrace (prefixWord ++ tailWord_137162) baseStart_137162 baseEnd_137162 := by
    simpa [prefixWord, tailWord_137162, baseEnd_137162] using wordTrace_append hprefix tailTrace_137162
  have hstable : (prefixWord ++ tailWord_137162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137162).length < 2 ^ (prefixWord ++ tailWord_137162).sum := by decide
  have hdescent : baseEnd_137162 < baseStart_137162 := by decide
  rcases family_descends (prefixWord ++ tailWord_137162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137172 : List Nat := [2, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_137172 : Nat := 118140960795 + 137172 * 2 ^ 59
def prefixEnd_137172 : Nat := 4983230072969 + 3 ^ 40 * 137172 * 2
def baseEnd_137172 : Nat := 62609038523237820105923

theorem tailTrace_137172 : CollatzResearch.WordTrace tailWord_137172 prefixEnd_137172 62609038523237820105923 := by
  unfold tailWord_137172
  simp only [CollatzResearch.WordTrace]
  refine ⟨2501536929528372978790885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3335382572704497305054513 2501536929528372978790885)
  ·
    refine ⟨469038174286569933523291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2501536929528372978790885 469038174286569933523291)
    ·
      refine ⟨703557261429854900284937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469038174286569933523291 703557261429854900284937)
      ·
        refine ⟨527667946072391175213703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 703557261429854900284937 527667946072391175213703)
        ·
          refine ⟨791501919108586762820555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527667946072391175213703 791501919108586762820555)
          ·
            refine ⟨1187252878662880144230833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791501919108586762820555 1187252878662880144230833)
            ·
              refine ⟨890439658997160108173125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1187252878662880144230833 890439658997160108173125)
              ·
                refine ⟨166957436061967520282461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 890439658997160108173125 166957436061967520282461)
                ·
                  refine ⟨62609038523237820105923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166957436061967520282461 62609038523237820105923)
                  ·
                    rfl

theorem cell20_137172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_137172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137172 prefixEnd_137172 := by exact prefixLift 137172
  have htrace : WordTrace (prefixWord ++ tailWord_137172) baseStart_137172 baseEnd_137172 := by
    simpa [prefixWord, tailWord_137172, baseEnd_137172] using wordTrace_append hprefix tailTrace_137172
  have hstable : (prefixWord ++ tailWord_137172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137172).length < 2 ^ (prefixWord ++ tailWord_137172).sum := by decide
  have hdescent : baseEnd_137172 < baseStart_137172 := by decide
  rcases family_descends (prefixWord ++ tailWord_137172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137200 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_137200 : Nat := 118140960795 + 137200 * 2 ^ 59
def prefixEnd_137200 : Nat := 4983230072969 + 3 ^ 40 * 137200 * 2
def baseEnd_137200 : Nat := 62621818486194167172475

theorem tailTrace_137200 : CollatzResearch.WordTrace tailWord_137200 prefixEnd_137200 62621818486194167172475 := by
  unfold tailWord_137200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2502047551477653369800527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3336063401970204493067369 2502047551477653369800527)
  ·
    refine ⟨3753071327216480054700791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2502047551477653369800527 3753071327216480054700791)
    ·
      refine ⟨5629606990824720082051187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3753071327216480054700791 5629606990824720082051187)
      ·
        refine ⟨8444410486237080123076781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5629606990824720082051187 8444410486237080123076781)
        ·
          refine ⟨3166653932338905046153793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8444410486237080123076781 3166653932338905046153793)
          ·
            refine ⟨2374990449254178784615345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166653932338905046153793 2374990449254178784615345)
            ·
              refine ⟨1781242836940634088461509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374990449254178784615345 1781242836940634088461509)
              ·
                refine ⟨333983031926368891586533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1781242836940634088461509 333983031926368891586533)
                ·
                  refine ⟨62621818486194167172475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333983031926368891586533 62621818486194167172475)
                  ·
                    rfl

theorem cell20_137200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_137200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137200 prefixEnd_137200 := by exact prefixLift 137200
  have htrace : WordTrace (prefixWord ++ tailWord_137200) baseStart_137200 baseEnd_137200 := by
    simpa [prefixWord, tailWord_137200, baseEnd_137200] using wordTrace_append hprefix tailTrace_137200
  have hstable : (prefixWord ++ tailWord_137200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137200).length < 2 ^ (prefixWord ++ tailWord_137200).sum := by decide
  have hdescent : baseEnd_137200 < baseStart_137200 := by decide
  rcases family_descends (prefixWord ++ tailWord_137200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137222 : List Nat := [6, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_137222 : Nat := 118140960795 + 137222 * 2 ^ 59
def prefixEnd_137222 : Nat := 4983230072969 + 3 ^ 40 * 137222 * 2
def baseEnd_137222 : Nat := 62631859885659868439053

theorem tailTrace_137222 : CollatzResearch.WordTrace tailWord_137222 prefixEnd_137222 62631859885659868439053 := by
  unfold tailWord_137222
  simp only [CollatzResearch.WordTrace]
  refine ⟨156403047152362640528185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3336598339250402997934613 156403047152362640528185)
  ·
    refine ⟨117302285364271980396139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156403047152362640528185 117302285364271980396139)
    ·
      refine ⟨175953428046407970594209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117302285364271980396139 175953428046407970594209)
      ·
        refine ⟨131965071034805977945657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175953428046407970594209 131965071034805977945657)
        ·
          refine ⟨98973803276104483459243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131965071034805977945657 98973803276104483459243)
          ·
            refine ⟨148460704914156725188865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98973803276104483459243 148460704914156725188865)
            ·
              refine ⟨111345528685617543891649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148460704914156725188865 111345528685617543891649)
              ·
                refine ⟨83509146514213157918737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111345528685617543891649 83509146514213157918737)
                ·
                  refine ⟨62631859885659868439053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83509146514213157918737 62631859885659868439053)
                  ·
                    rfl

theorem cell20_137222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_137222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137222 prefixEnd_137222 := by exact prefixLift 137222
  have htrace : WordTrace (prefixWord ++ tailWord_137222) baseStart_137222 baseEnd_137222 := by
    simpa [prefixWord, tailWord_137222, baseEnd_137222] using wordTrace_append hprefix tailTrace_137222
  have hstable : (prefixWord ++ tailWord_137222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137222).length < 2 ^ (prefixWord ++ tailWord_137222).sum := by decide
  have hdescent : baseEnd_137222 < baseStart_137222 := by decide
  rcases family_descends (prefixWord ++ tailWord_137222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137268 : List Nat := [2, 5, 1, 2, 2, 1, 2, 3, 2]
def baseStart_137268 : Nat := 118140960795 + 137268 * 2 ^ 59
def prefixEnd_137268 : Nat := 4983230072969 + 3 ^ 40 * 137268 * 2
def baseEnd_137268 : Nat := 62652855539088152905531

theorem tailTrace_137268 : CollatzResearch.WordTrace tailWord_137268 prefixEnd_137268 62652855539088152905531 := by
  unfold tailWord_137268
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503287633354477176538229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3337716844472636235384305 2503287633354477176538229)
  ·
    refine ⟨234683215626982235300459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2503287633354477176538229 234683215626982235300459)
    ·
      refine ⟨352024823440473352950689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234683215626982235300459 352024823440473352950689)
      ·
        refine ⟨264018617580355014713017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352024823440473352950689 264018617580355014713017)
        ·
          refine ⟨198013963185266261034763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264018617580355014713017 198013963185266261034763)
          ·
            refine ⟨297020944777899391552145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198013963185266261034763 297020944777899391552145)
            ·
              refine ⟨222765708583424543664109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297020944777899391552145 222765708583424543664109)
              ·
                refine ⟨83537140718784203874041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222765708583424543664109 83537140718784203874041)
                ·
                  refine ⟨62652855539088152905531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83537140718784203874041 62652855539088152905531)
                  ·
                    rfl

theorem cell20_137268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_137268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137268 prefixEnd_137268 := by exact prefixLift 137268
  have htrace : WordTrace (prefixWord ++ tailWord_137268) baseStart_137268 baseEnd_137268 := by
    simpa [prefixWord, tailWord_137268, baseEnd_137268] using wordTrace_append hprefix tailTrace_137268
  have hstable : (prefixWord ++ tailWord_137268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137268).length < 2 ^ (prefixWord ++ tailWord_137268).sum := by decide
  have hdescent : baseEnd_137268 < baseStart_137268 := by decide
  rcases family_descends (prefixWord ++ tailWord_137268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137276 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_137276 : Nat := 118140960795 + 137276 * 2 ^ 59
def prefixEnd_137276 : Nat := 4983230072969 + 3 ^ 40 * 137276 * 2
def baseEnd_137276 : Nat := 62656506957075680638831

theorem tailTrace_137276 : CollatzResearch.WordTrace tailWord_137276 prefixEnd_137276 62656506957075680638831 := by
  unfold tailWord_137276
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503433525339985859683841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3337911367119981146245121 2503433525339985859683841)
  ·
    refine ⟨1877575144004989394762881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2503433525339985859683841 1877575144004989394762881)
    ·
      refine ⟨1408181358003742046072161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1877575144004989394762881 1408181358003742046072161)
      ·
        refine ⟨1056136018502806534554121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1408181358003742046072161 1056136018502806534554121)
        ·
          refine ⟨792102013877104900915591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1056136018502806534554121 792102013877104900915591)
          ·
            refine ⟨1188153020815657351373387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792102013877104900915591 1188153020815657351373387)
            ·
              refine ⟨1782229531223486027060081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188153020815657351373387 1782229531223486027060081)
              ·
                refine ⟨1336672148417614520295061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782229531223486027060081 1336672148417614520295061)
                ·
                  refine ⟨62656506957075680638831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1336672148417614520295061 62656506957075680638831)
                  ·
                    rfl

theorem cell20_137276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_137276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137276 prefixEnd_137276 := by exact prefixLift 137276
  have htrace : WordTrace (prefixWord ++ tailWord_137276) baseStart_137276 baseEnd_137276 := by
    simpa [prefixWord, tailWord_137276, baseEnd_137276] using wordTrace_append hprefix tailTrace_137276
  have hstable : (prefixWord ++ tailWord_137276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137276).length < 2 ^ (prefixWord ++ tailWord_137276).sum := by decide
  have hdescent : baseEnd_137276 < baseStart_137276 := by decide
  rcases family_descends (prefixWord ++ tailWord_137276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137317 : List Nat := [1, 3, 1, 3, 2, 4, 2, 4]
def baseStart_137317 : Nat := 118140960795 + 137317 * 2 ^ 59
def prefixEnd_137317 : Nat := 4983230072969 + 3 ^ 40 * 137317 * 2
def baseEnd_137317 : Nat := 20891740158087253423999

theorem tailTrace_137317 : CollatzResearch.WordTrace tailWord_137317 prefixEnd_137317 20891740158087253423999 := by
  unfold tailWord_137317
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008362443531435721610205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3338908295687623814406803 5008362443531435721610205)
  ·
    refine ⟨1878135916324288395603827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5008362443531435721610205 1878135916324288395603827)
    ·
      refine ⟨2817203874486432593405741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1878135916324288395603827 2817203874486432593405741)
      ·
        refine ⟨1056451452932412222527153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2817203874486432593405741 1056451452932412222527153)
        ·
          refine ⟨792338589699309166895365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1056451452932412222527153 792338589699309166895365)
          ·
            refine ⟨148563485568620468792881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 792338589699309166895365 148563485568620468792881)
            ·
              refine ⟨111422614176465351594661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148563485568620468792881 111422614176465351594661)
              ·
                refine ⟨20891740158087253423999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111422614176465351594661 20891740158087253423999)
                ·
                  rfl

theorem cell20_137317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4].length) (baseStart_137317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137317 prefixEnd_137317 := by exact prefixLift 137317
  have htrace : WordTrace (prefixWord ++ tailWord_137317) baseStart_137317 baseEnd_137317 := by
    simpa [prefixWord, tailWord_137317, baseEnd_137317] using wordTrace_append hprefix tailTrace_137317
  have hstable : (prefixWord ++ tailWord_137317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137317).length < 2 ^ (prefixWord ++ tailWord_137317).sum := by decide
  have hdescent : baseEnd_137317 < baseStart_137317 := by decide
  rcases family_descends (prefixWord ++ tailWord_137317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137321 : List Nat := [1, 2, 1, 1, 1, 5, 3, 6]
def baseStart_137321 : Nat := 118140960795 + 137321 * 2 ^ 59
def prefixEnd_137321 : Nat := 4983230072969 + 3 ^ 40 * 137321 * 2
def baseEnd_137321 : Nat := 20892348727751841379549

theorem tailTrace_137321 : CollatzResearch.WordTrace tailWord_137321 prefixEnd_137321 20892348727751841379549 := by
  unfold tailWord_137321
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008508335516944404755817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3339005557011296269837211 5008508335516944404755817)
  ·
    refine ⟨3756381251637708303566863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5008508335516944404755817 3756381251637708303566863)
    ·
      refine ⟨5634571877456562455350295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3756381251637708303566863 5634571877456562455350295)
      ·
        refine ⟨8451857816184843683025443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5634571877456562455350295 8451857816184843683025443)
        ·
          refine ⟨12677786724277265524538165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8451857816184843683025443 12677786724277265524538165)
          ·
            refine ⟨1188542505400993642925453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12677786724277265524538165 1188542505400993642925453)
            ·
              refine ⟨445703439525372616097045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1188542505400993642925453 445703439525372616097045)
              ·
                refine ⟨20892348727751841379549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 445703439525372616097045 20892348727751841379549)
                ·
                  rfl

theorem cell20_137321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_137321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137321 prefixEnd_137321 := by exact prefixLift 137321
  have htrace : WordTrace (prefixWord ++ tailWord_137321) baseStart_137321 baseEnd_137321 := by
    simpa [prefixWord, tailWord_137321, baseEnd_137321] using wordTrace_append hprefix tailTrace_137321
  have hstable : (prefixWord ++ tailWord_137321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137321).length < 2 ^ (prefixWord ++ tailWord_137321).sum := by decide
  have hdescent : baseEnd_137321 < baseStart_137321 := by decide
  rcases family_descends (prefixWord ++ tailWord_137321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137358 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_137358 : Nat := 118140960795 + 137358 * 2 ^ 59
def prefixEnd_137358 : Nat := 4983230072969 + 3 ^ 40 * 137358 * 2
def baseEnd_137358 : Nat := 62693933991447839905163

theorem tailTrace_137358 : CollatzResearch.WordTrace tailWord_137358 prefixEnd_137358 62693933991447839905163 := by
  unfold tailWord_137358
  simp only [CollatzResearch.WordTrace]
  refine ⟨626232229547862465481591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3339905224255266482568485 626232229547862465481591)
  ·
    refine ⟨939348344321793698222387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 626232229547862465481591 939348344321793698222387)
    ·
      refine ⟨1409022516482690547333581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939348344321793698222387 1409022516482690547333581)
      ·
        refine ⟨528383443681008955250093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1409022516482690547333581 528383443681008955250093)
        ·
          refine ⟨198143791380378358218785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 528383443681008955250093 198143791380378358218785)
          ·
            refine ⟨148607843535283768664089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198143791380378358218785 148607843535283768664089)
            ·
              refine ⟨111455882651462826498067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148607843535283768664089 111455882651462826498067)
              ·
                refine ⟨167183823977194239747101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111455882651462826498067 167183823977194239747101)
                ·
                  refine ⟨62693933991447839905163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167183823977194239747101 62693933991447839905163)
                  ·
                    rfl

theorem cell20_137358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_137358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137358 prefixEnd_137358 := by exact prefixLift 137358
  have htrace : WordTrace (prefixWord ++ tailWord_137358) baseStart_137358 baseEnd_137358 := by
    simpa [prefixWord, tailWord_137358, baseEnd_137358] using wordTrace_append hprefix tailTrace_137358
  have hstable : (prefixWord ++ tailWord_137358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137358).length < 2 ^ (prefixWord ++ tailWord_137358).sum := by decide
  have hdescent : baseEnd_137358 < baseStart_137358 := by decide
  rcases family_descends (prefixWord ++ tailWord_137358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137362 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_137362 : Nat := 118140960795 + 137362 * 2 ^ 59
def prefixEnd_137362 : Nat := 4983230072969 + 3 ^ 40 * 137362 * 2
def baseEnd_137362 : Nat := 62695759700441603771813

theorem tailTrace_137362 : CollatzResearch.WordTrace tailWord_137362 prefixEnd_137362 62695759700441603771813 := by
  unfold tailWord_137362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252500932092102101749585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3340002485578938937998893 1252500932092102101749585)
  ·
    refine ⟨939375699069076576312189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1252500932092102101749585 939375699069076576312189)
    ·
      refine ⟨352265887150903716117071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 939375699069076576312189 352265887150903716117071)
      ·
        refine ⟨528398830726355574175607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352265887150903716117071 528398830726355574175607)
        ·
          refine ⟨792598246089533361263411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528398830726355574175607 792598246089533361263411)
          ·
            refine ⟨1188897369134300041895117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792598246089533361263411 1188897369134300041895117)
            ·
              refine ⟨445836513425362515710669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1188897369134300041895117 445836513425362515710669)
              ·
                refine ⟨167188692534510943391501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 445836513425362515710669 167188692534510943391501)
                ·
                  refine ⟨62695759700441603771813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167188692534510943391501 62695759700441603771813)
                  ·
                    rfl

theorem cell20_137362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_137362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137362 prefixEnd_137362 := by exact prefixLift 137362
  have htrace : WordTrace (prefixWord ++ tailWord_137362) baseStart_137362 baseEnd_137362 := by
    simpa [prefixWord, tailWord_137362, baseEnd_137362] using wordTrace_append hprefix tailTrace_137362
  have hstable : (prefixWord ++ tailWord_137362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137362).length < 2 ^ (prefixWord ++ tailWord_137362).sum := by decide
  have hdescent : baseEnd_137362 < baseStart_137362 := by decide
  rcases family_descends (prefixWord ++ tailWord_137362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137410 : List Nat := [3, 5, 1, 1, 1, 1, 3, 5]
def baseStart_137410 : Nat := 118140960795 + 137410 * 2 ^ 59
def prefixEnd_137410 : Nat := 4983230072969 + 3 ^ 40 * 137410 * 2
def baseEnd_137410 : Nat := 20905889402788923390539

theorem tailTrace_137410 : CollatzResearch.WordTrace tailWord_137410 prefixEnd_137410 20905889402788923390539 := by
  unfold tailWord_137410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252938608048628151186421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3341169621463008403163789 1252938608048628151186421)
  ·
    refine ⟨117462994504558889173727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1252938608048628151186421 117462994504558889173727)
    ·
      refine ⟨176194491756838333760591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117462994504558889173727 176194491756838333760591)
      ·
        refine ⟨264291737635257500640887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176194491756838333760591 264291737635257500640887)
        ·
          refine ⟨396437606452886250961331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264291737635257500640887 396437606452886250961331)
          ·
            refine ⟨594656409679329376441997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396437606452886250961331 594656409679329376441997)
            ·
              refine ⟨222996153629748516165749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 594656409679329376441997 222996153629748516165749)
              ·
                refine ⟨20905889402788923390539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222996153629748516165749 20905889402788923390539)
                ·
                  rfl

theorem cell20_137410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_137410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137410 prefixEnd_137410 := by exact prefixLift 137410
  have htrace : WordTrace (prefixWord ++ tailWord_137410) baseStart_137410 baseEnd_137410 := by
    simpa [prefixWord, tailWord_137410, baseEnd_137410] using wordTrace_append hprefix tailTrace_137410
  have hstable : (prefixWord ++ tailWord_137410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137410).length < 2 ^ (prefixWord ++ tailWord_137410).sum := by decide
  have hdescent : baseEnd_137410 < baseStart_137410 := by decide
  rcases family_descends (prefixWord ++ tailWord_137410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137462 : List Nat := [5, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_137462 : Nat := 118140960795 + 137462 * 2 ^ 59
def prefixEnd_137462 : Nat := 4983230072969 + 3 ^ 40 * 137462 * 2
def baseEnd_137462 : Nat := 62741402425285700438071

theorem tailTrace_137462 : CollatzResearch.WordTrace tailWord_137462 prefixEnd_137462 62741402425285700438071 := by
  unfold tailWord_137462
  simp only [CollatzResearch.WordTrace]
  refine ⟨313353189250382842852415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3342434018670750323759093 313353189250382842852415)
  ·
    refine ⟨470029783875574264278623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 313353189250382842852415 470029783875574264278623)
    ·
      refine ⟨705044675813361396417935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470029783875574264278623 705044675813361396417935)
      ·
        refine ⟨1057567013720042094626903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705044675813361396417935 1057567013720042094626903)
        ·
          refine ⟨1586350520580063141940355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057567013720042094626903 1586350520580063141940355)
          ·
            refine ⟨2379525780870094712910533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586350520580063141940355 2379525780870094712910533)
            ·
              refine ⟨446161083913142758670725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2379525780870094712910533 446161083913142758670725)
              ·
                refine ⟨83655203233714267250761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446161083913142758670725 83655203233714267250761)
                ·
                  refine ⟨62741402425285700438071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83655203233714267250761 62741402425285700438071)
                  ·
                    rfl

theorem cell20_137462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_137462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137462 prefixEnd_137462 := by exact prefixLift 137462
  have htrace : WordTrace (prefixWord ++ tailWord_137462) baseStart_137462 baseEnd_137462 := by
    simpa [prefixWord, tailWord_137462, baseEnd_137462] using wordTrace_append hprefix tailTrace_137462
  have hstable : (prefixWord ++ tailWord_137462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137462).length < 2 ^ (prefixWord ++ tailWord_137462).sum := by decide
  have hdescent : baseEnd_137462 < baseStart_137462 := by decide
  rcases family_descends (prefixWord ++ tailWord_137462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137466 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_137466 : Nat := 118140960795 + 137466 * 2 ^ 59
def prefixEnd_137466 : Nat := 4983230072969 + 3 ^ 40 * 137466 * 2
def baseEnd_137466 : Nat := 62743228134279464304721

theorem tailTrace_137466 : CollatzResearch.WordTrace tailWord_137466 prefixEnd_137466 62743228134279464304721 := by
  unfold tailWord_137466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253449229997908542196063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3342531279994422779189501 1253449229997908542196063)
  ·
    refine ⟨1880173844996862813294095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1253449229997908542196063 1880173844996862813294095)
    ·
      refine ⟨2820260767495294219941143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880173844996862813294095 2820260767495294219941143)
      ·
        refine ⟨4230391151242941329911715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820260767495294219941143 4230391151242941329911715)
        ·
          refine ⟨6345586726864411994867573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230391151242941329911715 6345586726864411994867573)
          ·
            refine ⟨594898755643538624518835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6345586726864411994867573 594898755643538624518835)
            ·
              refine ⟨892348133465307936778253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594898755643538624518835 892348133465307936778253)
              ·
                refine ⟨334630550049490476291845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 892348133465307936778253 334630550049490476291845)
                ·
                  refine ⟨62743228134279464304721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 334630550049490476291845 62743228134279464304721)
                  ·
                    rfl

theorem cell20_137466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_137466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137466 prefixEnd_137466 := by exact prefixLift 137466
  have htrace : WordTrace (prefixWord ++ tailWord_137466) baseStart_137466 baseEnd_137466 := by
    simpa [prefixWord, tailWord_137466, baseEnd_137466] using wordTrace_append hprefix tailTrace_137466
  have hstable : (prefixWord ++ tailWord_137466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137466).length < 2 ^ (prefixWord ++ tailWord_137466).sum := by decide
  have hdescent : baseEnd_137466 < baseStart_137466 := by decide
  rcases family_descends (prefixWord ++ tailWord_137466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137473 : List Nat := [1, 2, 4, 1, 1, 2, 2, 7]
def baseStart_137473 : Nat := 118140960795 + 137473 * 2 ^ 59
def prefixEnd_137473 : Nat := 4983230072969 + 3 ^ 40 * 137473 * 2
def baseEnd_137473 : Nat := 20915474375006183690453

theorem tailTrace_137473 : CollatzResearch.WordTrace tailWord_137473 prefixEnd_137473 20915474375006183690453 := by
  unfold tailWord_137473
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014052230966274364289073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3342701487310849576192715 5014052230966274364289073)
  ·
    refine ⟨3760539173224705773216805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5014052230966274364289073 3760539173224705773216805)
    ·
      refine ⟨705101094979632332478151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3760539173224705773216805 705101094979632332478151)
      ·
        refine ⟨1057651642469448498717227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705101094979632332478151 1057651642469448498717227)
        ·
          refine ⟨1586477463704172748075841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057651642469448498717227 1586477463704172748075841)
          ·
            refine ⟨1189858097778129561056881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1586477463704172748075841 1189858097778129561056881)
            ·
              refine ⟨892393573333597170792661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189858097778129561056881 892393573333597170792661)
              ·
                refine ⟨20915474375006183690453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 892393573333597170792661 20915474375006183690453)
                ·
                  rfl

theorem cell20_137473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_137473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137473 prefixEnd_137473 := by exact prefixLift 137473
  have htrace : WordTrace (prefixWord ++ tailWord_137473) baseStart_137473 baseEnd_137473 := by
    simpa [prefixWord, tailWord_137473, baseEnd_137473] using wordTrace_append hprefix tailTrace_137473
  have hstable : (prefixWord ++ tailWord_137473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137473).length < 2 ^ (prefixWord ++ tailWord_137473).sum := by decide
  have hdescent : baseEnd_137473 < baseStart_137473 := by decide
  rcases family_descends (prefixWord ++ tailWord_137473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137517 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 4]
def baseStart_137517 : Nat := 118140960795 + 137517 * 2 ^ 59
def prefixEnd_137517 : Nat := 4983230072969 + 3 ^ 40 * 137517 * 2
def baseEnd_137517 : Nat := 62766505923949953604513

theorem tailTrace_137517 : CollatzResearch.WordTrace tailWord_137517 prefixEnd_137517 62766505923949953604513 := by
  unfold tailWord_137517
  simp only [CollatzResearch.WordTrace]
  refine ⟨5015657042806869878890805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3343771361871246585927203 5015657042806869878890805)
  ·
    refine ⟨470217847763144051146013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5015657042806869878890805 470217847763144051146013)
    ·
      refine ⟨176331692911179019179755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 470217847763144051146013 176331692911179019179755)
      ·
        refine ⟨264497539366768528769633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176331692911179019179755 264497539366768528769633)
        ·
          refine ⟨198373154525076396577225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264497539366768528769633 198373154525076396577225)
          ·
            refine ⟨148779865893807297432919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198373154525076396577225 148779865893807297432919)
            ·
              refine ⟨223169798840710946149379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148779865893807297432919 223169798840710946149379)
              ·
                refine ⟨334754698261066419224069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223169798840710946149379 334754698261066419224069)
                ·
                  refine ⟨62766505923949953604513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 334754698261066419224069 62766505923949953604513)
                  ·
                    rfl

theorem cell20_137517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_137517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137517 prefixEnd_137517 := by exact prefixLift 137517
  have htrace : WordTrace (prefixWord ++ tailWord_137517) baseStart_137517 baseEnd_137517 := by
    simpa [prefixWord, tailWord_137517, baseEnd_137517] using wordTrace_append hprefix tailTrace_137517
  have hstable : (prefixWord ++ tailWord_137517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137517).length < 2 ^ (prefixWord ++ tailWord_137517).sum := by decide
  have hdescent : baseEnd_137517 < baseStart_137517 := by decide
  rcases family_descends (prefixWord ++ tailWord_137517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137535 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 3]
def baseStart_137535 : Nat := 118140960795 + 137535 * 2 ^ 59
def prefixEnd_137535 : Nat := 4983230072969 + 3 ^ 40 * 137535 * 2
def baseEnd_137535 : Nat := 62774721614421891004439

theorem tailTrace_137535 : CollatzResearch.WordTrace tailWord_137535 prefixEnd_137535 62774721614421891004439 := by
  unfold tailWord_137535
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016313556741658953046059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3344209037827772635364039 5016313556741658953046059)
  ·
    refine ⟨7524470335112488429569089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5016313556741658953046059 7524470335112488429569089)
    ·
      refine ⟨5643352751334366322176817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7524470335112488429569089 5643352751334366322176817)
      ·
        refine ⟨4232514563500774741632613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5643352751334366322176817 4232514563500774741632613)
        ·
          refine ⟨793596480656395264056115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4232514563500774741632613 793596480656395264056115)
          ·
            refine ⟨1190394720984592896084173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793596480656395264056115 1190394720984592896084173)
            ·
              refine ⟨446398020369222336031565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1190394720984592896084173 446398020369222336031565)
              ·
                refine ⟨167399257638458376011837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446398020369222336031565 167399257638458376011837)
                ·
                  refine ⟨62774721614421891004439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167399257638458376011837 62774721614421891004439)
                  ·
                    rfl

theorem cell20_137535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 3].length) (baseStart_137535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137535 prefixEnd_137535 := by exact prefixLift 137535
  have htrace : WordTrace (prefixWord ++ tailWord_137535) baseStart_137535 baseEnd_137535 := by
    simpa [prefixWord, tailWord_137535, baseEnd_137535] using wordTrace_append hprefix tailTrace_137535
  have hstable : (prefixWord ++ tailWord_137535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137535).length < 2 ^ (prefixWord ++ tailWord_137535).sum := by decide
  have hdescent : baseEnd_137535 < baseStart_137535 := by decide
  rcases family_descends (prefixWord ++ tailWord_137535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137559 : List Nat := [1, 1, 3, 2, 3, 1, 2, 5, 2]
def baseStart_137559 : Nat := 118140960795 + 137559 * 2 ^ 59
def prefixEnd_137559 : Nat := 4983230072969 + 3 ^ 40 * 137559 * 2
def baseEnd_137559 : Nat := 62785675868384474204341

theorem tailTrace_137559 : CollatzResearch.WordTrace tailWord_137559 prefixEnd_137559 62785675868384474204341 := by
  unfold tailWord_137559
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017188908654711051919731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3344792605769807367946487 5017188908654711051919731)
  ·
    refine ⟨7525783362982066577879597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5017188908654711051919731 7525783362982066577879597)
    ·
      refine ⟨2822168761118274966704849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7525783362982066577879597 2822168761118274966704849)
      ·
        refine ⟨2116626570838706225028637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2822168761118274966704849 2116626570838706225028637)
        ·
          refine ⟨793734964064514834385739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2116626570838706225028637 793734964064514834385739)
          ·
            refine ⟨1190602446096772251578609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793734964064514834385739 1190602446096772251578609)
            ·
              refine ⟨892951834572579188683957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190602446096772251578609 892951834572579188683957)
              ·
                refine ⟨83714234491179298939121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 892951834572579188683957 83714234491179298939121)
                ·
                  refine ⟨62785675868384474204341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83714234491179298939121 62785675868384474204341)
                  ·
                    rfl

theorem cell20_137559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 2].length) (baseStart_137559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137559 prefixEnd_137559 := by exact prefixLift 137559
  have htrace : WordTrace (prefixWord ++ tailWord_137559) baseStart_137559 baseEnd_137559 := by
    simpa [prefixWord, tailWord_137559, baseEnd_137559] using wordTrace_append hprefix tailTrace_137559
  have hstable : (prefixWord ++ tailWord_137559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137559).length < 2 ^ (prefixWord ++ tailWord_137559).sum := by decide
  have hdescent : baseEnd_137559 < baseStart_137559 := by decide
  rcases family_descends (prefixWord ++ tailWord_137559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137573 : List Nat := [1, 3, 1, 3, 1, 3, 1, 4, 3]
def baseStart_137573 : Nat := 118140960795 + 137573 * 2 ^ 59
def prefixEnd_137573 : Nat := 4983230072969 + 3 ^ 40 * 137573 * 2
def baseEnd_137573 : Nat := 62792065849862647737617

theorem tailTrace_137573 : CollatzResearch.WordTrace tailWord_137573 prefixEnd_137573 62792065849862647737617 := by
  unfold tailWord_137573
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017699530603991442929373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3345133020402660961952915 5017699530603991442929373)
  ·
    refine ⟨1881637323976496791098515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5017699530603991442929373 1881637323976496791098515)
    ·
      refine ⟨2822455985964745186647773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881637323976496791098515 2822455985964745186647773)
      ·
        refine ⟨1058420994736779444992915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2822455985964745186647773 1058420994736779444992915)
        ·
          refine ⟨1587631492105169167489373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058420994736779444992915 1587631492105169167489373)
          ·
            refine ⟨595361809539438437808515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1587631492105169167489373 595361809539438437808515)
            ·
              refine ⟨893042714309157656712773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595361809539438437808515 893042714309157656712773)
              ·
                refine ⟨167445508932967060633645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 893042714309157656712773 167445508932967060633645)
                ·
                  refine ⟨62792065849862647737617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167445508932967060633645 62792065849862647737617)
                  ·
                    rfl

theorem cell20_137573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_137573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137573 prefixEnd_137573 := by exact prefixLift 137573
  have htrace : WordTrace (prefixWord ++ tailWord_137573) baseStart_137573 baseEnd_137573 := by
    simpa [prefixWord, tailWord_137573, baseEnd_137573] using wordTrace_append hprefix tailTrace_137573
  have hstable : (prefixWord ++ tailWord_137573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137573).length < 2 ^ (prefixWord ++ tailWord_137573).sum := by decide
  have hdescent : baseEnd_137573 < baseStart_137573 := by decide
  rcases family_descends (prefixWord ++ tailWord_137573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137576 : List Nat := [2, 1, 4, 2, 2, 2, 1, 4, 2]
def baseStart_137576 : Nat := 118140960795 + 137576 * 2 ^ 59
def prefixEnd_137576 : Nat := 4983230072969 + 3 ^ 40 * 137576 * 2
def baseEnd_137576 : Nat := 62793435131607970637605

theorem tailTrace_137576 : CollatzResearch.WordTrace tailWord_137576 prefixEnd_137576 62793435131607970637605 := by
  unfold tailWord_137576
  simp only [CollatzResearch.WordTrace]
  refine ⟨2508904474796561477644291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3345205966395415303525721 2508904474796561477644291)
  ·
    refine ⟨3763356712194842216466437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2508904474796561477644291 3763356712194842216466437)
    ·
      refine ⟨705629383536532915587457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3763356712194842216466437 705629383536532915587457)
      ·
        refine ⟨529222037652399686690593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 705629383536532915587457 529222037652399686690593)
        ·
          refine ⟨396916528239299765017945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529222037652399686690593 396916528239299765017945)
          ·
            refine ⟨297687396179474823763459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396916528239299765017945 297687396179474823763459)
            ·
              refine ⟨446531094269212235645189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297687396179474823763459 446531094269212235645189)
              ·
                refine ⟨83724580175477294183473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446531094269212235645189 83724580175477294183473)
                ·
                  refine ⟨62793435131607970637605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83724580175477294183473 62793435131607970637605)
                  ·
                    rfl

theorem cell20_137576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_137576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137576 prefixEnd_137576 := by exact prefixLift 137576
  have htrace : WordTrace (prefixWord ++ tailWord_137576) baseStart_137576 baseEnd_137576 := by
    simpa [prefixWord, tailWord_137576, baseEnd_137576] using wordTrace_append hprefix tailTrace_137576
  have hstable : (prefixWord ++ tailWord_137576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137576).length < 2 ^ (prefixWord ++ tailWord_137576).sum := by decide
  have hdescent : baseEnd_137576 < baseStart_137576 := by decide
  rcases family_descends (prefixWord ++ tailWord_137576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137604 : List Nat := [2, 3, 2, 1, 1, 2, 5, 4]
def baseStart_137604 : Nat := 118140960795 + 137604 * 2 ^ 59
def prefixEnd_137604 : Nat := 4983230072969 + 3 ^ 40 * 137604 * 2
def baseEnd_137604 : Nat := 20935405031521439234719

theorem tailTrace_137604 : CollatzResearch.WordTrace tailWord_137604 prefixEnd_137604 20935405031521439234719 := by
  unfold tailWord_137604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509415096745841868653933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3345886795661122491538577 2509415096745841868653933)
  ·
    refine ⟨941030661279690700745225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2509415096745841868653933 941030661279690700745225)
    ·
      refine ⟨705772995959768025558919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 941030661279690700745225 705772995959768025558919)
      ·
        refine ⟨1058659493939652038338379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705772995959768025558919 1058659493939652038338379)
        ·
          refine ⟨1587989240909478057507569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058659493939652038338379 1587989240909478057507569)
          ·
            refine ⟨1190991930682108543130677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587989240909478057507569 1190991930682108543130677)
            ·
              refine ⟨111655493501447675918501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1190991930682108543130677 111655493501447675918501)
              ·
                refine ⟨20935405031521439234719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111655493501447675918501 20935405031521439234719)
                ·
                  rfl

theorem cell20_137604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_137604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137604 prefixEnd_137604 := by exact prefixLift 137604
  have htrace : WordTrace (prefixWord ++ tailWord_137604) baseStart_137604 baseEnd_137604 := by
    simpa [prefixWord, tailWord_137604, baseEnd_137604] using wordTrace_append hprefix tailTrace_137604
  have hstable : (prefixWord ++ tailWord_137604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137604).length < 2 ^ (prefixWord ++ tailWord_137604).sum := by decide
  have hdescent : baseEnd_137604 < baseStart_137604 := by decide
  rcases family_descends (prefixWord ++ tailWord_137604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137614 : List Nat := [4, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_137614 : Nat := 118140960795 + 137614 * 2 ^ 59
def prefixEnd_137614 : Nat := 4983230072969 + 3 ^ 40 * 137614 * 2
def baseEnd_137614 : Nat := 62810779367048727370783

theorem tailTrace_137614 : CollatzResearch.WordTrace tailWord_137614 prefixEnd_137614 62810779367048727370783 := by
  unfold tailWord_137614
  simp only [CollatzResearch.WordTrace]
  refine ⟨627399365431931930646487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3346129948970303630114597 627399365431931930646487)
  ·
    refine ⟨941099048147897895969731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627399365431931930646487 941099048147897895969731)
    ·
      refine ⟨1411648572221846843954597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941099048147897895969731 1411648572221846843954597)
      ·
        refine ⟨264684107291596283241487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1411648572221846843954597 264684107291596283241487)
        ·
          refine ⟨397026160937394424862231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264684107291596283241487 397026160937394424862231)
          ·
            refine ⟨595539241406091637293347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397026160937394424862231 595539241406091637293347)
            ·
              refine ⟨893308862109137455940021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595539241406091637293347 893308862109137455940021)
              ·
                refine ⟨83747705822731636494377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 893308862109137455940021 83747705822731636494377)
                ·
                  refine ⟨62810779367048727370783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83747705822731636494377 62810779367048727370783)
                  ·
                    rfl

theorem cell20_137614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_137614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137614 prefixEnd_137614 := by exact prefixLift 137614
  have htrace : WordTrace (prefixWord ++ tailWord_137614) baseStart_137614 baseEnd_137614 := by
    simpa [prefixWord, tailWord_137614, baseEnd_137614] using wordTrace_append hprefix tailTrace_137614
  have hstable : (prefixWord ++ tailWord_137614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137614).length < 2 ^ (prefixWord ++ tailWord_137614).sum := by decide
  have hdescent : baseEnd_137614 < baseStart_137614 := by decide
  rcases family_descends (prefixWord ++ tailWord_137614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137635 : List Nat := [1, 1, 1, 4, 1, 4, 2, 4, 2]
def baseStart_137635 : Nat := 118140960795 + 137635 * 2 ^ 59
def prefixEnd_137635 : Nat := 4983230072969 + 3 ^ 40 * 137635 * 2
def baseEnd_137635 : Nat := 62820364339265987670697

theorem tailTrace_137635 : CollatzResearch.WordTrace tailWord_137635 prefixEnd_137635 62820364339265987670697 := by
  unfold tailWord_137635
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019960856379376031686359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3346640570919584021124239 5019960856379376031686359)
  ·
    refine ⟨7529941284569064047529539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5019960856379376031686359 7529941284569064047529539)
    ·
      refine ⟨11294911926853596071294309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7529941284569064047529539 11294911926853596071294309)
      ·
        refine ⟨2117795986285049263367683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11294911926853596071294309 2117795986285049263367683)
        ·
          refine ⟨3176693979427573895051525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117795986285049263367683 3176693979427573895051525)
          ·
            refine ⟨595630121142670105322161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3176693979427573895051525 595630121142670105322161)
            ·
              refine ⟨446722590857002578991621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595630121142670105322161 446722590857002578991621)
              ·
                refine ⟨83760485785687983560929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 446722590857002578991621 83760485785687983560929)
                ·
                  refine ⟨62820364339265987670697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83760485785687983560929 62820364339265987670697)
                  ·
                    rfl

theorem cell20_137635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 4, 2].length) (baseStart_137635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137635 prefixEnd_137635 := by exact prefixLift 137635
  have htrace : WordTrace (prefixWord ++ tailWord_137635) baseStart_137635 baseEnd_137635 := by
    simpa [prefixWord, tailWord_137635, baseEnd_137635] using wordTrace_append hprefix tailTrace_137635
  have hstable : (prefixWord ++ tailWord_137635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137635).length < 2 ^ (prefixWord ++ tailWord_137635).sum := by decide
  have hdescent : baseEnd_137635 < baseStart_137635 := by decide
  rcases family_descends (prefixWord ++ tailWord_137635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137665 : List Nat := [1, 2, 7, 1, 1, 2, 1, 3, 2]
def baseStart_137665 : Nat := 118140960795 + 137665 * 2 ^ 59
def prefixEnd_137665 : Nat := 4983230072969 + 3 ^ 40 * 137665 * 2
def baseEnd_137665 : Nat := 62834057156719216670575

theorem tailTrace_137665 : CollatzResearch.WordTrace tailWord_137665 prefixEnd_137665 62834057156719216670575 := by
  unfold tailWord_137665
  simp only [CollatzResearch.WordTrace]
  refine ⟨5021055046270691155278449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3347370030847127436852299 5021055046270691155278449)
  ·
    refine ⟨3765791284703018366458837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5021055046270691155278449 3765791284703018366458837)
    ·
      refine ⟨88260733235226992963879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3765791284703018366458837 88260733235226992963879)
      ·
        refine ⟨132391099852840489445819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88260733235226992963879 132391099852840489445819)
        ·
          refine ⟨198586649779260734168729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132391099852840489445819 198586649779260734168729)
          ·
            refine ⟨148939987334445550626547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198586649779260734168729 148939987334445550626547)
            ·
              refine ⟨223409981001668325939821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148939987334445550626547 223409981001668325939821)
              ·
                refine ⟨83778742875625622227433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223409981001668325939821 83778742875625622227433)
                ·
                  refine ⟨62834057156719216670575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83778742875625622227433 62834057156719216670575)
                  ·
                    rfl

theorem cell20_137665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_137665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137665 prefixEnd_137665 := by exact prefixLift 137665
  have htrace : WordTrace (prefixWord ++ tailWord_137665) baseStart_137665 baseEnd_137665 := by
    simpa [prefixWord, tailWord_137665, baseEnd_137665] using wordTrace_append hprefix tailTrace_137665
  have hstable : (prefixWord ++ tailWord_137665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137665).length < 2 ^ (prefixWord ++ tailWord_137665).sum := by decide
  have hdescent : baseEnd_137665 < baseStart_137665 := by decide
  rcases family_descends (prefixWord ++ tailWord_137665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137673 : List Nat := [1, 2, 1, 1, 2, 1, 7, 3, 2]
def baseStart_137673 : Nat := 118140960795 + 137673 * 2 ^ 59
def prefixEnd_137673 : Nat := 4983230072969 + 3 ^ 40 * 137673 * 2
def baseEnd_137673 : Nat := 62837708574706744403875

theorem tailTrace_137673 : CollatzResearch.WordTrace tailWord_137673 prefixEnd_137673 62837708574706744403875 := by
  unfold tailWord_137673
  simp only [CollatzResearch.WordTrace]
  refine ⟨5021346830241708521569673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3347564553494472347713115 5021346830241708521569673)
  ·
    refine ⟨3766010122681281391177255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5021346830241708521569673 3766010122681281391177255)
    ·
      refine ⟨5649015184021922086765883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3766010122681281391177255 5649015184021922086765883)
      ·
        refine ⟨8473522776032883130148825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5649015184021922086765883 8473522776032883130148825)
        ·
          refine ⟨6355142082024662347611619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8473522776032883130148825 6355142082024662347611619)
          ·
            refine ⟨9532713123036993521417429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6355142082024662347611619 9532713123036993521417429)
            ·
              refine ⟨223422963821179535658221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9532713123036993521417429 223422963821179535658221)
              ·
                refine ⟨83783611432942325871833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223422963821179535658221 83783611432942325871833)
                ·
                  refine ⟨62837708574706744403875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83783611432942325871833 62837708574706744403875)
                  ·
                    rfl

theorem cell20_137673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_137673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137673 prefixEnd_137673 := by exact prefixLift 137673
  have htrace : WordTrace (prefixWord ++ tailWord_137673) baseStart_137673 baseEnd_137673 := by
    simpa [prefixWord, tailWord_137673, baseEnd_137673] using wordTrace_append hprefix tailTrace_137673
  have hstable : (prefixWord ++ tailWord_137673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137673).length < 2 ^ (prefixWord ++ tailWord_137673).sum := by decide
  have hdescent : baseEnd_137673 < baseStart_137673 := by decide
  rcases family_descends (prefixWord ++ tailWord_137673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137690 : List Nat := [3, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_137690 : Nat := 118140960795 + 137690 * 2 ^ 59
def prefixEnd_137690 : Nat := 4983230072969 + 3 ^ 40 * 137690 * 2
def baseEnd_137690 : Nat := 62845467837930240837139

theorem tailTrace_137690 : CollatzResearch.WordTrace tailWord_137690 prefixEnd_137690 62845467837930240837139 := by
  unfold tailWord_137690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1255491717795030106234631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3347977914120080283292349 1255491717795030106234631)
  ·
    refine ⟨1883237576692545159351947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1255491717795030106234631 1883237576692545159351947)
    ·
      refine ⟨2824856365038817739027921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1883237576692545159351947 2824856365038817739027921)
      ·
        refine ⟨2118642273779113304270941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2824856365038817739027921 2118642273779113304270941)
        ·
          refine ⟨794490852667167489101603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2118642273779113304270941 794490852667167489101603)
          ·
            refine ⟨1191736279000751233652405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794490852667167489101603 1191736279000751233652405)
            ·
              refine ⟨111725276156320428154913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1191736279000751233652405 111725276156320428154913)
              ·
                refine ⟨83793957117240321116185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111725276156320428154913 83793957117240321116185)
                ·
                  refine ⟨62845467837930240837139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83793957117240321116185 62845467837930240837139)
                  ·
                    rfl

theorem cell20_137690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_137690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137690 prefixEnd_137690 := by exact prefixLift 137690
  have htrace : WordTrace (prefixWord ++ tailWord_137690) baseStart_137690 baseEnd_137690 := by
    simpa [prefixWord, tailWord_137690, baseEnd_137690] using wordTrace_append hprefix tailTrace_137690
  have hstable : (prefixWord ++ tailWord_137690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137690).length < 2 ^ (prefixWord ++ tailWord_137690).sum := by decide
  have hdescent : baseEnd_137690 < baseStart_137690 := by decide
  rcases family_descends (prefixWord ++ tailWord_137690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137704 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 3]
def baseStart_137704 : Nat := 118140960795 + 137704 * 2 ^ 59
def prefixEnd_137704 : Nat := 4983230072969 + 3 ^ 40 * 137704 * 2
def baseEnd_137704 : Nat := 62851857819408414370415

theorem tailTrace_137704 : CollatzResearch.WordTrace tailWord_137704 prefixEnd_137704 62851857819408414370415 := by
  unfold tailWord_137704
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511238746564700407974083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3348318328752933877298777 2511238746564700407974083)
  ·
    refine ⟨3766858119847050611961125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2511238746564700407974083 3766858119847050611961125)
    ·
      refine ⟨706285897471321989742711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3766858119847050611961125 706285897471321989742711)
      ·
        refine ⟨1059428846206982984614067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706285897471321989742711 1059428846206982984614067)
        ·
          refine ⟨1589143269310474476921101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1059428846206982984614067 1589143269310474476921101)
          ·
            refine ⟨595928725991427928845413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1589143269310474476921101 595928725991427928845413)
            ·
              refine ⟨111736636123392736658515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 595928725991427928845413 111736636123392736658515)
              ·
                refine ⟨167604954185089104987773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111736636123392736658515 167604954185089104987773)
                ·
                  refine ⟨62851857819408414370415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167604954185089104987773 62851857819408414370415)
                  ·
                    rfl

theorem cell20_137704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_137704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137704 prefixEnd_137704 := by exact prefixLift 137704
  have htrace : WordTrace (prefixWord ++ tailWord_137704) baseStart_137704 baseEnd_137704 := by
    simpa [prefixWord, tailWord_137704, baseEnd_137704] using wordTrace_append hprefix tailTrace_137704
  have hstable : (prefixWord ++ tailWord_137704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137704).length < 2 ^ (prefixWord ++ tailWord_137704).sum := by decide
  have hdescent : baseEnd_137704 < baseStart_137704 := by decide
  rcases family_descends (prefixWord ++ tailWord_137704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137715 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_137715 : Nat := 118140960795 + 137715 * 2 ^ 59
def prefixEnd_137715 : Nat := 4983230072969 + 3 ^ 40 * 137715 * 2
def baseEnd_137715 : Nat := 62856878519141265003703

theorem tailTrace_137715 : CollatzResearch.WordTrace tailWord_137715 prefixEnd_137715 62856878519141265003703 := by
  unfold tailWord_137715
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022878696089549694598599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3348585797393033129732399 5022878696089549694598599)
  ·
    refine ⟨7534318044134324541897899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5022878696089549694598599 7534318044134324541897899)
    ·
      refine ⟨11301477066201486812846849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7534318044134324541897899 11301477066201486812846849)
      ·
        refine ⟨8476107799651115109635137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11301477066201486812846849 8476107799651115109635137)
        ·
          refine ⟨6357080849738336332226353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8476107799651115109635137 6357080849738336332226353)
          ·
            refine ⟨4767810637303752249169765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6357080849738336332226353 4767810637303752249169765)
            ·
              refine ⟨893964494494453546719331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4767810637303752249169765 893964494494453546719331)
              ·
                refine ⟨1340946741741680320078997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893964494494453546719331 1340946741741680320078997)
                ·
                  refine ⟨62856878519141265003703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1340946741741680320078997 62856878519141265003703)
                  ·
                    rfl

theorem cell20_137715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_137715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137715 prefixEnd_137715 := by exact prefixLift 137715
  have htrace : WordTrace (prefixWord ++ tailWord_137715) baseStart_137715 baseEnd_137715 := by
    simpa [prefixWord, tailWord_137715, baseEnd_137715] using wordTrace_append hprefix tailTrace_137715
  have hstable : (prefixWord ++ tailWord_137715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137715).length < 2 ^ (prefixWord ++ tailWord_137715).sum := by decide
  have hdescent : baseEnd_137715 < baseStart_137715 := by decide
  rcases family_descends (prefixWord ++ tailWord_137715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137741 : List Nat := [1, 7, 1, 1, 1, 3, 2, 2, 2]
def baseStart_137741 : Nat := 118140960795 + 137741 * 2 ^ 59
def prefixEnd_137741 : Nat := 4983230072969 + 3 ^ 40 * 137741 * 2
def baseEnd_137741 : Nat := 62868745627600730136931

theorem tailTrace_137741 : CollatzResearch.WordTrace tailWord_137741 prefixEnd_137741 62868745627600730136931 := by
  unfold tailWord_137741
  simp only [CollatzResearch.WordTrace]
  refine ⟨5023826993995356135045077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3349217995996904090030051 5023826993995356135045077)
  ·
    refine ⟨117745945171766159415119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 5023826993995356135045077 117745945171766159415119)
    ·
      refine ⟨176618917757649239122679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117745945171766159415119 176618917757649239122679)
      ·
        refine ⟨264928376636473858684019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176618917757649239122679 264928376636473858684019)
        ·
          refine ⟨397392564954710788026029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264928376636473858684019 397392564954710788026029)
          ·
            refine ⟨149022211858016545509761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 397392564954710788026029 149022211858016545509761)
            ·
              refine ⟨111766658893512409132321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149022211858016545509761 111766658893512409132321)
              ·
                refine ⟨83824994170134306849241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111766658893512409132321 83824994170134306849241)
                ·
                  refine ⟨62868745627600730136931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83824994170134306849241 62868745627600730136931)
                  ·
                    rfl

theorem cell20_137741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_137741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137741 prefixEnd_137741 := by exact prefixLift 137741
  have htrace : WordTrace (prefixWord ++ tailWord_137741) baseStart_137741 baseEnd_137741 := by
    simpa [prefixWord, tailWord_137741, baseEnd_137741] using wordTrace_append hprefix tailTrace_137741
  have hstable : (prefixWord ++ tailWord_137741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137741).length < 2 ^ (prefixWord ++ tailWord_137741).sum := by decide
  have hdescent : baseEnd_137741 < baseStart_137741 := by decide
  rcases family_descends (prefixWord ++ tailWord_137741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137742 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_137742 : Nat := 118140960795 + 137742 * 2 ^ 59
def prefixEnd_137742 : Nat := 4983230072969 + 3 ^ 40 * 137742 * 2
def baseEnd_137742 : Nat := 62869202054849171103593

theorem tailTrace_137742 : CollatzResearch.WordTrace tailWord_137742 prefixEnd_137742 62869202054849171103593 := by
  unfold tailWord_137742
  simp only [CollatzResearch.WordTrace]
  refine ⟨627982933373966663228935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3349242311327822203887653 627982933373966663228935)
  ·
    refine ⟨941974400060949994843403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627982933373966663228935 941974400060949994843403)
    ·
      refine ⟨1412961600091424992265105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941974400060949994843403 1412961600091424992265105)
      ·
        refine ⟨1059721200068568744198829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1412961600091424992265105 1059721200068568744198829)
        ·
          refine ⟨397395450025713279074561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1059721200068568744198829 397395450025713279074561)
          ·
            refine ⟨298046587519284959305921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397395450025713279074561 298046587519284959305921)
            ·
              refine ⟨223534940639463719479441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298046587519284959305921 223534940639463719479441)
              ·
                refine ⟨167651205479597789609581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223534940639463719479441 167651205479597789609581)
                ·
                  refine ⟨62869202054849171103593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167651205479597789609581 62869202054849171103593)
                  ·
                    rfl

theorem cell20_137742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_137742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137742 prefixEnd_137742 := by exact prefixLift 137742
  have htrace : WordTrace (prefixWord ++ tailWord_137742) baseStart_137742 baseEnd_137742 := by
    simpa [prefixWord, tailWord_137742, baseEnd_137742] using wordTrace_append hprefix tailTrace_137742
  have hstable : (prefixWord ++ tailWord_137742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137742).length < 2 ^ (prefixWord ++ tailWord_137742).sum := by decide
  have hdescent : baseEnd_137742 < baseStart_137742 := by decide
  rcases family_descends (prefixWord ++ tailWord_137742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137749 : List Nat := [1, 3, 2, 1, 3, 1, 3, 4, 2]
def baseStart_137749 : Nat := 118140960795 + 137749 * 2 ^ 59
def prefixEnd_137749 : Nat := 4983230072969 + 3 ^ 40 * 137749 * 2
def baseEnd_137749 : Nat := 62872397045588257870231

theorem tailTrace_137749 : CollatzResearch.WordTrace tailWord_137749 prefixEnd_137749 62872397045588257870231 := by
  unfold tailWord_137749
  simp only [CollatzResearch.WordTrace]
  refine ⟨5024118777966373501336301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3349412518644249000890867 5024118777966373501336301)
  ·
    refine ⟨1884044541737390063001113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5024118777966373501336301 1884044541737390063001113)
    ·
      refine ⟨1413033406303042547250835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1884044541737390063001113 1413033406303042547250835)
      ·
        refine ⟨2119550109454563820876253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413033406303042547250835 2119550109454563820876253)
        ·
          refine ⟨794831291045461432828595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2119550109454563820876253 794831291045461432828595)
          ·
            refine ⟨1192246936568192149242893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794831291045461432828595 1192246936568192149242893)
            ·
              refine ⟨447092601213072055966085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1192246936568192149242893 447092601213072055966085)
              ·
                refine ⟨83829862727451010493641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447092601213072055966085 83829862727451010493641)
                ·
                  refine ⟨62872397045588257870231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83829862727451010493641 62872397045588257870231)
                  ·
                    rfl

theorem cell20_137749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_137749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137749 prefixEnd_137749 := by exact prefixLift 137749
  have htrace : WordTrace (prefixWord ++ tailWord_137749) baseStart_137749 baseEnd_137749 := by
    simpa [prefixWord, tailWord_137749, baseEnd_137749] using wordTrace_append hprefix tailTrace_137749
  have hstable : (prefixWord ++ tailWord_137749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137749).length < 2 ^ (prefixWord ++ tailWord_137749).sum := by decide
  have hdescent : baseEnd_137749 < baseStart_137749 := by decide
  rcases family_descends (prefixWord ++ tailWord_137749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137756 : List Nat := [2, 2, 3, 1, 2, 4, 1, 5]
def baseStart_137756 : Nat := 118140960795 + 137756 * 2 ^ 59
def prefixEnd_137756 : Nat := 4983230072969 + 3 ^ 40 * 137756 * 2
def baseEnd_137756 : Nat := 20958530678775781545623

theorem tailTrace_137756 : CollatzResearch.WordTrace tailWord_137756 prefixEnd_137756 20958530678775781545623 := by
  unfold tailWord_137756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2512187044470506848420561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3349582725960675797894081 2512187044470506848420561)
  ·
    refine ⟨1884140283352880136315421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2512187044470506848420561 1884140283352880136315421)
    ·
      refine ⟨706552606257330051118283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1884140283352880136315421 706552606257330051118283)
      ·
        refine ⟨1059828909385995076677425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706552606257330051118283 1059828909385995076677425)
        ·
          refine ⟨794871682039496307508069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1059828909385995076677425 794871682039496307508069)
          ·
            refine ⟨149038440382405557657763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 794871682039496307508069 149038440382405557657763)
            ·
              refine ⟨223557660573608336486645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149038440382405557657763 223557660573608336486645)
              ·
                refine ⟨20958530678775781545623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223557660573608336486645 20958530678775781545623)
                ·
                  rfl

theorem cell20_137756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_137756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137756 prefixEnd_137756 := by exact prefixLift 137756
  have htrace : WordTrace (prefixWord ++ tailWord_137756) baseStart_137756 baseEnd_137756 := by
    simpa [prefixWord, tailWord_137756, baseEnd_137756] using wordTrace_append hprefix tailTrace_137756
  have hstable : (prefixWord ++ tailWord_137756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137756).length < 2 ^ (prefixWord ++ tailWord_137756).sum := by decide
  have hdescent : baseEnd_137756 < baseStart_137756 := by decide
  rcases family_descends (prefixWord ++ tailWord_137756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137763 : List Nat := [1, 1, 1, 4, 4, 1, 2, 3, 3]
def baseStart_137763 : Nat := 118140960795 + 137763 * 2 ^ 59
def prefixEnd_137763 : Nat := 4983230072969 + 3 ^ 40 * 137763 * 2
def baseEnd_137763 : Nat := 62878787027066431403507

theorem tailTrace_137763 : CollatzResearch.WordTrace tailWord_137763 prefixEnd_137763 62878787027066431403507 := by
  unfold tailWord_137763
  simp only [CollatzResearch.WordTrace]
  refine ⟨5024629399915653892345943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3349752933277102594897295 5024629399915653892345943)
  ·
    refine ⟨7536944099873480838518915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5024629399915653892345943 7536944099873480838518915)
    ·
      refine ⟨11305416149810221257778373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7536944099873480838518915 11305416149810221257778373)
      ·
        refine ⟨2119765528089416485833445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11305416149810221257778373 2119765528089416485833445)
        ·
          refine ⟨397456036516765591093771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2119765528089416485833445 397456036516765591093771)
          ·
            refine ⟨596184054775148386640657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397456036516765591093771 596184054775148386640657)
            ·
              refine ⟨447138041081361289980493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596184054775148386640657 447138041081361289980493)
              ·
                refine ⟨167676765405510483742685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 447138041081361289980493 167676765405510483742685)
                ·
                  refine ⟨62878787027066431403507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167676765405510483742685 62878787027066431403507)
                  ·
                    rfl

theorem cell20_137763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_137763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137763 prefixEnd_137763 := by exact prefixLift 137763
  have htrace : WordTrace (prefixWord ++ tailWord_137763) baseStart_137763 baseEnd_137763 := by
    simpa [prefixWord, tailWord_137763, baseEnd_137763] using wordTrace_append hprefix tailTrace_137763
  have hstable : (prefixWord ++ tailWord_137763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137763).length < 2 ^ (prefixWord ++ tailWord_137763).sum := by decide
  have hdescent : baseEnd_137763 < baseStart_137763 := by decide
  rcases family_descends (prefixWord ++ tailWord_137763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137770 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_137770 : Nat := 118140960795 + 137770 * 2 ^ 59
def prefixEnd_137770 : Nat := 4983230072969 + 3 ^ 40 * 137770 * 2
def baseEnd_137770 : Nat := 62881982017805518170145

theorem tailTrace_137770 : CollatzResearch.WordTrace tailWord_137770 prefixEnd_137770 62881982017805518170145 := by
  unfold tailWord_137770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1256221177722573521962691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3349923140593529391900509 1256221177722573521962691)
  ·
    refine ⟨1884331766583860282944037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1256221177722573521962691 1884331766583860282944037)
    ·
      refine ⟨353312206234473803052007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1884331766583860282944037 353312206234473803052007)
      ·
        refine ⟨529968309351710704578011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353312206234473803052007 529968309351710704578011)
        ·
          refine ⟨794952464027566056867017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529968309351710704578011 794952464027566056867017)
          ·
            refine ⟨596214348020674542650263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794952464027566056867017 596214348020674542650263)
            ·
              refine ⟨894321522031011813975395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596214348020674542650263 894321522031011813975395)
              ·
                refine ⟨1341482283046517720963093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894321522031011813975395 1341482283046517720963093)
                ·
                  refine ⟨62881982017805518170145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1341482283046517720963093 62881982017805518170145)
                  ·
                    rfl

theorem cell20_137770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_137770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137770 prefixEnd_137770 := by exact prefixLift 137770
  have htrace : WordTrace (prefixWord ++ tailWord_137770) baseStart_137770 baseEnd_137770 := by
    simpa [prefixWord, tailWord_137770, baseEnd_137770] using wordTrace_append hprefix tailTrace_137770
  have hstable : (prefixWord ++ tailWord_137770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137770).length < 2 ^ (prefixWord ++ tailWord_137770).sum := by decide
  have hdescent : baseEnd_137770 < baseStart_137770 := by decide
  rcases family_descends (prefixWord ++ tailWord_137770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137784 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_137784 : Nat := 118140960795 + 137784 * 2 ^ 59
def prefixEnd_137784 : Nat := 4983230072969 + 3 ^ 40 * 137784 * 2
def baseEnd_137784 : Nat := 62888371999283691703421

theorem tailTrace_137784 : CollatzResearch.WordTrace tailWord_137784 prefixEnd_137784 62888371999283691703421 := by
  unfold tailWord_137784
  simp only [CollatzResearch.WordTrace]
  refine ⟨2512697666419787239430203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3350263555226382985906937 2512697666419787239430203)
  ·
    refine ⟨3769046499629680859145305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2512697666419787239430203 3769046499629680859145305)
    ·
      refine ⟨2826784874722260644358979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3769046499629680859145305 2826784874722260644358979)
      ·
        refine ⟨4240177312083390966538469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2826784874722260644358979 4240177312083390966538469)
        ·
          refine ⟨795033246015635806225963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4240177312083390966538469 795033246015635806225963)
          ·
            refine ⟨1192549869023453709338945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795033246015635806225963 1192549869023453709338945)
            ·
              refine ⟨894412401767590282004209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192549869023453709338945 894412401767590282004209)
              ·
                refine ⟨670809301325692711503157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894412401767590282004209 670809301325692711503157)
                ·
                  refine ⟨62888371999283691703421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 670809301325692711503157 62888371999283691703421)
                  ·
                    rfl

theorem cell20_137784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_137784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137784 prefixEnd_137784 := by exact prefixLift 137784
  have htrace : WordTrace (prefixWord ++ tailWord_137784) baseStart_137784 baseEnd_137784 := by
    simpa [prefixWord, tailWord_137784, baseEnd_137784] using wordTrace_append hprefix tailTrace_137784
  have hstable : (prefixWord ++ tailWord_137784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137784).length < 2 ^ (prefixWord ++ tailWord_137784).sum := by decide
  have hdescent : baseEnd_137784 < baseStart_137784 := by decide
  rcases family_descends (prefixWord ++ tailWord_137784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137791 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_137791 : Nat := 118140960795 + 137791 * 2 ^ 59
def prefixEnd_137791 : Nat := 4983230072969 + 3 ^ 40 * 137791 * 2
def baseEnd_137791 : Nat := 62891566990022778470059

theorem tailTrace_137791 : CollatzResearch.WordTrace tailWord_137791 prefixEnd_137791 62891566990022778470059 := by
  unfold tailWord_137791
  simp only [CollatzResearch.WordTrace]
  refine ⟨5025650643814214674365227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3350433762542809782910151 5025650643814214674365227)
  ·
    refine ⟨7538475965721322011547841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5025650643814214674365227 7538475965721322011547841)
    ·
      refine ⟨5653856974290991508660881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7538475965721322011547841 5653856974290991508660881)
      ·
        refine ⟨4240392730718243631495661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5653856974290991508660881 4240392730718243631495661)
        ·
          refine ⟨1590147274019341361810873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4240392730718243631495661 1590147274019341361810873)
          ·
            refine ⟨1192610455514506021358155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590147274019341361810873 1192610455514506021358155)
            ·
              refine ⟨1788915683271759032037233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192610455514506021358155 1788915683271759032037233)
              ·
                refine ⟨1341686762453819274027925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788915683271759032037233 1341686762453819274027925)
                ·
                  refine ⟨62891566990022778470059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1341686762453819274027925 62891566990022778470059)
                  ·
                    rfl

theorem cell20_137791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_137791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137791 prefixEnd_137791 := by exact prefixLift 137791
  have htrace : WordTrace (prefixWord ++ tailWord_137791) baseStart_137791 baseEnd_137791 := by
    simpa [prefixWord, tailWord_137791, baseEnd_137791] using wordTrace_append hprefix tailTrace_137791
  have hstable : (prefixWord ++ tailWord_137791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137791).length < 2 ^ (prefixWord ++ tailWord_137791).sum := by decide
  have hdescent : baseEnd_137791 < baseStart_137791 := by decide
  rcases family_descends (prefixWord ++ tailWord_137791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137832 : List Nat := [2, 1, 4, 3, 2, 1, 1, 6]
def baseStart_137832 : Nat := 118140960795 + 137832 * 2 ^ 59
def prefixEnd_137832 : Nat := 4983230072969 + 3 ^ 40 * 137832 * 2
def baseEnd_137832 : Nat := 20970093502402952701075

theorem tailTrace_137832 : CollatzResearch.WordTrace tailWord_137832 prefixEnd_137832 20970093502402952701075 := by
  unfold tailWord_137832
  simp only [CollatzResearch.WordTrace]
  refine ⟨2513573018332839338303875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3351430691110452451071833 2513573018332839338303875)
  ·
    refine ⟨3770359527499259007455813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2513573018332839338303875 3770359527499259007455813)
    ·
      refine ⟨706942411406111063897965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3770359527499259007455813 706942411406111063897965)
      ·
        refine ⟨265103404277291648961737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 706942411406111063897965 265103404277291648961737)
        ·
          refine ⟨198827553207968736721303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265103404277291648961737 198827553207968736721303)
          ·
            refine ⟨298241329811953105081955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198827553207968736721303 298241329811953105081955)
            ·
              refine ⟨447361994717929657622933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298241329811953105081955 447361994717929657622933)
              ·
                refine ⟨20970093502402952701075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 447361994717929657622933 20970093502402952701075)
                ·
                  rfl

theorem cell20_137832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_137832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137832 prefixEnd_137832 := by exact prefixLift 137832
  have htrace : WordTrace (prefixWord ++ tailWord_137832) baseStart_137832 baseEnd_137832 := by
    simpa [prefixWord, tailWord_137832, baseEnd_137832] using wordTrace_append hprefix tailTrace_137832
  have hstable : (prefixWord ++ tailWord_137832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137832).length < 2 ^ (prefixWord ++ tailWord_137832).sum := by decide
  have hdescent : baseEnd_137832 < baseStart_137832 := by decide
  rcases family_descends (prefixWord ++ tailWord_137832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137867 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_137867 : Nat := 118140960795 + 137867 * 2 ^ 59
def prefixEnd_137867 : Nat := 4983230072969 + 3 ^ 40 * 137867 * 2
def baseEnd_137867 : Nat := 62926255460904291936415

theorem tailTrace_137867 : CollatzResearch.WordTrace tailWord_137867 prefixEnd_137867 62926255460904291936415 := by
  unfold tailWord_137867
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028422591538879654131855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3352281727692586436087903 5028422591538879654131855)
  ·
    refine ⟨7542633887308319481197783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5028422591538879654131855 7542633887308319481197783)
    ·
      refine ⟨11313950830962479221796675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7542633887308319481197783 11313950830962479221796675)
      ·
        refine ⟨16970926246443718832695013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11313950830962479221796675 16970926246443718832695013)
        ·
          refine ⟨3182048671208197281130315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16970926246443718832695013 3182048671208197281130315)
          ·
            refine ⟨4773073006812295921695473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182048671208197281130315 4773073006812295921695473)
            ·
              refine ⟨3579804755109221941271605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4773073006812295921695473 3579804755109221941271605)
              ·
                refine ⟨335606695791489556994213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3579804755109221941271605 335606695791489556994213)
                ·
                  refine ⟨62926255460904291936415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335606695791489556994213 62926255460904291936415)
                  ·
                    rfl

theorem cell20_137867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_137867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137867 prefixEnd_137867 := by exact prefixLift 137867
  have htrace : WordTrace (prefixWord ++ tailWord_137867) baseStart_137867 baseEnd_137867 := by
    simpa [prefixWord, tailWord_137867, baseEnd_137867] using wordTrace_append hprefix tailTrace_137867
  have hstable : (prefixWord ++ tailWord_137867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137867).length < 2 ^ (prefixWord ++ tailWord_137867).sum := by decide
  have hdescent : baseEnd_137867 < baseStart_137867 := by decide
  rcases family_descends (prefixWord ++ tailWord_137867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137943 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_137943 : Nat := 118140960795 + 137943 * 2 ^ 59
def prefixEnd_137943 : Nat := 4983230072969 + 3 ^ 40 * 137943 * 2
def baseEnd_137943 : Nat := 62960943931785805402771

theorem tailTrace_137943 : CollatzResearch.WordTrace tailWord_137943 prefixEnd_137943 62960943931785805402771 := by
  unfold tailWord_137943
  simp only [CollatzResearch.WordTrace]
  refine ⟨5031194539263544633898483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3354129692842363089265655 5031194539263544633898483)
  ·
    refine ⟨7546791808895316950847725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5031194539263544633898483 7546791808895316950847725)
    ·
      refine ⟨2830046928335743856567897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7546791808895316950847725 2830046928335743856567897)
      ·
        refine ⟨2122535196251807892425923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2830046928335743856567897 2122535196251807892425923)
        ·
          refine ⟨3183802794377711838638885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2122535196251807892425923 3183802794377711838638885)
          ·
            refine ⟨596963023945820969744791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3183802794377711838638885 596963023945820969744791)
            ·
              refine ⟨895444535918731454617187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596963023945820969744791 895444535918731454617187)
              ·
                refine ⟨1343166803878097181925781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895444535918731454617187 1343166803878097181925781)
                ·
                  refine ⟨62960943931785805402771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1343166803878097181925781 62960943931785805402771)
                  ·
                    rfl

theorem cell20_137943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_137943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137943 prefixEnd_137943 := by exact prefixLift 137943
  have htrace : WordTrace (prefixWord ++ tailWord_137943) baseStart_137943 baseEnd_137943 := by
    simpa [prefixWord, tailWord_137943, baseEnd_137943] using wordTrace_append hprefix tailTrace_137943
  have hstable : (prefixWord ++ tailWord_137943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137943).length < 2 ^ (prefixWord ++ tailWord_137943).sum := by decide
  have hdescent : baseEnd_137943 < baseStart_137943 := by decide
  rcases family_descends (prefixWord ++ tailWord_137943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137970 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_137970 : Nat := 118140960795 + 137970 * 2 ^ 59
def prefixEnd_137970 : Nat := 4983230072969 + 3 ^ 40 * 137970 * 2
def baseEnd_137970 : Nat := 62973267467493711502661

theorem tailTrace_137970 : CollatzResearch.WordTrace tailWord_137970 prefixEnd_137970 62973267467493711502661 := by
  unfold tailWord_137970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258044827541432061282841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3354786206777152163420909 1258044827541432061282841)
  ·
    refine ⟨943533620656074045962131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1258044827541432061282841 943533620656074045962131)
    ·
      refine ⟨1415300430984111068943197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 943533620656074045962131 1415300430984111068943197)
      ·
        refine ⟨530737661619041650853699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1415300430984111068943197 530737661619041650853699)
        ·
          refine ⟨796106492428562476280549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530737661619041650853699 796106492428562476280549)
          ·
            refine ⟨149269967330355464302603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 796106492428562476280549 149269967330355464302603)
            ·
              refine ⟨223904950995533196453905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149269967330355464302603 223904950995533196453905)
              ·
                refine ⟨167928713246649897340429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223904950995533196453905 167928713246649897340429)
                ·
                  refine ⟨62973267467493711502661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167928713246649897340429 62973267467493711502661)
                  ·
                    rfl

theorem cell20_137970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_137970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137970 prefixEnd_137970 := by exact prefixLift 137970
  have htrace : WordTrace (prefixWord ++ tailWord_137970) baseStart_137970 baseEnd_137970 := by
    simpa [prefixWord, tailWord_137970, baseEnd_137970] using wordTrace_append hprefix tailTrace_137970
  have hstable : (prefixWord ++ tailWord_137970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137970).length < 2 ^ (prefixWord ++ tailWord_137970).sum := by decide
  have hdescent : baseEnd_137970 < baseStart_137970 := by decide
  rcases family_descends (prefixWord ++ tailWord_137970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137973 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 4]
def baseStart_137973 : Nat := 118140960795 + 137973 * 2 ^ 59
def prefixEnd_137973 : Nat := 4983230072969 + 3 ^ 40 * 137973 * 2
def baseEnd_137973 : Nat := 62974636749239034402649

theorem tailTrace_137973 : CollatzResearch.WordTrace tailWord_137973 prefixEnd_137973 62974636749239034402649 := by
  unfold tailWord_137973
  simp only [CollatzResearch.WordTrace]
  refine ⟨5032288729154859757490573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3354859152769906504993715 5032288729154859757490573)
  ·
    refine ⟨1887108273433072409058965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5032288729154859757490573 1887108273433072409058965)
    ·
      refine ⟨88458200317175269174639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1887108273433072409058965 88458200317175269174639)
      ·
        refine ⟨132687300475762903761959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88458200317175269174639 132687300475762903761959)
        ·
          refine ⟨199030950713644355642939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132687300475762903761959 199030950713644355642939)
          ·
            refine ⟨298546426070466533464409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199030950713644355642939 298546426070466533464409)
            ·
              refine ⟨223909819552849900098307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298546426070466533464409 223909819552849900098307)
              ·
                refine ⟨335864729329274850147461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223909819552849900098307 335864729329274850147461)
                ·
                  refine ⟨62974636749239034402649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335864729329274850147461 62974636749239034402649)
                  ·
                    rfl

theorem cell20_137973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_137973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_137973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_137973 prefixEnd_137973 := by exact prefixLift 137973
  have htrace : WordTrace (prefixWord ++ tailWord_137973) baseStart_137973 baseEnd_137973 := by
    simpa [prefixWord, tailWord_137973, baseEnd_137973] using wordTrace_append hprefix tailTrace_137973
  have hstable : (prefixWord ++ tailWord_137973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137973).length < 2 ^ (prefixWord ++ tailWord_137973).sum := by decide
  have hdescent : baseEnd_137973 < baseStart_137973 := by decide
  rcases family_descends (prefixWord ++ tailWord_137973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138012 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_138012 : Nat := 118140960795 + 138012 * 2 ^ 59
def prefixEnd_138012 : Nat := 4983230072969 + 3 ^ 40 * 138012 * 2
def baseEnd_138012 : Nat := 62992437411928232102489

theorem tailTrace_138012 : CollatzResearch.WordTrace tailWord_138012 prefixEnd_138012 62992437411928232102489 := by
  unfold tailWord_138012
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516855588006784709080145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3355807450675712945440193 2516855588006784709080145)
  ·
    refine ⟨1887641691005088531810109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2516855588006784709080145 1887641691005088531810109)
    ·
      refine ⟨707865634126908199428791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1887641691005088531810109 707865634126908199428791)
      ·
        refine ⟨1061798451190362299143187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707865634126908199428791 1061798451190362299143187)
        ·
          refine ⟨1592697676785543448714781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061798451190362299143187 1592697676785543448714781)
          ·
            refine ⟨597261628794578793268043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1592697676785543448714781 597261628794578793268043)
            ·
              refine ⟨895892443191868189902065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597261628794578793268043 895892443191868189902065)
              ·
                refine ⟨671919332393901142426549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895892443191868189902065 671919332393901142426549)
                ·
                  refine ⟨62992437411928232102489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 671919332393901142426549 62992437411928232102489)
                  ·
                    rfl

theorem cell20_138012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_138012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138012 prefixEnd_138012 := by exact prefixLift 138012
  have htrace : WordTrace (prefixWord ++ tailWord_138012) baseStart_138012 baseEnd_138012 := by
    simpa [prefixWord, tailWord_138012, baseEnd_138012] using wordTrace_append hprefix tailTrace_138012
  have hstable : (prefixWord ++ tailWord_138012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138012).length < 2 ^ (prefixWord ++ tailWord_138012).sum := by decide
  have hdescent : baseEnd_138012 < baseStart_138012 := by decide
  rcases family_descends (prefixWord ++ tailWord_138012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138015 : List Nat := [1, 1, 2, 4, 2, 2, 3, 3, 2]
def baseStart_138015 : Nat := 118140960795 + 138015 * 2 ^ 59
def prefixEnd_138015 : Nat := 4983230072969 + 3 ^ 40 * 138015 * 2
def baseEnd_138015 : Nat := 62993806693673555002477

theorem tailTrace_138015 : CollatzResearch.WordTrace tailWord_138015 prefixEnd_138015 62993806693673555002477 := by
  unfold tailWord_138015
  simp only [CollatzResearch.WordTrace]
  refine ⟨5033820595002700930519499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3355880396668467287012999 5033820595002700930519499)
  ·
    refine ⟨7550730892504051395779249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5033820595002700930519499 7550730892504051395779249)
    ·
      refine ⟨5663048169378038546834437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7550730892504051395779249 5663048169378038546834437)
      ·
        refine ⟨1061821531758382227531457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5663048169378038546834437 1061821531758382227531457)
        ·
          refine ⟨796366148818786670648593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1061821531758382227531457 796366148818786670648593)
          ·
            refine ⟨597274611614090002986445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796366148818786670648593 597274611614090002986445)
            ·
              refine ⟨223977979355283751119917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 597274611614090002986445 223977979355283751119917)
              ·
                refine ⟨83991742258231406669969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223977979355283751119917 83991742258231406669969)
                ·
                  refine ⟨62993806693673555002477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83991742258231406669969 62993806693673555002477)
                  ·
                    rfl

theorem cell20_138015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 2].length) (baseStart_138015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138015 prefixEnd_138015 := by exact prefixLift 138015
  have htrace : WordTrace (prefixWord ++ tailWord_138015) baseStart_138015 baseEnd_138015 := by
    simpa [prefixWord, tailWord_138015, baseEnd_138015] using wordTrace_append hprefix tailTrace_138015
  have hstable : (prefixWord ++ tailWord_138015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138015).length < 2 ^ (prefixWord ++ tailWord_138015).sum := by decide
  have hdescent : baseEnd_138015 < baseStart_138015 := by decide
  rcases family_descends (prefixWord ++ tailWord_138015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138046 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_138046 : Nat := 118140960795 + 138046 * 2 ^ 59
def prefixEnd_138046 : Nat := 4983230072969 + 3 ^ 40 * 138046 * 2
def baseEnd_138046 : Nat := 63007955938375224969017

theorem tailTrace_138046 : CollatzResearch.WordTrace tailWord_138046 prefixEnd_138046 63007955938375224969017 := by
  unfold tailWord_138046
  simp only [CollatzResearch.WordTrace]
  refine ⟨629368907236299153112249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3356634171926928816598661 629368907236299153112249)
  ·
    refine ⟨472026680427224364834187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 629368907236299153112249 472026680427224364834187)
    ·
      refine ⟨708040020640836547251281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472026680427224364834187 708040020640836547251281)
      ·
        refine ⟨531030015480627410438461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 708040020640836547251281 531030015480627410438461)
        ·
          refine ⟨199136255805235278914423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 531030015480627410438461 199136255805235278914423)
          ·
            refine ⟨298704383707852918371635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199136255805235278914423 298704383707852918371635)
            ·
              refine ⟨448056575561779377557453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298704383707852918371635 448056575561779377557453)
              ·
                refine ⟨168021215835667266584045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448056575561779377557453 168021215835667266584045)
                ·
                  refine ⟨63007955938375224969017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168021215835667266584045 63007955938375224969017)
                  ·
                    rfl

theorem cell20_138046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_138046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138046 prefixEnd_138046 := by exact prefixLift 138046
  have htrace : WordTrace (prefixWord ++ tailWord_138046) baseStart_138046 baseEnd_138046 := by
    simpa [prefixWord, tailWord_138046, baseEnd_138046] using wordTrace_append hprefix tailTrace_138046
  have hstable : (prefixWord ++ tailWord_138046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138046).length < 2 ^ (prefixWord ++ tailWord_138046).sum := by decide
  have hdescent : baseEnd_138046 < baseStart_138046 := by decide
  rcases family_descends (prefixWord ++ tailWord_138046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138064 : List Nat := [2, 1, 1, 1, 1, 4, 4, 6]
def baseStart_138064 : Nat := 118140960795 + 138064 * 2 ^ 59
def prefixEnd_138064 : Nat := 4983230072969 + 3 ^ 40 * 138064 * 2
def baseEnd_138064 : Nat := 21005390542949054122981

theorem tailTrace_138064 : CollatzResearch.WordTrace tailWord_138064 prefixEnd_138064 21005390542949054122981 := by
  unfold tailWord_138064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517803885912591149526623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3357071847883454866035497 2517803885912591149526623)
  ·
    refine ⟨3776705828868886724289935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2517803885912591149526623 3776705828868886724289935)
    ·
      refine ⟨5665058743303330086434903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3776705828868886724289935 5665058743303330086434903)
      ·
        refine ⟨8497588114954995129652355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5665058743303330086434903 8497588114954995129652355)
        ·
          refine ⟨12746382172432492694478533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8497588114954995129652355 12746382172432492694478533)
          ·
            refine ⟨2389946657331092380214725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12746382172432492694478533 2389946657331092380214725)
            ·
              refine ⟨448114998249579821290261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2389946657331092380214725 448114998249579821290261)
              ·
                refine ⟨21005390542949054122981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 448114998249579821290261 21005390542949054122981)
                ·
                  rfl

theorem cell20_138064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_138064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138064 prefixEnd_138064 := by exact prefixLift 138064
  have htrace : WordTrace (prefixWord ++ tailWord_138064) baseStart_138064 baseEnd_138064 := by
    simpa [prefixWord, tailWord_138064, baseEnd_138064] using wordTrace_append hprefix tailTrace_138064
  have hstable : (prefixWord ++ tailWord_138064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138064).length < 2 ^ (prefixWord ++ tailWord_138064).sum := by decide
  have hdescent : baseEnd_138064 < baseStart_138064 := by decide
  rcases family_descends (prefixWord ++ tailWord_138064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138091 : List Nat := [1, 1, 1, 1, 2, 2, 8, 2, 2]
def baseStart_138091 : Nat := 118140960795 + 138091 * 2 ^ 59
def prefixEnd_138091 : Nat := 4983230072969 + 3 ^ 40 * 138091 * 2
def baseEnd_138091 : Nat := 63028495164555068468833

theorem tailTrace_138091 : CollatzResearch.WordTrace tailWord_138091 prefixEnd_138091 63028495164555068468833 := by
  unfold tailWord_138091
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036592542727365910286127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3357728361818243940190751 5036592542727365910286127)
  ·
    refine ⟨7554888814091048865429191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5036592542727365910286127 7554888814091048865429191)
    ·
      refine ⟨11332333221136573298143787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7554888814091048865429191 11332333221136573298143787)
      ·
        refine ⟨16998499831704859947215681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11332333221136573298143787 16998499831704859947215681)
        ·
          refine ⟨12748874873778644960411761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16998499831704859947215681 12748874873778644960411761)
          ·
            refine ⟨9561656155333983720308821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12748874873778644960411761 9561656155333983720308821)
            ·
              refine ⟨112050658070320121722369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 9561656155333983720308821 112050658070320121722369)
              ·
                refine ⟨84037993552740091291777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112050658070320121722369 84037993552740091291777)
                ·
                  refine ⟨63028495164555068468833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84037993552740091291777 63028495164555068468833)
                  ·
                    rfl

theorem cell20_138091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 2].length) (baseStart_138091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138091 prefixEnd_138091 := by exact prefixLift 138091
  have htrace : WordTrace (prefixWord ++ tailWord_138091) baseStart_138091 baseEnd_138091 := by
    simpa [prefixWord, tailWord_138091, baseEnd_138091] using wordTrace_append hprefix tailTrace_138091
  have hstable : (prefixWord ++ tailWord_138091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138091).length < 2 ^ (prefixWord ++ tailWord_138091).sum := by decide
  have hdescent : baseEnd_138091 < baseStart_138091 := by decide
  rcases family_descends (prefixWord ++ tailWord_138091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138143 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 3]
def baseStart_138143 : Nat := 118140960795 + 138143 * 2 ^ 59
def prefixEnd_138143 : Nat := 4983230072969 + 3 ^ 40 * 138143 * 2
def baseEnd_138143 : Nat := 63052229381473998735287

theorem tailTrace_138143 : CollatzResearch.WordTrace tailWord_138143 prefixEnd_138143 63052229381473998735287 := by
  unfold tailWord_138143
  simp only [CollatzResearch.WordTrace]
  refine ⟨5038489138538978791179083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3358992759025985860786055 5038489138538978791179083)
  ·
    refine ⟨7557733707808468186768625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5038489138538978791179083 7557733707808468186768625)
    ·
      refine ⟨5668300280856351140076469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7557733707808468186768625 5668300280856351140076469)
      ·
        refine ⟨531403151330282919382169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5668300280856351140076469 531403151330282919382169)
        ·
          refine ⟨398552363497712189536627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531403151330282919382169 398552363497712189536627)
          ·
            refine ⟨597828545246568284304941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398552363497712189536627 597828545246568284304941)
            ·
              refine ⟨224185704467463106614353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 597828545246568284304941 224185704467463106614353)
              ·
                refine ⟨168139278350597329960765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224185704467463106614353 168139278350597329960765)
                ·
                  refine ⟨63052229381473998735287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168139278350597329960765 63052229381473998735287)
                  ·
                    rfl

theorem cell20_138143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_138143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138143 prefixEnd_138143 := by exact prefixLift 138143
  have htrace : WordTrace (prefixWord ++ tailWord_138143) baseStart_138143 baseEnd_138143 := by
    simpa [prefixWord, tailWord_138143, baseEnd_138143] using wordTrace_append hprefix tailTrace_138143
  have hstable : (prefixWord ++ tailWord_138143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138143).length < 2 ^ (prefixWord ++ tailWord_138143).sum := by decide
  have hdescent : baseEnd_138143 < baseStart_138143 := by decide
  rcases family_descends (prefixWord ++ tailWord_138143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138166 : List Nat := [5, 1, 4, 1, 2, 1, 2, 4]
def baseStart_138166 : Nat := 118140960795 + 138166 * 2 ^ 59
def prefixEnd_138166 : Nat := 4983230072969 + 3 ^ 40 * 138166 * 2
def baseEnd_138166 : Nat := 21020909069396046989509

theorem tailTrace_138166 : CollatzResearch.WordTrace tailWord_138166 prefixEnd_138166 21020909069396046989509 := by
  unfold tailWord_138166
  simp only [CollatzResearch.WordTrace]
  refine ⟨314958001090978357454147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3359552011637102479510901 314958001090978357454147)
  ·
    refine ⟨472437001636467536181221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 314958001090978357454147 472437001636467536181221)
    ·
      refine ⟨88581937806837663033979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 472437001636467536181221 88581937806837663033979)
      ·
        refine ⟨132872906710256494550969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88581937806837663033979 132872906710256494550969)
        ·
          refine ⟨99654680032692370913227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132872906710256494550969 99654680032692370913227)
          ·
            refine ⟨149482020049038556369841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99654680032692370913227 149482020049038556369841)
            ·
              refine ⟨112111515036778917277381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149482020049038556369841 112111515036778917277381)
              ·
                refine ⟨21020909069396046989509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112111515036778917277381 21020909069396046989509)
                ·
                  rfl

theorem cell20_138166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_138166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138166 prefixEnd_138166 := by exact prefixLift 138166
  have htrace : WordTrace (prefixWord ++ tailWord_138166) baseStart_138166 baseEnd_138166 := by
    simpa [prefixWord, tailWord_138166, baseEnd_138166] using wordTrace_append hprefix tailTrace_138166
  have hstable : (prefixWord ++ tailWord_138166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138166).length < 2 ^ (prefixWord ++ tailWord_138166).sum := by decide
  have hdescent : baseEnd_138166 < baseStart_138166 := by decide
  rcases family_descends (prefixWord ++ tailWord_138166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138180 : List Nat := [2, 3, 3, 3, 2, 1, 1, 3, 2]
def baseStart_138180 : Nat := 118140960795 + 138180 * 2 ^ 59
def prefixEnd_138180 : Nat := 4983230072969 + 3 ^ 40 * 138180 * 2
def baseEnd_138180 : Nat := 63069117189666314501803

theorem tailTrace_138180 : CollatzResearch.WordTrace tailWord_138180 prefixEnd_138180 63069117189666314501803 := by
  unfold tailWord_138180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519919319702467055137997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3359892426269956073517329 2519919319702467055137997)
  ·
    refine ⟨944969744888425145676749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2519919319702467055137997 944969744888425145676749)
    ·
      refine ⟨354363654333159429628781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 944969744888425145676749 354363654333159429628781)
      ·
        refine ⟨132886370374934786110793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354363654333159429628781 132886370374934786110793)
        ·
          refine ⟨99664777781201089583095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132886370374934786110793 99664777781201089583095)
          ·
            refine ⟨149497166671801634374643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99664777781201089583095 149497166671801634374643)
            ·
              refine ⟨224245750007702451561965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149497166671801634374643 224245750007702451561965)
              ·
                refine ⟨84092156252888419335737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224245750007702451561965 84092156252888419335737)
                ·
                  refine ⟨63069117189666314501803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84092156252888419335737 63069117189666314501803)
                  ·
                    rfl

theorem cell20_138180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_138180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138180 prefixEnd_138180 := by exact prefixLift 138180
  have htrace : WordTrace (prefixWord ++ tailWord_138180) baseStart_138180 baseEnd_138180 := by
    simpa [prefixWord, tailWord_138180, baseEnd_138180] using wordTrace_append hprefix tailTrace_138180
  have hstable : (prefixWord ++ tailWord_138180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138180).length < 2 ^ (prefixWord ++ tailWord_138180).sum := by decide
  have hdescent : baseEnd_138180 < baseStart_138180 := by decide
  rcases family_descends (prefixWord ++ tailWord_138180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138184 : List Nat := [2, 1, 3, 1, 5, 2, 1, 3, 2]
def baseStart_138184 : Nat := 118140960795 + 138184 * 2 ^ 59
def prefixEnd_138184 : Nat := 4983230072969 + 3 ^ 40 * 138184 * 2
def baseEnd_138184 : Nat := 63070942898660078368453

theorem tailTrace_138184 : CollatzResearch.WordTrace tailWord_138184 prefixEnd_138184 63070942898660078368453 := by
  unfold tailWord_138184
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519992265695221396710803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3359989687593628528947737 2519992265695221396710803)
  ·
    refine ⟨3779988398542832095066205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2519992265695221396710803 3779988398542832095066205)
    ·
      refine ⟨1417495649453562035649827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3779988398542832095066205 1417495649453562035649827)
      ·
        refine ⟨2126243474180343053474741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417495649453562035649827 2126243474180343053474741)
        ·
          refine ⟨199335325704407161263257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2126243474180343053474741 199335325704407161263257)
          ·
            refine ⟨149501494278305370947443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199335325704407161263257 149501494278305370947443)
            ·
              refine ⟨224252241417458056421165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149501494278305370947443 224252241417458056421165)
              ·
                refine ⟨84094590531546771157937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224252241417458056421165 84094590531546771157937)
                ·
                  refine ⟨63070942898660078368453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84094590531546771157937 63070942898660078368453)
                  ·
                    rfl

theorem cell20_138184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_138184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138184 prefixEnd_138184 := by exact prefixLift 138184
  have htrace : WordTrace (prefixWord ++ tailWord_138184) baseStart_138184 baseEnd_138184 := by
    simpa [prefixWord, tailWord_138184, baseEnd_138184] using wordTrace_append hprefix tailTrace_138184
  have hstable : (prefixWord ++ tailWord_138184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138184).length < 2 ^ (prefixWord ++ tailWord_138184).sum := by decide
  have hdescent : baseEnd_138184 < baseStart_138184 := by decide
  rcases family_descends (prefixWord ++ tailWord_138184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138202 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_138202 : Nat := 118140960795 + 138202 * 2 ^ 59
def prefixEnd_138202 : Nat := 4983230072969 + 3 ^ 40 * 138202 * 2
def baseEnd_138202 : Nat := 63079158589132015768379

theorem tailTrace_138202 : CollatzResearch.WordTrace tailWord_138202 prefixEnd_138202 63079158589132015768379 := by
  unfold tailWord_138202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260160261331307966894215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3360427363550154578384573 1260160261331307966894215)
  ·
    refine ⟨1890240391996961950341323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260160261331307966894215 1890240391996961950341323)
    ·
      refine ⟨2835360587995442925511985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890240391996961950341323 2835360587995442925511985)
      ·
        refine ⟨2126520440996582194133989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2835360587995442925511985 2126520440996582194133989)
        ·
          refine ⟨398722582686859161400123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2126520440996582194133989 398722582686859161400123)
          ·
            refine ⟨598083874030288742100185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398722582686859161400123 598083874030288742100185)
            ·
              refine ⟨448562905522716556575139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598083874030288742100185 448562905522716556575139)
              ·
                refine ⟨672844358284074834862709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448562905522716556575139 672844358284074834862709)
                ·
                  refine ⟨63079158589132015768379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 672844358284074834862709 63079158589132015768379)
                  ·
                    rfl

theorem cell20_138202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_138202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138202 prefixEnd_138202 := by exact prefixLift 138202
  have htrace : WordTrace (prefixWord ++ tailWord_138202) baseStart_138202 baseEnd_138202 := by
    simpa [prefixWord, tailWord_138202, baseEnd_138202] using wordTrace_append hprefix tailTrace_138202
  have hstable : (prefixWord ++ tailWord_138202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138202).length < 2 ^ (prefixWord ++ tailWord_138202).sum := by decide
  have hdescent : baseEnd_138202 < baseStart_138202 := by decide
  rcases family_descends (prefixWord ++ tailWord_138202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138205 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 4]
def baseStart_138205 : Nat := 118140960795 + 138205 * 2 ^ 59
def prefixEnd_138205 : Nat := 4983230072969 + 3 ^ 40 * 138205 * 2
def baseEnd_138205 : Nat := 63080527870877338668367

theorem tailTrace_138205 : CollatzResearch.WordTrace tailWord_138205 prefixEnd_138205 63080527870877338668367 := by
  unfold tailWord_138205
  simp only [CollatzResearch.WordTrace]
  refine ⟨5040750464314363379936069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3360500309542908919957379 5040750464314363379936069)
  ·
    refine ⟨945140712058943133738013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5040750464314363379936069 945140712058943133738013)
    ·
      refine ⟨354427767022103675151755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 945140712058943133738013 354427767022103675151755)
      ·
        refine ⟨531641650533155512727633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354427767022103675151755 531641650533155512727633)
        ·
          refine ⟨398731237899866634545725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531641650533155512727633 398731237899866634545725)
          ·
            refine ⟨149524214212449987954647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 398731237899866634545725 149524214212449987954647)
            ·
              refine ⟨224286321318674981931971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149524214212449987954647 224286321318674981931971)
              ·
                refine ⟨336429481978012472897957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224286321318674981931971 336429481978012472897957)
                ·
                  refine ⟨63080527870877338668367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 336429481978012472897957 63080527870877338668367)
                  ·
                    rfl

theorem cell20_138205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_138205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138205 prefixEnd_138205 := by exact prefixLift 138205
  have htrace : WordTrace (prefixWord ++ tailWord_138205) baseStart_138205 baseEnd_138205 := by
    simpa [prefixWord, tailWord_138205, baseEnd_138205] using wordTrace_append hprefix tailTrace_138205
  have hstable : (prefixWord ++ tailWord_138205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138205).length < 2 ^ (prefixWord ++ tailWord_138205).sum := by decide
  have hdescent : baseEnd_138205 < baseStart_138205 := by decide
  rcases family_descends (prefixWord ++ tailWord_138205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138216 : List Nat := [2, 1, 4, 1, 1, 1, 3, 7]
def baseStart_138216 : Nat := 118140960795 + 138216 * 2 ^ 59
def prefixEnd_138216 : Nat := 4983230072969 + 3 ^ 40 * 138216 * 2
def baseEnd_138216 : Nat := 21028516190203396433885

theorem tailTrace_138216 : CollatzResearch.WordTrace tailWord_138216 prefixEnd_138216 21028516190203396433885 := by
  unfold tailWord_138216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2520575833637256129293251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3360767778183008172391001 2520575833637256129293251)
  ·
    refine ⟨3780863750455884193939877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2520575833637256129293251 3780863750455884193939877)
    ·
      refine ⟨708911953210478286363727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3780863750455884193939877 708911953210478286363727)
      ·
        refine ⟨1063367929815717429545591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708911953210478286363727 1063367929815717429545591)
        ·
          refine ⟨1595051894723576144318387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063367929815717429545591 1595051894723576144318387)
          ·
            refine ⟨2392577842085364216477581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595051894723576144318387 2392577842085364216477581)
            ·
              refine ⟨897216690782011581179093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2392577842085364216477581 897216690782011581179093)
              ·
                refine ⟨21028516190203396433885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 897216690782011581179093 21028516190203396433885)
                ·
                  rfl

theorem cell20_138216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_138216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138216 prefixEnd_138216 := by exact prefixLift 138216
  have htrace : WordTrace (prefixWord ++ tailWord_138216) baseStart_138216 baseEnd_138216 := by
    simpa [prefixWord, tailWord_138216, baseEnd_138216] using wordTrace_append hprefix tailTrace_138216
  have hstable : (prefixWord ++ tailWord_138216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138216).length < 2 ^ (prefixWord ++ tailWord_138216).sum := by decide
  have hdescent : baseEnd_138216 < baseStart_138216 := by decide
  rcases family_descends (prefixWord ++ tailWord_138216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138254 : List Nat := [4, 1, 1, 2, 2, 10]
def baseStart_138254 : Nat := 118140960795 + 138254 * 2 ^ 59
def prefixEnd_138254 : Nat := 4983230072969 + 3 ^ 40 * 138254 * 2
def baseEnd_138254 : Nat := 2337144178001886890179

theorem tailTrace_138254 : CollatzResearch.WordTrace tailWord_138254 prefixEnd_138254 2337144178001886890179 := by
  unfold tailWord_138254
  simp only [CollatzResearch.WordTrace]
  refine ⟨630317205142105593558727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3361691760757896498979877 630317205142105593558727)
  ·
    refine ⟨945475807713158390338091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 630317205142105593558727 945475807713158390338091)
    ·
      refine ⟨1418213711569737585507137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 945475807713158390338091 1418213711569737585507137)
      ·
        refine ⟨1063660283677303189130353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1418213711569737585507137 1063660283677303189130353)
        ·
          refine ⟨797745212757977391847765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1063660283677303189130353 797745212757977391847765)
          ·
            refine ⟨2337144178001886890179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 797745212757977391847765 2337144178001886890179)
            ·
              rfl

theorem cell20_138254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 10].length) (baseStart_138254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138254 prefixEnd_138254 := by exact prefixLift 138254
  have htrace : WordTrace (prefixWord ++ tailWord_138254) baseStart_138254 baseEnd_138254 := by
    simpa [prefixWord, tailWord_138254, baseEnd_138254] using wordTrace_append hprefix tailTrace_138254
  have hstable : (prefixWord ++ tailWord_138254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138254).length < 2 ^ (prefixWord ++ tailWord_138254).sum := by decide
  have hdescent : baseEnd_138254 < baseStart_138254 := by decide
  rcases family_descends (prefixWord ++ tailWord_138254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138271 : List Nat := [1, 1, 2, 4, 1, 5, 1, 5]
def baseStart_138271 : Nat := 118140960795 + 138271 * 2 ^ 59
def prefixEnd_138271 : Nat := 4983230072969 + 3 ^ 40 * 138271 * 2
def baseEnd_138271 : Nat := 21036884023091480822699

theorem tailTrace_138271 : CollatzResearch.WordTrace tailWord_138271 prefixEnd_138271 21036884023091480822699 := by
  unfold tailWord_138271
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043157682075256651838667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3362105121383504434559111 5043157682075256651838667)
  ·
    refine ⟨7564736523112884977758001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5043157682075256651838667 7564736523112884977758001)
    ·
      refine ⟨5673552392334663733318501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7564736523112884977758001 5673552392334663733318501)
      ·
        refine ⟨1063791073562749449997219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5673552392334663733318501 1063791073562749449997219)
        ·
          refine ⟨1595686610344124174995829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063791073562749449997219 1595686610344124174995829)
          ·
            refine ⟨149595619719761641405859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1595686610344124174995829 149595619719761641405859)
            ·
              refine ⟨224393429579642462108789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149595619719761641405859 224393429579642462108789)
              ·
                refine ⟨21036884023091480822699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 224393429579642462108789 21036884023091480822699)
                ·
                  rfl

theorem cell20_138271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 5].length) (baseStart_138271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138271 prefixEnd_138271 := by exact prefixLift 138271
  have htrace : WordTrace (prefixWord ++ tailWord_138271) baseStart_138271 baseEnd_138271 := by
    simpa [prefixWord, tailWord_138271, baseEnd_138271] using wordTrace_append hprefix tailTrace_138271
  have hstable : (prefixWord ++ tailWord_138271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138271).length < 2 ^ (prefixWord ++ tailWord_138271).sum := by decide
  have hdescent : baseEnd_138271 < baseStart_138271 := by decide
  rcases family_descends (prefixWord ++ tailWord_138271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138489 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_138489 : Nat := 118140960795 + 138489 * 2 ^ 59
def prefixEnd_138489 : Nat := 4983230072969 + 3 ^ 40 * 138489 * 2
def baseEnd_138489 : Nat := 63210153209434573200539

theorem tailTrace_138489 : CollatzResearch.WordTrace tailWord_138489 prefixEnd_138489 63210153209434573200539 := by
  unfold tailWord_138489
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051108795285479883274521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3367405863523653255516347 5051108795285479883274521)
  ·
    refine ⟨3788331596464109912455891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5051108795285479883274521 3788331596464109912455891)
    ·
      refine ⟨5682497394696164868683837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3788331596464109912455891 5682497394696164868683837)
      ·
        refine ⟨2130936523011061825756439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5682497394696164868683837 2130936523011061825756439)
        ·
          refine ⟨3196404784516592738634659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130936523011061825756439 3196404784516592738634659)
          ·
            refine ⟨4794607176774889107951989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196404784516592738634659 4794607176774889107951989)
            ·
              refine ⟨449494422822645853870499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4794607176774889107951989 449494422822645853870499)
              ·
                refine ⟨674241634233968780805749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449494422822645853870499 674241634233968780805749)
                ·
                  refine ⟨63210153209434573200539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 674241634233968780805749 63210153209434573200539)
                  ·
                    rfl

theorem cell20_138489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_138489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138489 prefixEnd_138489 := by exact prefixLift 138489
  have htrace : WordTrace (prefixWord ++ tailWord_138489) baseStart_138489 baseEnd_138489 := by
    simpa [prefixWord, tailWord_138489, baseEnd_138489] using wordTrace_append hprefix tailTrace_138489
  have hstable : (prefixWord ++ tailWord_138489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138489).length < 2 ^ (prefixWord ++ tailWord_138489).sum := by decide
  have hdescent : baseEnd_138489 < baseStart_138489 := by decide
  rcases family_descends (prefixWord ++ tailWord_138489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138492 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_138492 : Nat := 118140960795 + 138492 * 2 ^ 59
def prefixEnd_138492 : Nat := 4983230072969 + 3 ^ 40 * 138492 * 2
def baseEnd_138492 : Nat := 63211522491179896100527

theorem tailTrace_138492 : CollatzResearch.WordTrace tailWord_138492 prefixEnd_138492 63211522491179896100527 := by
  unfold tailWord_138492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2525609107137305697816865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3367478809516407597089153 2525609107137305697816865)
  ·
    refine ⟨1894206830352979273362649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2525609107137305697816865 1894206830352979273362649)
    ·
      refine ⟨1420655122764734455021987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1894206830352979273362649 1420655122764734455021987)
      ·
        refine ⟨2130982684147101682532981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420655122764734455021987 2130982684147101682532981)
        ·
          refine ⟨199779626638790782737467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2130982684147101682532981 199779626638790782737467)
          ·
            refine ⟨299669439958186174106201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199779626638790782737467 299669439958186174106201)
            ·
              refine ⟨224752079968639630579651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299669439958186174106201 224752079968639630579651)
              ·
                refine ⟨337128119952959445869477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224752079968639630579651 337128119952959445869477)
                ·
                  refine ⟨63211522491179896100527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337128119952959445869477 63211522491179896100527)
                  ·
                    rfl

theorem cell20_138492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_138492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138492 prefixEnd_138492 := by exact prefixLift 138492
  have htrace : WordTrace (prefixWord ++ tailWord_138492) baseStart_138492 baseEnd_138492 := by
    simpa [prefixWord, tailWord_138492, baseEnd_138492] using wordTrace_append hprefix tailTrace_138492
  have hstable : (prefixWord ++ tailWord_138492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138492).length < 2 ^ (prefixWord ++ tailWord_138492).sum := by decide
  have hdescent : baseEnd_138492 < baseStart_138492 := by decide
  rcases family_descends (prefixWord ++ tailWord_138492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138520 : List Nat := [2, 1, 2, 3, 1, 4, 1, 6]
def baseStart_138520 : Nat := 118140960795 + 138520 * 2 ^ 59
def prefixEnd_138520 : Nat := 4983230072969 + 3 ^ 40 * 138520 * 2
def baseEnd_138520 : Nat := 21074767484712081055693

theorem tailTrace_138520 : CollatzResearch.WordTrace tailWord_138520 prefixEnd_138520 21074767484712081055693 := by
  unfold tailWord_138520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526119729086586088826507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3368159638782114785102009 2526119729086586088826507)
  ·
    refine ⟨3789179593629879133239761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2526119729086586088826507 3789179593629879133239761)
    ·
      refine ⟨2841884695222409349929821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3789179593629879133239761 2841884695222409349929821)
      ·
        refine ⟨1065706760708403506223683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2841884695222409349929821 1065706760708403506223683)
        ·
          refine ⟨1598560141062605259335525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065706760708403506223683 1598560141062605259335525)
          ·
            refine ⟨299730026449238486125411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1598560141062605259335525 299730026449238486125411)
            ·
              refine ⟨449595039673857729188117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299730026449238486125411 449595039673857729188117)
              ·
                refine ⟨21074767484712081055693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 449595039673857729188117 21074767484712081055693)
                ·
                  rfl

theorem cell20_138520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_138520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138520 prefixEnd_138520 := by exact prefixLift 138520
  have htrace : WordTrace (prefixWord ++ tailWord_138520) baseStart_138520 baseEnd_138520 := by
    simpa [prefixWord, tailWord_138520, baseEnd_138520] using wordTrace_append hprefix tailTrace_138520
  have hstable : (prefixWord ++ tailWord_138520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138520).length < 2 ^ (prefixWord ++ tailWord_138520).sum := by decide
  have hdescent : baseEnd_138520 < baseStart_138520 := by decide
  rcases family_descends (prefixWord ++ tailWord_138520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138547 : List Nat := [1, 1, 1, 2, 5, 3, 3, 2, 2]
def baseStart_138547 : Nat := 118140960795 + 138547 * 2 ^ 59
def prefixEnd_138547 : Nat := 4983230072969 + 3 ^ 40 * 138547 * 2
def baseEnd_138547 : Nat := 63236625989844149266969

theorem tailTrace_138547 : CollatzResearch.WordTrace tailWord_138547 prefixEnd_138547 63236625989844149266969 := by
  unfold tailWord_138547
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053224229075355788885895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3368816152716903859257263 5053224229075355788885895)
  ·
    refine ⟨7579836343613033683328843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5053224229075355788885895 7579836343613033683328843)
    ·
      refine ⟨11369754515419550524993265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7579836343613033683328843 11369754515419550524993265)
      ·
        refine ⟨8527315886564662893744949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11369754515419550524993265 8527315886564662893744949)
        ·
          refine ⟨799435864365437146288589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8527315886564662893744949 799435864365437146288589)
          ·
            refine ⟨299788449137038929858221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 799435864365437146288589 299788449137038929858221)
            ·
              refine ⟨112420668426389598696833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299788449137038929858221 112420668426389598696833)
              ·
                refine ⟨84315501319792199022625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112420668426389598696833 84315501319792199022625)
                ·
                  refine ⟨63236625989844149266969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84315501319792199022625 63236625989844149266969)
                  ·
                    rfl

theorem cell20_138547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 2].length) (baseStart_138547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138547 prefixEnd_138547 := by exact prefixLift 138547
  have htrace : WordTrace (prefixWord ++ tailWord_138547) baseStart_138547 baseEnd_138547 := by
    simpa [prefixWord, tailWord_138547, baseEnd_138547] using wordTrace_append hprefix tailTrace_138547
  have hstable : (prefixWord ++ tailWord_138547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138547).length < 2 ^ (prefixWord ++ tailWord_138547).sum := by decide
  have hdescent : baseEnd_138547 < baseStart_138547 := by decide
  rcases family_descends (prefixWord ++ tailWord_138547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138557 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 3]
def baseStart_138557 : Nat := 118140960795 + 138557 * 2 ^ 59
def prefixEnd_138557 : Nat := 4983230072969 + 3 ^ 40 * 138557 * 2
def baseEnd_138557 : Nat := 63241190262328558933595

theorem tailTrace_138557 : CollatzResearch.WordTrace tailWord_138557 prefixEnd_138557 63241190262328558933595 := by
  unfold tailWord_138557
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053588959039127496749925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3369059306026084997833283 5053588959039127496749925)
  ·
    refine ⟨947547929819836405640611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5053588959039127496749925 947547929819836405640611)
    ·
      refine ⟨1421321894729754608460917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 947547929819836405640611 1421321894729754608460917)
      ·
        refine ⟨133248927630914494543211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1421321894729754608460917 133248927630914494543211)
        ·
          refine ⟨199873391446371741814817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133248927630914494543211 199873391446371741814817)
          ·
            refine ⟨149905043584778806361113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199873391446371741814817 149905043584778806361113)
            ·
              refine ⟨112428782688584104770835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149905043584778806361113 112428782688584104770835)
              ·
                refine ⟨168643174032876157156253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112428782688584104770835 168643174032876157156253)
                ·
                  refine ⟨63241190262328558933595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168643174032876157156253 63241190262328558933595)
                  ·
                    rfl

theorem cell20_138557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_138557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138557 prefixEnd_138557 := by exact prefixLift 138557
  have htrace : WordTrace (prefixWord ++ tailWord_138557) baseStart_138557 baseEnd_138557 := by
    simpa [prefixWord, tailWord_138557, baseEnd_138557] using wordTrace_append hprefix tailTrace_138557
  have hstable : (prefixWord ++ tailWord_138557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138557).length < 2 ^ (prefixWord ++ tailWord_138557).sum := by decide
  have hdescent : baseEnd_138557 < baseStart_138557 := by decide
  rcases family_descends (prefixWord ++ tailWord_138557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138561 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 3]
def baseStart_138561 : Nat := 118140960795 + 138561 * 2 ^ 59
def prefixEnd_138561 : Nat := 4983230072969 + 3 ^ 40 * 138561 * 2
def baseEnd_138561 : Nat := 63243015971322322800245

theorem tailTrace_138561 : CollatzResearch.WordTrace tailWord_138561 prefixEnd_138561 63243015971322322800245 := by
  unfold tailWord_138561
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053734851024636179895537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3369156567349757453263691 5053734851024636179895537)
  ·
    refine ⟨3790301138268477134921653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5053734851024636179895537 3790301138268477134921653)
    ·
      refine ⟨355340731712669731398905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3790301138268477134921653 355340731712669731398905)
      ·
        refine ⟨266505548784502298549179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 355340731712669731398905 266505548784502298549179)
        ·
          refine ⟨399758323176753447823769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266505548784502298549179 399758323176753447823769)
          ·
            refine ⟨299818742382565085867827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399758323176753447823769 299818742382565085867827)
            ·
              refine ⟨449728113573847628801741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299818742382565085867827 449728113573847628801741)
              ·
                refine ⟨168648042590192860800653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 449728113573847628801741 168648042590192860800653)
                ·
                  refine ⟨63243015971322322800245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168648042590192860800653 63243015971322322800245)
                  ·
                    rfl

theorem cell20_138561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_138561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138561 prefixEnd_138561 := by exact prefixLift 138561
  have htrace : WordTrace (prefixWord ++ tailWord_138561) baseStart_138561 baseEnd_138561 := by
    simpa [prefixWord, tailWord_138561, baseEnd_138561] using wordTrace_append hprefix tailTrace_138561
  have hstable : (prefixWord ++ tailWord_138561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138561).length < 2 ^ (prefixWord ++ tailWord_138561).sum := by decide
  have hdescent : baseEnd_138561 < baseStart_138561 := by decide
  rcases family_descends (prefixWord ++ tailWord_138561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138579 : List Nat := [1, 1, 1, 2, 1, 1, 5, 8]
def baseStart_138579 : Nat := 118140960795 + 138579 * 2 ^ 59
def prefixEnd_138579 : Nat := 4983230072969 + 3 ^ 40 * 138579 * 2
def baseEnd_138579 : Nat := 21083743887264753400057

theorem tailTrace_138579 : CollatzResearch.WordTrace tailWord_138579 prefixEnd_138579 21083743887264753400057 := by
  unfold tailWord_138579
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054391364959425254050791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3369594243306283502700527 5054391364959425254050791)
  ·
    refine ⟨7581587047439137881076187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5054391364959425254050791 7581587047439137881076187)
    ·
      refine ⟨11372380571158706821614281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7581587047439137881076187 11372380571158706821614281)
      ·
        refine ⟨8529285428369030116210711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11372380571158706821614281 8529285428369030116210711)
        ·
          refine ⟨12793928142553545174316067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8529285428369030116210711 12793928142553545174316067)
          ·
            refine ⟨19190892213830317761474101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12793928142553545174316067 19190892213830317761474101)
            ·
              refine ⟨1799146145046592290138197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19190892213830317761474101 1799146145046592290138197)
              ·
                refine ⟨21083743887264753400057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1799146145046592290138197 21083743887264753400057)
                ·
                  rfl

theorem cell20_138579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_138579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138579 prefixEnd_138579 := by exact prefixLift 138579
  have htrace : WordTrace (prefixWord ++ tailWord_138579) baseStart_138579 baseEnd_138579 := by
    simpa [prefixWord, tailWord_138579, baseEnd_138579] using wordTrace_append hprefix tailTrace_138579
  have hstable : (prefixWord ++ tailWord_138579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138579).length < 2 ^ (prefixWord ++ tailWord_138579).sum := by decide
  have hdescent : baseEnd_138579 < baseStart_138579 := by decide
  rcases family_descends (prefixWord ++ tailWord_138579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138599 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 3]
def baseStart_138599 : Nat := 118140960795 + 138599 * 2 ^ 59
def prefixEnd_138599 : Nat := 4983230072969 + 3 ^ 40 * 138599 * 2
def baseEnd_138599 : Nat := 63260360206763079533423

theorem tailTrace_138599 : CollatzResearch.WordTrace tailWord_138599 prefixEnd_138599 63260360206763079533423 := by
  unfold tailWord_138599
  simp only [CollatzResearch.WordTrace]
  refine ⟨5055120824886968669778851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3370080549924645779852567 5055120824886968669778851)
  ·
    refine ⟨7582681237330453004668277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5055120824886968669778851 7582681237330453004668277)
    ·
      refine ⟨710876365999729969187651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7582681237330453004668277 710876365999729969187651)
      ·
        refine ⟨1066314548999594953781477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710876365999729969187651 1066314548999594953781477)
        ·
          refine ⟨199933977937424053834027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1066314548999594953781477 199933977937424053834027)
          ·
            refine ⟨299900966906136080751041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199933977937424053834027 299900966906136080751041)
            ·
              refine ⟨224925725179602060563281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299900966906136080751041 224925725179602060563281)
              ·
                refine ⟨168694293884701545422461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224925725179602060563281 168694293884701545422461)
                ·
                  refine ⟨63260360206763079533423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168694293884701545422461 63260360206763079533423)
                  ·
                    rfl

theorem cell20_138599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_138599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138599 prefixEnd_138599 := by exact prefixLift 138599
  have htrace : WordTrace (prefixWord ++ tailWord_138599) baseStart_138599 baseEnd_138599 := by
    simpa [prefixWord, tailWord_138599, baseEnd_138599] using wordTrace_append hprefix tailTrace_138599
  have hstable : (prefixWord ++ tailWord_138599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138599).length < 2 ^ (prefixWord ++ tailWord_138599).sum := by decide
  have hdescent : baseEnd_138599 < baseStart_138599 := by decide
  rcases family_descends (prefixWord ++ tailWord_138599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138627 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_138627 : Nat := 118140960795 + 138627 * 2 ^ 59
def prefixEnd_138627 : Nat := 4983230072969 + 3 ^ 40 * 138627 * 2
def baseEnd_138627 : Nat := 63273140169719426599975

theorem tailTrace_138627 : CollatzResearch.WordTrace tailWord_138627 prefixEnd_138627 63273140169719426599975 := by
  unfold tailWord_138627
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056142068785529451798135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3370761379190352967865423 5056142068785529451798135)
  ·
    refine ⟨7584213103178294177697203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5056142068785529451798135 7584213103178294177697203)
    ·
      refine ⟨11376319654767441266545805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7584213103178294177697203 11376319654767441266545805)
      ·
        refine ⟨4266119870537790474954677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11376319654767441266545805 4266119870537790474954677)
        ·
          refine ⟨399948737862917857027001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4266119870537790474954677 399948737862917857027001)
          ·
            refine ⟨299961553397188392770251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399948737862917857027001 299961553397188392770251)
            ·
              refine ⟨449942330095782589155377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299961553397188392770251 449942330095782589155377)
              ·
                refine ⟨337456747571836941866533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449942330095782589155377 337456747571836941866533)
                ·
                  refine ⟨63273140169719426599975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337456747571836941866533 63273140169719426599975)
                  ·
                    rfl

theorem cell20_138627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_138627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138627 prefixEnd_138627 := by exact prefixLift 138627
  have htrace : WordTrace (prefixWord ++ tailWord_138627) baseStart_138627 baseEnd_138627 := by
    simpa [prefixWord, tailWord_138627, baseEnd_138627] using wordTrace_append hprefix tailTrace_138627
  have hstable : (prefixWord ++ tailWord_138627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138627).length < 2 ^ (prefixWord ++ tailWord_138627).sum := by decide
  have hdescent : baseEnd_138627 < baseStart_138627 := by decide
  rcases family_descends (prefixWord ++ tailWord_138627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138658 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_138658 : Nat := 118140960795 + 138658 * 2 ^ 59
def prefixEnd_138658 : Nat := 4983230072969 + 3 ^ 40 * 138658 * 2
def baseEnd_138658 : Nat := 63287289414421096566515

theorem tailTrace_138658 : CollatzResearch.WordTrace tailWord_138658 prefixEnd_138658 63287289414421096566515 := by
  unfold tailWord_138658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264318182918305436544157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3371515154448814497451085 1264318182918305436544157)
  ·
    refine ⟨474119318594364538704059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1264318182918305436544157 474119318594364538704059)
    ·
      refine ⟨711178977891546808056089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474119318594364538704059 711178977891546808056089)
      ·
        refine ⟨533384233418660106042067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 711178977891546808056089 533384233418660106042067)
        ·
          refine ⟨800076350127990159063101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533384233418660106042067 800076350127990159063101)
          ·
            refine ⟨300028631297996309648663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 800076350127990159063101 300028631297996309648663)
            ·
              refine ⟨450042946946994464472995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300028631297996309648663 450042946946994464472995)
              ·
                refine ⟨675064420420491696709493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450042946946994464472995 675064420420491696709493)
                ·
                  refine ⟨63287289414421096566515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 675064420420491696709493 63287289414421096566515)
                  ·
                    rfl

theorem cell20_138658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_138658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138658 prefixEnd_138658 := by exact prefixLift 138658
  have htrace : WordTrace (prefixWord ++ tailWord_138658) baseStart_138658 baseEnd_138658 := by
    simpa [prefixWord, tailWord_138658, baseEnd_138658] using wordTrace_append hprefix tailTrace_138658
  have hstable : (prefixWord ++ tailWord_138658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138658).length < 2 ^ (prefixWord ++ tailWord_138658).sum := by decide
  have hdescent : baseEnd_138658 < baseStart_138658 := by decide
  rcases family_descends (prefixWord ++ tailWord_138658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138730 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_138730 : Nat := 118140960795 + 138730 * 2 ^ 59
def prefixEnd_138730 : Nat := 4983230072969 + 3 ^ 40 * 138730 * 2
def baseEnd_138730 : Nat := 63320152176308846166221

theorem tailTrace_138730 : CollatzResearch.WordTrace tailWord_138730 prefixEnd_138730 63320152176308846166221 := by
  unfold tailWord_138730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264974696853094510699411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3373265858274918695198429 1264974696853094510699411)
  ·
    refine ⟨1897462045279641766049117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1264974696853094510699411 1897462045279641766049117)
    ·
      refine ⟨711548266979865662268419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1897462045279641766049117 711548266979865662268419)
      ·
        refine ⟨1067322400469798493402629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711548266979865662268419 1067322400469798493402629)
        ·
          refine ⟨200122950088087217512993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1067322400469798493402629 200122950088087217512993)
          ·
            refine ⟨150092212566065413134745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200122950088087217512993 150092212566065413134745)
            ·
              refine ⟨112569159424549059851059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150092212566065413134745 112569159424549059851059)
              ·
                refine ⟨168853739136823589776589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112569159424549059851059 168853739136823589776589)
                ·
                  refine ⟨63320152176308846166221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168853739136823589776589 63320152176308846166221)
                  ·
                    rfl

theorem cell20_138730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_138730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138730 prefixEnd_138730 := by exact prefixLift 138730
  have htrace : WordTrace (prefixWord ++ tailWord_138730) baseStart_138730 baseEnd_138730 := by
    simpa [prefixWord, tailWord_138730, baseEnd_138730] using wordTrace_append hprefix tailTrace_138730
  have hstable : (prefixWord ++ tailWord_138730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138730).length < 2 ^ (prefixWord ++ tailWord_138730).sum := by decide
  have hdescent : baseEnd_138730 < baseStart_138730 := by decide
  rcases family_descends (prefixWord ++ tailWord_138730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138734 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_138734 : Nat := 118140960795 + 138734 * 2 ^ 59
def prefixEnd_138734 : Nat := 4983230072969 + 3 ^ 40 * 138734 * 2
def baseEnd_138734 : Nat := 63321977885302610032871

theorem tailTrace_138734 : CollatzResearch.WordTrace tailWord_138734 prefixEnd_138734 63321977885302610032871 := by
  unfold tailWord_138734
  simp only [CollatzResearch.WordTrace]
  refine ⟨632505584924735840742907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3373363119598591150628837 632505584924735840742907)
  ·
    refine ⟨948758377387103761114361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 632505584924735840742907 948758377387103761114361)
    ·
      refine ⟨711568783040327820835771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 948758377387103761114361 711568783040327820835771)
      ·
        refine ⟨1067353174560491731253657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711568783040327820835771 1067353174560491731253657)
        ·
          refine ⟨800514880920368798440243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1067353174560491731253657 800514880920368798440243)
          ·
            refine ⟨1200772321380553197660365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800514880920368798440243 1200772321380553197660365)
            ·
              refine ⟨450289620517707449122637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1200772321380553197660365 450289620517707449122637)
              ·
                refine ⟨168858607694140293420989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 450289620517707449122637 168858607694140293420989)
                ·
                  refine ⟨63321977885302610032871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168858607694140293420989 63321977885302610032871)
                  ·
                    rfl

theorem cell20_138734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_138734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138734 prefixEnd_138734 := by exact prefixLift 138734
  have htrace : WordTrace (prefixWord ++ tailWord_138734) baseStart_138734 baseEnd_138734 := by
    simpa [prefixWord, tailWord_138734, baseEnd_138734] using wordTrace_append hprefix tailTrace_138734
  have hstable : (prefixWord ++ tailWord_138734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138734).length < 2 ^ (prefixWord ++ tailWord_138734).sum := by decide
  have hdescent : baseEnd_138734 < baseStart_138734 := by decide
  rcases family_descends (prefixWord ++ tailWord_138734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138765 : List Nat := [1, 7, 1, 1, 10]
def baseStart_138765 : Nat := 118140960795 + 138765 * 2 ^ 59
def prefixEnd_138765 : Nat := 4983230072969 + 3 ^ 40 * 138765 * 2
def baseEnd_138765 : Nat := 781927495432151604931

theorem tailTrace_138765 : CollatzResearch.WordTrace tailWord_138765 prefixEnd_138765 781927495432151604931 := by
  unfold tailWord_138765
  simp only [CollatzResearch.WordTrace]
  refine ⟨5061175342285579020321749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3374116894857052680214499 5061175342285579020321749)
  ·
    refine ⟨118621297084818258288791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 5061175342285579020321749 118621297084818258288791)
    ·
      refine ⟨177931945627227387433187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118621297084818258288791 177931945627227387433187)
      ·
        refine ⟨266897918440841081149781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177931945627227387433187 266897918440841081149781)
        ·
          refine ⟨781927495432151604931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 266897918440841081149781 781927495432151604931)
          ·
            rfl

theorem cell20_138765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 10].length) (baseStart_138765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138765 prefixEnd_138765 := by exact prefixLift 138765
  have htrace : WordTrace (prefixWord ++ tailWord_138765) baseStart_138765 baseEnd_138765 := by
    simpa [prefixWord, tailWord_138765, baseEnd_138765] using wordTrace_append hprefix tailTrace_138765
  have hstable : (prefixWord ++ tailWord_138765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138765).length < 2 ^ (prefixWord ++ tailWord_138765).sum := by decide
  have hdescent : baseEnd_138765 < baseStart_138765 := by decide
  rcases family_descends (prefixWord ++ tailWord_138765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138786 : List Nat := [3, 3, 1, 1, 1, 1, 5, 5]
def baseStart_138786 : Nat := 118140960795 + 138786 * 2 ^ 59
def prefixEnd_138786 : Nat := 4983230072969 + 3 ^ 40 * 138786 * 2
def baseEnd_138786 : Nat := 21115237367407180099775

theorem tailTrace_138786 : CollatzResearch.WordTrace tailWord_138786 prefixEnd_138786 21115237367407180099775 := by
  unfold tailWord_138786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265485318802374901709053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3374627516806333071224141 1265485318802374901709053)
  ·
    refine ⟨474556994550890588140895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1265485318802374901709053 474556994550890588140895)
    ·
      refine ⟨711835491826335882211343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474556994550890588140895 711835491826335882211343)
      ·
        refine ⟨1067753237739503823317015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711835491826335882211343 1067753237739503823317015)
        ·
          refine ⟨1601629856609255734975523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067753237739503823317015 1601629856609255734975523)
          ·
            refine ⟨2402444784913883602463285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601629856609255734975523 2402444784913883602463285)
            ·
              refine ⟨225229198585676587730933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2402444784913883602463285 225229198585676587730933)
              ·
                refine ⟨21115237367407180099775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 225229198585676587730933 21115237367407180099775)
                ·
                  rfl

theorem cell20_138786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_138786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138786 prefixEnd_138786 := by exact prefixLift 138786
  have htrace : WordTrace (prefixWord ++ tailWord_138786) baseStart_138786 baseEnd_138786 := by
    simpa [prefixWord, tailWord_138786, baseEnd_138786] using wordTrace_append hprefix tailTrace_138786
  have hstable : (prefixWord ++ tailWord_138786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138786).length < 2 ^ (prefixWord ++ tailWord_138786).sum := by decide
  have hdescent : baseEnd_138786 < baseStart_138786 := by decide
  rcases family_descends (prefixWord ++ tailWord_138786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138813 : List Nat := [1, 4, 1, 3, 3, 1, 2, 3, 2]
def baseStart_138813 : Nat := 118140960795 + 138813 * 2 ^ 59
def prefixEnd_138813 : Nat := 4983230072969 + 3 ^ 40 * 138813 * 2
def baseEnd_138813 : Nat := 63358035637929446399215

theorem tailTrace_138813 : CollatzResearch.WordTrace tailWord_138813 prefixEnd_138813 63358035637929446399215 := by
  unfold tailWord_138813
  simp only [CollatzResearch.WordTrace]
  refine ⟨5062926046111683218069093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3375284030741122145379395 5062926046111683218069093)
  ·
    refine ⟨949298633645940603387955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5062926046111683218069093 949298633645940603387955)
    ·
      refine ⟨1423947950468910905081933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 949298633645940603387955 1423947950468910905081933)
      ·
        refine ⟨533980481425841589405725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1423947950468910905081933 533980481425841589405725)
        ·
          refine ⟨200242680534690596027147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 533980481425841589405725 200242680534690596027147)
          ·
            refine ⟨300364020802035894040721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200242680534690596027147 300364020802035894040721)
            ·
              refine ⟨225273015601526920530541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300364020802035894040721 225273015601526920530541)
              ·
                refine ⟨84477380850572595198953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225273015601526920530541 84477380850572595198953)
                ·
                  refine ⟨63358035637929446399215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84477380850572595198953 63358035637929446399215)
                  ·
                    rfl

theorem cell20_138813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_138813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138813 prefixEnd_138813 := by exact prefixLift 138813
  have htrace : WordTrace (prefixWord ++ tailWord_138813) baseStart_138813 baseEnd_138813 := by
    simpa [prefixWord, tailWord_138813, baseEnd_138813] using wordTrace_append hprefix tailTrace_138813
  have hstable : (prefixWord ++ tailWord_138813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138813).length < 2 ^ (prefixWord ++ tailWord_138813).sum := by decide
  have hdescent : baseEnd_138813 < baseStart_138813 := by decide
  rcases family_descends (prefixWord ++ tailWord_138813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138834 : List Nat := [3, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_138834 : Nat := 118140960795 + 138834 * 2 ^ 59
def prefixEnd_138834 : Nat := 4983230072969 + 3 ^ 40 * 138834 * 2
def baseEnd_138834 : Nat := 63367620610146706699129

theorem tailTrace_138834 : CollatzResearch.WordTrace tailWord_138834 prefixEnd_138834 63367620610146706699129 := by
  unfold tailWord_138834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265922994758900951145889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3375794652690402536389037 1265922994758900951145889)
  ·
    refine ⟨949442246069175713359417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1265922994758900951145889 949442246069175713359417)
    ·
      refine ⟨712081684551881785019563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 949442246069175713359417 712081684551881785019563)
      ·
        refine ⟨1068122526827822677529345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712081684551881785019563 1068122526827822677529345)
        ·
          refine ⟨801091895120867008147009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1068122526827822677529345 801091895120867008147009)
          ·
            refine ⟨600818921340650256110257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 801091895120867008147009 600818921340650256110257)
            ·
              refine ⟨450614191005487692082693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600818921340650256110257 450614191005487692082693)
              ·
                refine ⟨84490160813528942265505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450614191005487692082693 84490160813528942265505)
                ·
                  refine ⟨63367620610146706699129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84490160813528942265505 63367620610146706699129)
                  ·
                    rfl

theorem cell20_138834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_138834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138834 prefixEnd_138834 := by exact prefixLift 138834
  have htrace : WordTrace (prefixWord ++ tailWord_138834) baseStart_138834 baseEnd_138834 := by
    simpa [prefixWord, tailWord_138834, baseEnd_138834] using wordTrace_append hprefix tailTrace_138834
  have hstable : (prefixWord ++ tailWord_138834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138834).length < 2 ^ (prefixWord ++ tailWord_138834).sum := by decide
  have hdescent : baseEnd_138834 < baseStart_138834 := by decide
  rcases family_descends (prefixWord ++ tailWord_138834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138903 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 3]
def baseStart_138903 : Nat := 118140960795 + 138903 * 2 ^ 59
def prefixEnd_138903 : Nat := 4983230072969 + 3 ^ 40 * 138903 * 2
def baseEnd_138903 : Nat := 63399114090289133398847

theorem tailTrace_138903 : CollatzResearch.WordTrace tailWord_138903 prefixEnd_138903 63399114090289133398847 := by
  unfold tailWord_138903
  simp only [CollatzResearch.WordTrace]
  refine ⟨5066208615785628588845363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3377472410523752392563575 5066208615785628588845363)
  ·
    refine ⟨7599312923678442883268045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5066208615785628588845363 7599312923678442883268045)
    ·
      refine ⟨2849742346379416081225517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7599312923678442883268045 2849742346379416081225517)
      ·
        refine ⟨1068653379892281030459569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2849742346379416081225517 1068653379892281030459569)
        ·
          refine ⟨801490034919210772844677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1068653379892281030459569 801490034919210772844677)
          ·
            refine ⟨150279381547352019908377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 801490034919210772844677 150279381547352019908377)
            ·
              refine ⟨112709536160514014931283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150279381547352019908377 112709536160514014931283)
              ·
                refine ⟨169064304240771022396925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112709536160514014931283 169064304240771022396925)
                ·
                  refine ⟨63399114090289133398847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169064304240771022396925 63399114090289133398847)
                  ·
                    rfl

theorem cell20_138903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 3].length) (baseStart_138903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138903 prefixEnd_138903 := by exact prefixLift 138903
  have htrace : WordTrace (prefixWord ++ tailWord_138903) baseStart_138903 baseEnd_138903 := by
    simpa [prefixWord, tailWord_138903, baseEnd_138903] using wordTrace_append hprefix tailTrace_138903
  have hstable : (prefixWord ++ tailWord_138903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138903).length < 2 ^ (prefixWord ++ tailWord_138903).sum := by decide
  have hdescent : baseEnd_138903 < baseStart_138903 := by decide
  rcases family_descends (prefixWord ++ tailWord_138903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138928 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_138928 : Nat := 118140960795 + 138928 * 2 ^ 59
def prefixEnd_138928 : Nat := 4983230072969 + 3 ^ 40 * 138928 * 2
def baseEnd_138928 : Nat := 63410524771500157565411

theorem tailTrace_138928 : CollatzResearch.WordTrace tailWord_138928 prefixEnd_138928 63410524771500157565411 := by
  unfold tailWord_138928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533560220347528929252719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3378080293796705239003625 2533560220347528929252719)
  ·
    refine ⟨3800340330521293393879079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2533560220347528929252719 3800340330521293393879079)
    ·
      refine ⟨5700510495781940090818619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3800340330521293393879079 5700510495781940090818619)
      ·
        refine ⟨8550765743672910136227929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5700510495781940090818619 8550765743672910136227929)
        ·
          refine ⟨6413074307754682602170947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8550765743672910136227929 6413074307754682602170947)
          ·
            refine ⟨9619611461632023903256421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6413074307754682602170947 9619611461632023903256421)
            ·
              refine ⟨1803677149056004481860579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9619611461632023903256421 1803677149056004481860579)
              ·
                refine ⟨2705515723584006722790869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803677149056004481860579 2705515723584006722790869)
                ·
                  refine ⟨63410524771500157565411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2705515723584006722790869 63410524771500157565411)
                  ·
                    rfl

theorem cell20_138928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_138928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138928 prefixEnd_138928 := by exact prefixLift 138928
  have htrace : WordTrace (prefixWord ++ tailWord_138928) baseStart_138928 baseEnd_138928 := by
    simpa [prefixWord, tailWord_138928, baseEnd_138928] using wordTrace_append hprefix tailTrace_138928
  have hstable : (prefixWord ++ tailWord_138928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138928).length < 2 ^ (prefixWord ++ tailWord_138928).sum := by decide
  have hdescent : baseEnd_138928 < baseStart_138928 := by decide
  rcases family_descends (prefixWord ++ tailWord_138928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138931 : List Nat := [1, 1, 1, 2, 3, 3, 2, 5, 2]
def baseStart_138931 : Nat := 118140960795 + 138931 * 2 ^ 59
def prefixEnd_138931 : Nat := 4983230072969 + 3 ^ 40 * 138931 * 2
def baseEnd_138931 : Nat := 63411894053245480465399

theorem tailTrace_138931 : CollatzResearch.WordTrace tailWord_138931 prefixEnd_138931 63411894053245480465399 := by
  unfold tailWord_138931
  simp only [CollatzResearch.WordTrace]
  refine ⟨5067229859684189370864647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3378153239789459580576431 5067229859684189370864647)
  ·
    refine ⟨7600844789526284056296971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5067229859684189370864647 7600844789526284056296971)
    ·
      refine ⟨11401267184289426084445457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7600844789526284056296971 11401267184289426084445457)
      ·
        refine ⟨8550950388217069563334093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11401267184289426084445457 8550950388217069563334093)
        ·
          refine ⟨3206606395581401086250285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8550950388217069563334093 3206606395581401086250285)
          ·
            refine ⟨1202477398343025407343857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3206606395581401086250285 1202477398343025407343857)
            ·
              refine ⟨901858048757269055507893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202477398343025407343857 901858048757269055507893)
              ·
                refine ⟨84549192070993973953865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 901858048757269055507893 84549192070993973953865)
                ·
                  refine ⟨63411894053245480465399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84549192070993973953865 63411894053245480465399)
                  ·
                    rfl

theorem cell20_138931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 2].length) (baseStart_138931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138931 prefixEnd_138931 := by exact prefixLift 138931
  have htrace : WordTrace (prefixWord ++ tailWord_138931) baseStart_138931 baseEnd_138931 := by
    simpa [prefixWord, tailWord_138931, baseEnd_138931] using wordTrace_append hprefix tailTrace_138931
  have hstable : (prefixWord ++ tailWord_138931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138931).length < 2 ^ (prefixWord ++ tailWord_138931).sum := by decide
  have hdescent : baseEnd_138931 < baseStart_138931 := by decide
  rcases family_descends (prefixWord ++ tailWord_138931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138948 : List Nat := [2, 3, 3, 1, 1, 1, 3, 4, 2]
def baseStart_138948 : Nat := 118140960795 + 138948 * 2 ^ 59
def prefixEnd_138948 : Nat := 4983230072969 + 3 ^ 40 * 138948 * 2
def baseEnd_138948 : Nat := 63419653316468976898663

theorem tailTrace_138948 : CollatzResearch.WordTrace tailWord_138948 prefixEnd_138948 63419653316468976898663 := by
  unfold tailWord_138948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533924950311300637116749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3378566600415067516155665 2533924950311300637116749)
  ·
    refine ⟨950221856366737738918781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2533924950311300637116749 950221856366737738918781)
    ·
      refine ⟨356333196137526652094543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 950221856366737738918781 356333196137526652094543)
      ·
        refine ⟨534499794206289978141815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356333196137526652094543 534499794206289978141815)
        ·
          refine ⟨801749691309434967212723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534499794206289978141815 801749691309434967212723)
          ·
            refine ⟨1202624536964152450819085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801749691309434967212723 1202624536964152450819085)
            ·
              refine ⟨450984201361557169057157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1202624536964152450819085 450984201361557169057157)
              ·
                refine ⟨84559537755291969198217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 450984201361557169057157 84559537755291969198217)
                ·
                  refine ⟨63419653316468976898663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84559537755291969198217 63419653316468976898663)
                  ·
                    rfl

theorem cell20_138948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_138948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138948 prefixEnd_138948 := by exact prefixLift 138948
  have htrace : WordTrace (prefixWord ++ tailWord_138948) baseStart_138948 baseEnd_138948 := by
    simpa [prefixWord, tailWord_138948, baseEnd_138948] using wordTrace_append hprefix tailTrace_138948
  have hstable : (prefixWord ++ tailWord_138948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138948).length < 2 ^ (prefixWord ++ tailWord_138948).sum := by decide
  have hdescent : baseEnd_138948 < baseStart_138948 := by decide
  rcases family_descends (prefixWord ++ tailWord_138948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138952 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_138952 : Nat := 118140960795 + 138952 * 2 ^ 59
def prefixEnd_138952 : Nat := 4983230072969 + 3 ^ 40 * 138952 * 2
def baseEnd_138952 : Nat := 63421479025462740765313

theorem tailTrace_138952 : CollatzResearch.WordTrace tailWord_138952 prefixEnd_138952 63421479025462740765313 := by
  unfold tailWord_138952
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533997896304054978689555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3378663861738739971586073 2533997896304054978689555)
  ·
    refine ⟨3800996844456082468034333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2533997896304054978689555 3800996844456082468034333)
    ·
      refine ⟨1425373816671030925512875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3800996844456082468034333 1425373816671030925512875)
      ·
        refine ⟨2138060725006546388269313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425373816671030925512875 2138060725006546388269313)
        ·
          refine ⟨1603545543754909791201985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2138060725006546388269313 1603545543754909791201985)
          ·
            refine ⟨1202659157816182343401489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1603545543754909791201985 1202659157816182343401489)
            ·
              refine ⟨901994368362136757551117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1202659157816182343401489 901994368362136757551117)
              ·
                refine ⟨338247888135801284081669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 901994368362136757551117 338247888135801284081669)
                ·
                  refine ⟨63421479025462740765313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338247888135801284081669 63421479025462740765313)
                  ·
                    rfl

theorem cell20_138952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_138952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138952 prefixEnd_138952 := by exact prefixLift 138952
  have htrace : WordTrace (prefixWord ++ tailWord_138952) baseStart_138952 baseEnd_138952 := by
    simpa [prefixWord, tailWord_138952, baseEnd_138952] using wordTrace_append hprefix tailTrace_138952
  have hstable : (prefixWord ++ tailWord_138952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138952).length < 2 ^ (prefixWord ++ tailWord_138952).sum := by decide
  have hdescent : baseEnd_138952 < baseStart_138952 := by decide
  rcases family_descends (prefixWord ++ tailWord_138952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138962 : List Nat := [3, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_138962 : Nat := 118140960795 + 138962 * 2 ^ 59
def prefixEnd_138962 : Nat := 4983230072969 + 3 ^ 40 * 138962 * 2
def baseEnd_138962 : Nat := 63426043297947150431939

theorem tailTrace_138962 : CollatzResearch.WordTrace tailWord_138962 prefixEnd_138962 63426043297947150431939 := by
  unfold tailWord_138962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1267090130642970416310785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3378907015047921110162093 1267090130642970416310785)
  ·
    refine ⟨950317597982227812233089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1267090130642970416310785 950317597982227812233089)
    ·
      refine ⟨712738198486670859174817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 950317597982227812233089 712738198486670859174817)
      ·
        refine ⟨534553648865003144381113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 712738198486670859174817 534553648865003144381113)
        ·
          refine ⟨400915236648752358285835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534553648865003144381113 400915236648752358285835)
          ·
            refine ⟨601372854973128537428753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400915236648752358285835 601372854973128537428753)
            ·
              refine ⟨451029641229846403071565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601372854973128537428753 451029641229846403071565)
              ·
                refine ⟨169136115461192401151837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 451029641229846403071565 169136115461192401151837)
                ·
                  refine ⟨63426043297947150431939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169136115461192401151837 63426043297947150431939)
                  ·
                    rfl

theorem cell20_138962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_138962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138962 prefixEnd_138962 := by exact prefixLift 138962
  have htrace : WordTrace (prefixWord ++ tailWord_138962) baseStart_138962 baseEnd_138962 := by
    simpa [prefixWord, tailWord_138962, baseEnd_138962] using wordTrace_append hprefix tailTrace_138962
  have hstable : (prefixWord ++ tailWord_138962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138962).length < 2 ^ (prefixWord ++ tailWord_138962).sum := by decide
  have hdescent : baseEnd_138962 < baseStart_138962 := by decide
  rcases family_descends (prefixWord ++ tailWord_138962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138972 : List Nat := [2, 2, 5, 1, 2, 1, 3, 4]
def baseStart_138972 : Nat := 118140960795 + 138972 * 2 ^ 59
def prefixEnd_138972 : Nat := 4983230072969 + 3 ^ 40 * 138972 * 2
def baseEnd_138972 : Nat := 21143535856810520032855

theorem tailTrace_138972 : CollatzResearch.WordTrace tailWord_138972 prefixEnd_138972 21143535856810520032855 := by
  unfold tailWord_138972
  simp only [CollatzResearch.WordTrace]
  refine ⟨2534362626267826686553585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3379150168357102248738113 2534362626267826686553585)
  ·
    refine ⟨1900771969700870014915189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2534362626267826686553585 1900771969700870014915189)
    ·
      refine ⟨178197372159456563898299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1900771969700870014915189 178197372159456563898299)
      ·
        refine ⟨267296058239184845847449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178197372159456563898299 267296058239184845847449)
        ·
          refine ⟨200472043679388634385587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267296058239184845847449 200472043679388634385587)
          ·
            refine ⟨300708065519082951578381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200472043679388634385587 300708065519082951578381)
            ·
              refine ⟨112765524569656106841893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 300708065519082951578381 112765524569656106841893)
              ·
                refine ⟨21143535856810520032855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112765524569656106841893 21143535856810520032855)
                ·
                  rfl

theorem cell20_138972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_138972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138972 prefixEnd_138972 := by exact prefixLift 138972
  have htrace : WordTrace (prefixWord ++ tailWord_138972) baseStart_138972 baseEnd_138972 := by
    simpa [prefixWord, tailWord_138972, baseEnd_138972] using wordTrace_append hprefix tailTrace_138972
  have hstable : (prefixWord ++ tailWord_138972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138972).length < 2 ^ (prefixWord ++ tailWord_138972).sum := by decide
  have hdescent : baseEnd_138972 < baseStart_138972 := by decide
  rcases family_descends (prefixWord ++ tailWord_138972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138990 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_138990 : Nat := 118140960795 + 138990 * 2 ^ 59
def prefixEnd_138990 : Nat := 4983230072969 + 3 ^ 40 * 138990 * 2
def baseEnd_138990 : Nat := 63438823260903497498491

theorem tailTrace_138990 : CollatzResearch.WordTrace tailWord_138990 prefixEnd_138990 63438823260903497498491 := by
  unfold tailWord_138990
  simp only [CollatzResearch.WordTrace]
  refine ⟨633672720808805305907803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3379587844313628298174949 633672720808805305907803)
  ·
    refine ⟨950509081213207958861705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 633672720808805305907803 950509081213207958861705)
    ·
      refine ⟨712881810909905969146279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 950509081213207958861705 712881810909905969146279)
      ·
        refine ⟨1069322716364858953719419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712881810909905969146279 1069322716364858953719419)
        ·
          refine ⟨1603984074547288430579129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069322716364858953719419 1603984074547288430579129)
          ·
            refine ⟨1202988055910466322934347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1603984074547288430579129 1202988055910466322934347)
            ·
              refine ⟨1804482083865699484401521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202988055910466322934347 1804482083865699484401521)
              ·
                refine ⟨1353361562899274613301141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1804482083865699484401521 1353361562899274613301141)
                ·
                  refine ⟨63438823260903497498491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1353361562899274613301141 63438823260903497498491)
                  ·
                    rfl

theorem cell20_138990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_138990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138990 prefixEnd_138990 := by exact prefixLift 138990
  have htrace : WordTrace (prefixWord ++ tailWord_138990) baseStart_138990 baseEnd_138990 := by
    simpa [prefixWord, tailWord_138990, baseEnd_138990] using wordTrace_append hprefix tailTrace_138990
  have hstable : (prefixWord ++ tailWord_138990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138990).length < 2 ^ (prefixWord ++ tailWord_138990).sum := by decide
  have hdescent : baseEnd_138990 < baseStart_138990 := by decide
  rcases family_descends (prefixWord ++ tailWord_138990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138996 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 3]
def baseStart_138996 : Nat := 118140960795 + 138996 * 2 ^ 59
def prefixEnd_138996 : Nat := 4983230072969 + 3 ^ 40 * 138996 * 2
def baseEnd_138996 : Nat := 63441561824394143298467

theorem tailTrace_138996 : CollatzResearch.WordTrace tailWord_138996 prefixEnd_138996 63441561824394143298467 := by
  unfold tailWord_138996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2534800302224352735990421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3379733736299136981320561 2534800302224352735990421)
  ·
    refine ⟨118818764166766534499551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2534800302224352735990421 118818764166766534499551)
    ·
      refine ⟨178228146250149801749327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118818764166766534499551 178228146250149801749327)
      ·
        refine ⟨267342219375224702623991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178228146250149801749327 267342219375224702623991)
        ·
          refine ⟨401013329062837053935987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267342219375224702623991 401013329062837053935987)
          ·
            refine ⟨601519993594255580903981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401013329062837053935987 601519993594255580903981)
            ·
              refine ⟨225569997597845842838993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 601519993594255580903981 225569997597845842838993)
              ·
                refine ⟨169177498198384382129245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225569997597845842838993 169177498198384382129245)
                ·
                  refine ⟨63441561824394143298467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169177498198384382129245 63441561824394143298467)
                  ·
                    rfl

theorem cell20_138996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_138996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_138996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_138996 prefixEnd_138996 := by exact prefixLift 138996
  have htrace : WordTrace (prefixWord ++ tailWord_138996) baseStart_138996 baseEnd_138996 := by
    simpa [prefixWord, tailWord_138996, baseEnd_138996] using wordTrace_append hprefix tailTrace_138996
  have hstable : (prefixWord ++ tailWord_138996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138996).length < 2 ^ (prefixWord ++ tailWord_138996).sum := by decide
  have hdescent : baseEnd_138996 < baseStart_138996 := by decide
  rcases family_descends (prefixWord ++ tailWord_138996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139007 : List Nat := [1, 1, 2, 2, 1, 3, 4, 4, 2]
def baseStart_139007 : Nat := 118140960795 + 139007 * 2 ^ 59
def prefixEnd_139007 : Nat := 4983230072969 + 3 ^ 40 * 139007 * 2
def baseEnd_139007 : Nat := 63446582524126993931755

theorem tailTrace_139007 : CollatzResearch.WordTrace tailWord_139007 prefixEnd_139007 63446582524126993931755 := by
  unfold tailWord_139007
  simp only [CollatzResearch.WordTrace]
  refine ⟨5070001807408854350631275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3380001204939236233754183 5070001807408854350631275)
  ·
    refine ⟨7605002711113281525946913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5070001807408854350631275 7605002711113281525946913)
    ·
      refine ⟨5703752033334961144460185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7605002711113281525946913 5703752033334961144460185)
      ·
        refine ⟨4277814025001220858345139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5703752033334961144460185 4277814025001220858345139)
        ·
          refine ⟨6416721037501831287517709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4277814025001220858345139 6416721037501831287517709)
          ·
            refine ⟨2406270389063186732819141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6416721037501831287517709 2406270389063186732819141)
            ·
              refine ⟨451175697949347512403589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2406270389063186732819141 451175697949347512403589)
              ·
                refine ⟨84595443365502658575673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451175697949347512403589 84595443365502658575673)
                ·
                  refine ⟨63446582524126993931755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84595443365502658575673 63446582524126993931755)
                  ·
                    rfl

theorem cell20_139007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 2].length) (baseStart_139007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139007 prefixEnd_139007 := by exact prefixLift 139007
  have htrace : WordTrace (prefixWord ++ tailWord_139007) baseStart_139007 baseEnd_139007 := by
    simpa [prefixWord, tailWord_139007, baseEnd_139007] using wordTrace_append hprefix tailTrace_139007
  have hstable : (prefixWord ++ tailWord_139007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139007).length < 2 ^ (prefixWord ++ tailWord_139007).sum := by decide
  have hdescent : baseEnd_139007 < baseStart_139007 := by decide
  rcases family_descends (prefixWord ++ tailWord_139007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139031 : List Nat := [1, 1, 3, 4, 2, 3, 2, 4]
def baseStart_139031 : Nat := 118140960795 + 139031 * 2 ^ 59
def prefixEnd_139031 : Nat := 4983230072969 + 3 ^ 40 * 139031 * 2
def baseEnd_139031 : Nat := 21152512259363192377219

theorem tailTrace_139031 : CollatzResearch.WordTrace tailWord_139031 prefixEnd_139031 21152512259363192377219 := by
  unfold tailWord_139031
  simp only [CollatzResearch.WordTrace]
  refine ⟨5070877159321906449504947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3380584772881270966336631 5070877159321906449504947)
  ·
    refine ⟨7606315738982859674257421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5070877159321906449504947 7606315738982859674257421)
    ·
      refine ⟨2852368402118572377846533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7606315738982859674257421 2852368402118572377846533)
      ·
        refine ⟨534819075397232320846225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2852368402118572377846533 534819075397232320846225)
        ·
          refine ⟨401114306547924240634669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534819075397232320846225 401114306547924240634669)
          ·
            refine ⟨150417864955471590238001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 401114306547924240634669 150417864955471590238001)
            ·
              refine ⟨112813398716603692678501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150417864955471590238001 112813398716603692678501)
              ·
                refine ⟨21152512259363192377219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112813398716603692678501 21152512259363192377219)
                ·
                  rfl

theorem cell20_139031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 4].length) (baseStart_139031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139031 prefixEnd_139031 := by exact prefixLift 139031
  have htrace : WordTrace (prefixWord ++ tailWord_139031) baseStart_139031 baseEnd_139031 := by
    simpa [prefixWord, tailWord_139031, baseEnd_139031] using wordTrace_append hprefix tailTrace_139031
  have hstable : (prefixWord ++ tailWord_139031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139031).length < 2 ^ (prefixWord ++ tailWord_139031).sum := by decide
  have hdescent : baseEnd_139031 < baseStart_139031 := by decide
  rcases family_descends (prefixWord ++ tailWord_139031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139062 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_139062 : Nat := 118140960795 + 139062 * 2 ^ 59
def prefixEnd_139062 : Nat := 4983230072969 + 3 ^ 40 * 139062 * 2
def baseEnd_139062 : Nat := 63471686022791247098197

theorem tailTrace_139062 : CollatzResearch.WordTrace tailWord_139062 prefixEnd_139062 63471686022791247098197 := by
  unfold tailWord_139062
  simp only [CollatzResearch.WordTrace]
  refine ⟨317000488888099921492715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3381338548139732495922293 317000488888099921492715)
  ·
    refine ⟨475500733332149882239073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317000488888099921492715 475500733332149882239073)
    ·
      refine ⟨356625549999112411679305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 475500733332149882239073 356625549999112411679305)
      ·
        refine ⟨267469162499334308759479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 356625549999112411679305 267469162499334308759479)
        ·
          refine ⟨401203743749001463139219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267469162499334308759479 401203743749001463139219)
          ·
            refine ⟨601805615623502194708829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401203743749001463139219 601805615623502194708829)
            ·
              refine ⟨225677105858813323015811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 601805615623502194708829 225677105858813323015811)
              ·
                refine ⟨338515658788219984523717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225677105858813323015811 338515658788219984523717)
                ·
                  refine ⟨63471686022791247098197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338515658788219984523717 63471686022791247098197)
                  ·
                    rfl

theorem cell20_139062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_139062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139062 prefixEnd_139062 := by exact prefixLift 139062
  have htrace : WordTrace (prefixWord ++ tailWord_139062) baseStart_139062 baseEnd_139062 := by
    simpa [prefixWord, tailWord_139062, baseEnd_139062] using wordTrace_append hprefix tailTrace_139062
  have hstable : (prefixWord ++ tailWord_139062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139062).length < 2 ^ (prefixWord ++ tailWord_139062).sum := by decide
  have hdescent : baseEnd_139062 < baseStart_139062 := by decide
  rcases family_descends (prefixWord ++ tailWord_139062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139121 : List Nat := [1, 2, 2, 2, 1, 3, 3, 4, 2]
def baseStart_139121 : Nat := 118140960795 + 139121 * 2 ^ 59
def prefixEnd_139121 : Nat := 4983230072969 + 3 ^ 40 * 139121 * 2
def baseEnd_139121 : Nat := 63498615230449264131289

theorem tailTrace_139121 : CollatzResearch.WordTrace tailWord_139121 prefixEnd_139121 63498615230449264131289 := by
  unfold tailWord_139121
  simp only [CollatzResearch.WordTrace]
  refine ⟨5074159728995851820281217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3382773152663901213520811 5074159728995851820281217)
  ·
    refine ⟨3805619796746888865210913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5074159728995851820281217 3805619796746888865210913)
    ·
      refine ⟨2854214847560166648908185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3805619796746888865210913 2854214847560166648908185)
      ·
        refine ⟨2140661135670124986681139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2854214847560166648908185 2140661135670124986681139)
        ·
          refine ⟨3210991703505187480021709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2140661135670124986681139 3210991703505187480021709)
          ·
            refine ⟨1204121888814445305008141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3210991703505187480021709 1204121888814445305008141)
            ·
              refine ⟨451545708305416989378053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1204121888814445305008141 451545708305416989378053)
              ·
                refine ⟨84664820307265685508385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 451545708305416989378053 84664820307265685508385)
                ·
                  refine ⟨63498615230449264131289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84664820307265685508385 63498615230449264131289)
                  ·
                    rfl

theorem cell20_139121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_139121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139121 prefixEnd_139121 := by exact prefixLift 139121
  have htrace : WordTrace (prefixWord ++ tailWord_139121) baseStart_139121 baseEnd_139121 := by
    simpa [prefixWord, tailWord_139121, baseEnd_139121] using wordTrace_append hprefix tailTrace_139121
  have hstable : (prefixWord ++ tailWord_139121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139121).length < 2 ^ (prefixWord ++ tailWord_139121).sum := by decide
  have hdescent : baseEnd_139121 < baseStart_139121 := by decide
  rcases family_descends (prefixWord ++ tailWord_139121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139159 : List Nat := [1, 1, 3, 3, 1, 3, 1, 5, 2]
def baseStart_139159 : Nat := 118140960795 + 139159 * 2 ^ 59
def prefixEnd_139159 : Nat := 4983230072969 + 3 ^ 40 * 139159 * 2
def baseEnd_139159 : Nat := 63515959465890020864467

theorem tailTrace_139159 : CollatzResearch.WordTrace tailWord_139159 prefixEnd_139159 63515959465890020864467 := by
  unfold tailWord_139159
  simp only [CollatzResearch.WordTrace]
  refine ⟨5075545702858184310164531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3383697135238789540109687 5075545702858184310164531)
  ·
    refine ⟨7613318554287276465246797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5075545702858184310164531 7613318554287276465246797)
    ·
      refine ⟨2854994457857728674467549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7613318554287276465246797 2854994457857728674467549)
      ·
        refine ⟨1070622921696648252925331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2854994457857728674467549 1070622921696648252925331)
        ·
          refine ⟨1605934382544972379387997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070622921696648252925331 1605934382544972379387997)
          ·
            refine ⟨602225393454364642270499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1605934382544972379387997 602225393454364642270499)
            ·
              refine ⟨903338090181546963405749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602225393454364642270499 903338090181546963405749)
              ·
                refine ⟨84687945954520027819289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 903338090181546963405749 84687945954520027819289)
                ·
                  refine ⟨63515959465890020864467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84687945954520027819289 63515959465890020864467)
                  ·
                    rfl

theorem cell20_139159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 2].length) (baseStart_139159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139159 prefixEnd_139159 := by exact prefixLift 139159
  have htrace : WordTrace (prefixWord ++ tailWord_139159) baseStart_139159 baseEnd_139159 := by
    simpa [prefixWord, tailWord_139159, baseEnd_139159] using wordTrace_append hprefix tailTrace_139159
  have hstable : (prefixWord ++ tailWord_139159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139159).length < 2 ^ (prefixWord ++ tailWord_139159).sum := by decide
  have hdescent : baseEnd_139159 < baseStart_139159 := by decide
  rcases family_descends (prefixWord ++ tailWord_139159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139169 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 3]
def baseStart_139169 : Nat := 118140960795 + 139169 * 2 ^ 59
def prefixEnd_139169 : Nat := 4983230072969 + 3 ^ 40 * 139169 * 2
def baseEnd_139169 : Nat := 63520523738374430531093

theorem tailTrace_139169 : CollatzResearch.WordTrace tailWord_139169 prefixEnd_139169 63520523738374430531093 := by
  unfold tailWord_139169
  simp only [CollatzResearch.WordTrace]
  refine ⟨5075910432821956018028561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3383940288547970678685707 5075910432821956018028561)
  ·
    refine ⟨3806932824616467013521421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5075910432821956018028561 3806932824616467013521421)
    ·
      refine ⟨1427599809231175130070533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3806932824616467013521421 1427599809231175130070533)
      ·
        refine ⟨267674964230845336888225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1427599809231175130070533 267674964230845336888225)
        ·
          refine ⟨200756223173134002666169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267674964230845336888225 200756223173134002666169)
          ·
            refine ⟨150567167379850501999627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200756223173134002666169 150567167379850501999627)
            ·
              refine ⟨225850751069775752999441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150567167379850501999627 225850751069775752999441)
              ·
                refine ⟨169388063302331814749581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225850751069775752999441 169388063302331814749581)
                ·
                  refine ⟨63520523738374430531093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169388063302331814749581 63520523738374430531093)
                  ·
                    rfl

theorem cell20_139169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_139169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139169 prefixEnd_139169 := by exact prefixLift 139169
  have htrace : WordTrace (prefixWord ++ tailWord_139169) baseStart_139169 baseEnd_139169 := by
    simpa [prefixWord, tailWord_139169, baseEnd_139169] using wordTrace_append hprefix tailTrace_139169
  have hstable : (prefixWord ++ tailWord_139169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139169).length < 2 ^ (prefixWord ++ tailWord_139169).sum := by decide
  have hdescent : baseEnd_139169 < baseStart_139169 := by decide
  rcases family_descends (prefixWord ++ tailWord_139169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139235 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 4]
def baseStart_139235 : Nat := 118140960795 + 139235 * 2 ^ 59
def prefixEnd_139235 : Nat := 4983230072969 + 3 ^ 40 * 139235 * 2
def baseEnd_139235 : Nat := 63550647936771534330823

theorem tailTrace_139235 : CollatzResearch.WordTrace tailWord_139235 prefixEnd_139235 63550647936771534330823 := by
  unfold tailWord_139235
  simp only [CollatzResearch.WordTrace]
  refine ⟨5078317650582849289931159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3385545100388566193287439 5078317650582849289931159)
  ·
    refine ⟨7617476475874273934896739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5078317650582849289931159 7617476475874273934896739)
    ·
      refine ⟨11426214713811410902345109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7617476475874273934896739 11426214713811410902345109)
      ·
        refine ⟨535603814709909886047427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11426214713811410902345109 535603814709909886047427)
        ·
          refine ⟨803405722064864829071141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535603814709909886047427 803405722064864829071141)
          ·
            refine ⟨150638572887162155450839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 803405722064864829071141 150638572887162155450839)
            ·
              refine ⟨225957859330743233176259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150638572887162155450839 225957859330743233176259)
              ·
                refine ⟨338936788996114849764389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225957859330743233176259 338936788996114849764389)
                ·
                  refine ⟨63550647936771534330823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338936788996114849764389 63550647936771534330823)
                  ·
                    rfl

theorem cell20_139235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 4].length) (baseStart_139235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139235 prefixEnd_139235 := by exact prefixLift 139235
  have htrace : WordTrace (prefixWord ++ tailWord_139235) baseStart_139235 baseEnd_139235 := by
    simpa [prefixWord, tailWord_139235, baseEnd_139235] using wordTrace_append hprefix tailTrace_139235
  have hstable : (prefixWord ++ tailWord_139235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139235).length < 2 ^ (prefixWord ++ tailWord_139235).sum := by decide
  have hdescent : baseEnd_139235 < baseStart_139235 := by decide
  rcases family_descends (prefixWord ++ tailWord_139235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139245 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 3]
def baseStart_139245 : Nat := 118140960795 + 139245 * 2 ^ 59
def prefixEnd_139245 : Nat := 4983230072969 + 3 ^ 40 * 139245 * 2
def baseEnd_139245 : Nat := 63555212209255943997449

theorem tailTrace_139245 : CollatzResearch.WordTrace tailWord_139245 prefixEnd_139245 63555212209255943997449 := by
  unfold tailWord_139245
  simp only [CollatzResearch.WordTrace]
  refine ⟨5078682380546620997795189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3385788253697747331863459 5078682380546620997795189)
  ·
    refine ⟨476126473176245718543299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5078682380546620997795189 476126473176245718543299)
    ·
      refine ⟨714189709764368577814949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476126473176245718543299 714189709764368577814949)
      ·
        refine ⟨133910570580819108340303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 714189709764368577814949 133910570580819108340303)
        ·
          refine ⟨200865855871228662510455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133910570580819108340303 200865855871228662510455)
          ·
            refine ⟨301298783806842993765683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200865855871228662510455 301298783806842993765683)
            ·
              refine ⟨451948175710264490648525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301298783806842993765683 451948175710264490648525)
              ·
                refine ⟨169480565891349183993197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 451948175710264490648525 169480565891349183993197)
                ·
                  refine ⟨63555212209255943997449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169480565891349183993197 63555212209255943997449)
                  ·
                    rfl

theorem cell20_139245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_139245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139245 prefixEnd_139245 := by exact prefixLift 139245
  have htrace : WordTrace (prefixWord ++ tailWord_139245) baseStart_139245 baseEnd_139245 := by
    simpa [prefixWord, tailWord_139245, baseEnd_139245] using wordTrace_append hprefix tailTrace_139245
  have hstable : (prefixWord ++ tailWord_139245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139245).length < 2 ^ (prefixWord ++ tailWord_139245).sum := by decide
  have hdescent : baseEnd_139245 < baseStart_139245 := by decide
  rcases family_descends (prefixWord ++ tailWord_139245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139290 : List Nat := [3, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_139290 : Nat := 118140960795 + 139290 * 2 ^ 59
def prefixEnd_139290 : Nat := 4983230072969 + 3 ^ 40 * 139290 * 2
def baseEnd_139290 : Nat := 63575751435435787497265

theorem tailTrace_139290 : CollatzResearch.WordTrace tailWord_139290 prefixEnd_139290 63575751435435787497265 := by
  unfold tailWord_139290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270080916345898420795831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3386882443589062455455549 1270080916345898420795831)
  ·
    refine ⟨1905121374518847631193747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1270080916345898420795831 1905121374518847631193747)
    ·
      refine ⟨2857682061778271446790621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1905121374518847631193747 2857682061778271446790621)
      ·
        refine ⟨1071630773166851792546483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2857682061778271446790621 1071630773166851792546483)
        ·
          refine ⟨1607446159750277688819725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071630773166851792546483 1607446159750277688819725)
          ·
            refine ⟨602792309906354133307397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1607446159750277688819725 602792309906354133307397)
            ·
              refine ⟨113023558107441399995137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 602792309906354133307397 113023558107441399995137)
              ·
                refine ⟨84767668580581049996353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113023558107441399995137 84767668580581049996353)
                ·
                  refine ⟨63575751435435787497265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84767668580581049996353 63575751435435787497265)
                  ·
                    rfl

theorem cell20_139290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_139290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139290 prefixEnd_139290 := by exact prefixLift 139290
  have htrace : WordTrace (prefixWord ++ tailWord_139290) baseStart_139290 baseEnd_139290 := by
    simpa [prefixWord, tailWord_139290, baseEnd_139290] using wordTrace_append hprefix tailTrace_139290
  have hstable : (prefixWord ++ tailWord_139290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139290).length < 2 ^ (prefixWord ++ tailWord_139290).sum := by decide
  have hdescent : baseEnd_139290 < baseStart_139290 := by decide
  rcases family_descends (prefixWord ++ tailWord_139290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139297 : List Nat := [1, 2, 3, 2, 5, 1, 1, 5]
def baseStart_139297 : Nat := 118140960795 + 139297 * 2 ^ 59
def prefixEnd_139297 : Nat := 4983230072969 + 3 ^ 40 * 139297 * 2
def baseEnd_139297 : Nat := 21192982142058291421301

theorem tailTrace_139297 : CollatzResearch.WordTrace tailWord_139297 prefixEnd_139297 21192982142058291421301 := by
  unfold tailWord_139297
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080578976358233878688145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3387052650905489252458763 5080578976358233878688145)
  ·
    refine ⟨3810434232268675409016109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5080578976358233878688145 3810434232268675409016109)
    ·
      refine ⟨1428912837100753278381041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3810434232268675409016109 1428912837100753278381041)
      ·
        refine ⟨1071684627825564958785781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1428912837100753278381041 1071684627825564958785781)
        ·
          refine ⟨100470433858646714886167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1071684627825564958785781 100470433858646714886167)
          ·
            refine ⟨150705650787970072329251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100470433858646714886167 150705650787970072329251)
            ·
              refine ⟨226058476181955108493877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150705650787970072329251 226058476181955108493877)
              ·
                refine ⟨21192982142058291421301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226058476181955108493877 21192982142058291421301)
                ·
                  rfl

theorem cell20_139297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 5].length) (baseStart_139297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139297 prefixEnd_139297 := by exact prefixLift 139297
  have htrace : WordTrace (prefixWord ++ tailWord_139297) baseStart_139297 baseEnd_139297 := by
    simpa [prefixWord, tailWord_139297, baseEnd_139297] using wordTrace_append hprefix tailTrace_139297
  have hstable : (prefixWord ++ tailWord_139297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139297).length < 2 ^ (prefixWord ++ tailWord_139297).sum := by decide
  have hdescent : baseEnd_139297 < baseStart_139297 := by decide
  rcases family_descends (prefixWord ++ tailWord_139297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139301 : List Nat := [1, 3, 1, 2, 2, 3, 3, 5]
def baseStart_139301 : Nat := 118140960795 + 139301 * 2 ^ 59
def prefixEnd_139301 : Nat := 4983230072969 + 3 ^ 40 * 139301 * 2
def baseEnd_139301 : Nat := 21193590711722879376851

theorem tailTrace_139301 : CollatzResearch.WordTrace tailWord_139301 prefixEnd_139301 21193590711722879376851 := by
  unfold tailWord_139301
  simp only [CollatzResearch.WordTrace]
  refine ⟨5080724868343742561833757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3387149912229161707889171 5080724868343742561833757)
  ·
    refine ⟨1905271825628903460687659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5080724868343742561833757 1905271825628903460687659)
    ·
      refine ⟨2857907738443355191031489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1905271825628903460687659 2857907738443355191031489)
      ·
        refine ⟨2143430803832516393273617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2857907738443355191031489 2143430803832516393273617)
        ·
          refine ⟨1607573102874387294955213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2143430803832516393273617 1607573102874387294955213)
          ·
            refine ⟨602839913577895235608205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1607573102874387294955213 602839913577895235608205)
            ·
              refine ⟨226064967591710713353077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 602839913577895235608205 226064967591710713353077)
              ·
                refine ⟨21193590711722879376851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226064967591710713353077 21193590711722879376851)
                ·
                  rfl

theorem cell20_139301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_139301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139301 prefixEnd_139301 := by exact prefixLift 139301
  have htrace : WordTrace (prefixWord ++ tailWord_139301) baseStart_139301 baseEnd_139301 := by
    simpa [prefixWord, tailWord_139301, baseEnd_139301] using wordTrace_append hprefix tailTrace_139301
  have hstable : (prefixWord ++ tailWord_139301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139301).length < 2 ^ (prefixWord ++ tailWord_139301).sum := by decide
  have hdescent : baseEnd_139301 < baseStart_139301 := by decide
  rcases family_descends (prefixWord ++ tailWord_139301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139315 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 6]
def baseStart_139315 : Nat := 118140960795 + 139315 * 2 ^ 59
def prefixEnd_139315 : Nat := 4983230072969 + 3 ^ 40 * 139315 * 2
def baseEnd_139315 : Nat := 63587162116646811663829

theorem tailTrace_139315 : CollatzResearch.WordTrace tailWord_139315 prefixEnd_139315 63587162116646811663829 := by
  unfold tailWord_139315
  simp only [CollatzResearch.WordTrace]
  refine ⟨5081235490293022952843399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3387490326862015301895599 5081235490293022952843399)
  ·
    refine ⟨7621853235439534429265099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5081235490293022952843399 7621853235439534429265099)
    ·
      refine ⟨11432779853159301643897649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7621853235439534429265099 11432779853159301643897649)
      ·
        refine ⟨8574584889869476232923237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11432779853159301643897649 8574584889869476232923237)
        ·
          refine ⟨1607734666850526793673107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8574584889869476232923237 1607734666850526793673107)
          ·
            refine ⟨2411602000275790190509661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1607734666850526793673107 2411602000275790190509661)
            ·
              refine ⟨904350750103421321441123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2411602000275790190509661 904350750103421321441123)
              ·
                refine ⟨1356526125155131982161685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904350750103421321441123 1356526125155131982161685)
                ·
                  refine ⟨63587162116646811663829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1356526125155131982161685 63587162116646811663829)
                  ·
                    rfl

theorem cell20_139315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_139315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139315 prefixEnd_139315 := by exact prefixLift 139315
  have htrace : WordTrace (prefixWord ++ tailWord_139315) baseStart_139315 baseEnd_139315 := by
    simpa [prefixWord, tailWord_139315, baseEnd_139315] using wordTrace_append hprefix tailTrace_139315
  have hstable : (prefixWord ++ tailWord_139315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139315).length < 2 ^ (prefixWord ++ tailWord_139315).sum := by decide
  have hdescent : baseEnd_139315 < baseStart_139315 := by decide
  rcases family_descends (prefixWord ++ tailWord_139315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139342 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_139342 : Nat := 118140960795 + 139342 * 2 ^ 59
def prefixEnd_139342 : Nat := 4983230072969 + 3 ^ 40 * 139342 * 2
def baseEnd_139342 : Nat := 63599485652354717763719

theorem tailTrace_139342 : CollatzResearch.WordTrace tailWord_139342 prefixEnd_139342 63599485652354717763719 := by
  unfold tailWord_139342
  simp only [CollatzResearch.WordTrace]
  refine ⟨635277532649400820509535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3388146840796804376050853 635277532649400820509535)
  ·
    refine ⟨952916298974101230764303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 635277532649400820509535 952916298974101230764303)
    ·
      refine ⟨1429374448461151846146455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952916298974101230764303 1429374448461151846146455)
      ·
        refine ⟨2144061672691727769219683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1429374448461151846146455 2144061672691727769219683)
        ·
          refine ⟨3216092509037591653829525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2144061672691727769219683 3216092509037591653829525)
          ·
            refine ⟨150754336361137108773259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3216092509037591653829525 150754336361137108773259)
            ·
              refine ⟨226131504541705663159889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150754336361137108773259 226131504541705663159889)
              ·
                refine ⟨169598628406279247369917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226131504541705663159889 169598628406279247369917)
                ·
                  refine ⟨63599485652354717763719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169598628406279247369917 63599485652354717763719)
                  ·
                    rfl

theorem cell20_139342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_139342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139342 prefixEnd_139342 := by exact prefixLift 139342
  have htrace : WordTrace (prefixWord ++ tailWord_139342) baseStart_139342 baseEnd_139342 := by
    simpa [prefixWord, tailWord_139342, baseEnd_139342] using wordTrace_append hprefix tailTrace_139342
  have hstable : (prefixWord ++ tailWord_139342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139342).length < 2 ^ (prefixWord ++ tailWord_139342).sum := by decide
  have hdescent : baseEnd_139342 < baseStart_139342 := by decide
  rcases family_descends (prefixWord ++ tailWord_139342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139349 : List Nat := [1, 3, 2, 2, 1, 3, 2, 4, 2]
def baseStart_139349 : Nat := 118140960795 + 139349 * 2 ^ 59
def prefixEnd_139349 : Nat := 4983230072969 + 3 ^ 40 * 139349 * 2
def baseEnd_139349 : Nat := 63602680643093804530357

theorem tailTrace_139349 : CollatzResearch.WordTrace tailWord_139349 prefixEnd_139349 63602680643093804530357 := by
  unfold tailWord_139349
  simp only [CollatzResearch.WordTrace]
  refine ⟨5082475572169846759581101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3388317048113231173054067 5082475572169846759581101)
  ·
    refine ⟨1905928339563692534842913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5082475572169846759581101 1905928339563692534842913)
    ·
      refine ⟨1429446254672769401132185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1905928339563692534842913 1429446254672769401132185)
      ·
        refine ⟨1072084691004577050849139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1429446254672769401132185 1072084691004577050849139)
        ·
          refine ⟨1608127036506865576273709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072084691004577050849139 1608127036506865576273709)
          ·
            refine ⟨603047638690074591102641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1608127036506865576273709 603047638690074591102641)
            ·
              refine ⟨452285729017555943326981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603047638690074591102641 452285729017555943326981)
              ·
                refine ⟨84803574190791739373809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 452285729017555943326981 84803574190791739373809)
                ·
                  refine ⟨63602680643093804530357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84803574190791739373809 63602680643093804530357)
                  ·
                    rfl

theorem cell20_139349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_139349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139349 prefixEnd_139349 := by exact prefixLift 139349
  have htrace : WordTrace (prefixWord ++ tailWord_139349) baseStart_139349 baseEnd_139349 := by
    simpa [prefixWord, tailWord_139349, baseEnd_139349] using wordTrace_append hprefix tailTrace_139349
  have hstable : (prefixWord ++ tailWord_139349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139349).length < 2 ^ (prefixWord ++ tailWord_139349).sum := by decide
  have hdescent : baseEnd_139349 < baseStart_139349 := by decide
  rcases family_descends (prefixWord ++ tailWord_139349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139418 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_139418 : Nat := 118140960795 + 139418 * 2 ^ 59
def prefixEnd_139418 : Nat := 4983230072969 + 3 ^ 40 * 139418 * 2
def baseEnd_139418 : Nat := 63634174123236231230075

theorem tailTrace_139418 : CollatzResearch.WordTrace tailWord_139418 prefixEnd_139418 63634174123236231230075 := by
  unfold tailWord_139418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271248052229967885960727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3389994805946581029228605 1271248052229967885960727)
  ·
    refine ⟨1906872078344951828941091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1271248052229967885960727 1906872078344951828941091)
    ·
      refine ⟨2860308117517427743411637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1906872078344951828941091 2860308117517427743411637)
      ·
        refine ⟨268153886017258850944841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2860308117517427743411637 268153886017258850944841)
        ·
          refine ⟨201115414512944138208631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268153886017258850944841 201115414512944138208631)
          ·
            refine ⟨301673121769416207312947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201115414512944138208631 301673121769416207312947)
            ·
              refine ⟨452509682654124310969421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301673121769416207312947 452509682654124310969421)
              ·
                refine ⟨169691130995296616613533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452509682654124310969421 169691130995296616613533)
                ·
                  refine ⟨63634174123236231230075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169691130995296616613533 63634174123236231230075)
                  ·
                    rfl

theorem cell20_139418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_139418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139418 prefixEnd_139418 := by exact prefixLift 139418
  have htrace : WordTrace (prefixWord ++ tailWord_139418) baseStart_139418 baseEnd_139418 := by
    simpa [prefixWord, tailWord_139418, baseEnd_139418] using wordTrace_append hprefix tailTrace_139418
  have hstable : (prefixWord ++ tailWord_139418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139418).length < 2 ^ (prefixWord ++ tailWord_139418).sum := by decide
  have hdescent : baseEnd_139418 < baseStart_139418 := by decide
  rcases family_descends (prefixWord ++ tailWord_139418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139429 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 6]
def baseStart_139429 : Nat := 118140960795 + 139429 * 2 ^ 59
def prefixEnd_139429 : Nat := 4983230072969 + 3 ^ 40 * 139429 * 2
def baseEnd_139429 : Nat := 63639194822969081863363

theorem tailTrace_139429 : CollatzResearch.WordTrace tailWord_139429 prefixEnd_139429 63639194822969081863363 := by
  unfold tailWord_139429
  simp only [CollatzResearch.WordTrace]
  refine ⟨5085393411880020422493341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3390262274586680281662227 5085393411880020422493341)
  ·
    refine ⟨1907022529455007658435003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5085393411880020422493341 1907022529455007658435003)
    ·
      refine ⟨2860533794182511487652505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907022529455007658435003 2860533794182511487652505)
      ·
        refine ⟨2145400345636883615739379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2860533794182511487652505 2145400345636883615739379)
        ·
          refine ⟨3218100518455325423609069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2145400345636883615739379 3218100518455325423609069)
          ·
            refine ⟨1206787694420747033853401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3218100518455325423609069 1206787694420747033853401)
            ·
              refine ⟨905090770815560275390051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206787694420747033853401 905090770815560275390051)
              ·
                refine ⟨1357636156223340413085077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 905090770815560275390051 1357636156223340413085077)
                ·
                  refine ⟨63639194822969081863363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1357636156223340413085077 63639194822969081863363)
                  ·
                    rfl

theorem cell20_139429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_139429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139429 prefixEnd_139429 := by exact prefixLift 139429
  have htrace : WordTrace (prefixWord ++ tailWord_139429) baseStart_139429 baseEnd_139429 := by
    simpa [prefixWord, tailWord_139429, baseEnd_139429] using wordTrace_append hprefix tailTrace_139429
  have hstable : (prefixWord ++ tailWord_139429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139429).length < 2 ^ (prefixWord ++ tailWord_139429).sum := by decide
  have hdescent : baseEnd_139429 < baseStart_139429 := by decide
  rcases family_descends (prefixWord ++ tailWord_139429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139467 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_139467 : Nat := 118140960795 + 139467 * 2 ^ 59
def prefixEnd_139467 : Nat := 4983230072969 + 3 ^ 40 * 139467 * 2
def baseEnd_139467 : Nat := 63656539058409838596541

theorem tailTrace_139467 : CollatzResearch.WordTrace tailWord_139467 prefixEnd_139467 63656539058409838596541 := by
  unfold tailWord_139467
  simp only [CollatzResearch.WordTrace]
  refine ⟨5086779385742352912376655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3391186257161568608251103 5086779385742352912376655)
  ·
    refine ⟨7630169078613529368564983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5086779385742352912376655 7630169078613529368564983)
    ·
      refine ⟨11445253617920294052847475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7630169078613529368564983 11445253617920294052847475)
      ·
        refine ⟨17167880426880441079271213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11445253617920294052847475 17167880426880441079271213)
        ·
          refine ⟨6437955160080165404726705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17167880426880441079271213 6437955160080165404726705)
          ·
            refine ⟨4828466370060124053545029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6437955160080165404726705 4828466370060124053545029)
            ·
              refine ⟨905337444386273260039693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4828466370060124053545029 905337444386273260039693)
              ·
                refine ⟨339501541644852472514885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 905337444386273260039693 339501541644852472514885)
                ·
                  refine ⟨63656539058409838596541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339501541644852472514885 63656539058409838596541)
                  ·
                    rfl

theorem cell20_139467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_139467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139467 prefixEnd_139467 := by exact prefixLift 139467
  have htrace : WordTrace (prefixWord ++ tailWord_139467) baseStart_139467 baseEnd_139467 := by
    simpa [prefixWord, tailWord_139467, baseEnd_139467] using wordTrace_append hprefix tailTrace_139467
  have hstable : (prefixWord ++ tailWord_139467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139467).length < 2 ^ (prefixWord ++ tailWord_139467).sum := by decide
  have hdescent : baseEnd_139467 < baseStart_139467 := by decide
  rcases family_descends (prefixWord ++ tailWord_139467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139470 : List Nat := [4, 1, 1, 1, 4, 3, 1, 5]
def baseStart_139470 : Nat := 118140960795 + 139470 * 2 ^ 59
def prefixEnd_139470 : Nat := 4983230072969 + 3 ^ 40 * 139470 * 2
def baseEnd_139470 : Nat := 21219302780051720498843

theorem tailTrace_139470 : CollatzResearch.WordTrace tailWord_139470 prefixEnd_139470 21219302780051720498843 := by
  unfold tailWord_139470
  simp only [CollatzResearch.WordTrace]
  refine ⟨635861100591435553091983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3391259203154322949823909 635861100591435553091983)
  ·
    refine ⟨953791650887153329637975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 635861100591435553091983 953791650887153329637975)
    ·
      refine ⟨1430687476330729994456963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953791650887153329637975 1430687476330729994456963)
      ·
        refine ⟨2146031214496094991685445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1430687476330729994456963 2146031214496094991685445)
        ·
          refine ⟨402380852718017810941021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2146031214496094991685445 402380852718017810941021)
          ·
            refine ⟨150892819769256679102883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402380852718017810941021 150892819769256679102883)
            ·
              refine ⟨226339229653885018654325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150892819769256679102883 226339229653885018654325)
              ·
                refine ⟨21219302780051720498843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226339229653885018654325 21219302780051720498843)
                ·
                  rfl

theorem cell20_139470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_139470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139470 prefixEnd_139470 := by exact prefixLift 139470
  have htrace : WordTrace (prefixWord ++ tailWord_139470) baseStart_139470 baseEnd_139470 := by
    simpa [prefixWord, tailWord_139470, baseEnd_139470] using wordTrace_append hprefix tailTrace_139470
  have hstable : (prefixWord ++ tailWord_139470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139470).length < 2 ^ (prefixWord ++ tailWord_139470).sum := by decide
  have hdescent : baseEnd_139470 < baseStart_139470 := by decide
  rcases family_descends (prefixWord ++ tailWord_139470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139498 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_139498 : Nat := 118140960795 + 139498 * 2 ^ 59
def prefixEnd_139498 : Nat := 4983230072969 + 3 ^ 40 * 139498 * 2
def baseEnd_139498 : Nat := 63670688303111508563081

theorem tailTrace_139498 : CollatzResearch.WordTrace tailWord_139498 prefixEnd_139498 63670688303111508563081 := by
  unfold tailWord_139498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271977512157511301688787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3391940032420030137836765 1271977512157511301688787)
  ·
    refine ⟨1907966268236266952533181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1271977512157511301688787 1907966268236266952533181)
    ·
      refine ⟨715487350588600107199943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1907966268236266952533181 715487350588600107199943)
      ·
        refine ⟨1073231025882900160799915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715487350588600107199943 1073231025882900160799915)
        ·
          refine ⟨1609846538824350241199873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073231025882900160799915 1609846538824350241199873)
          ·
            refine ⟨1207384904118262680899905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1609846538824350241199873 1207384904118262680899905)
            ·
              refine ⟨905538678088697010674929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207384904118262680899905 905538678088697010674929)
              ·
                refine ⟨679154008566522758006197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905538678088697010674929 679154008566522758006197)
                ·
                  refine ⟨63670688303111508563081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 679154008566522758006197 63670688303111508563081)
                  ·
                    rfl

theorem cell20_139498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_139498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139498 prefixEnd_139498 := by exact prefixLift 139498
  have htrace : WordTrace (prefixWord ++ tailWord_139498) baseStart_139498 baseEnd_139498 := by
    simpa [prefixWord, tailWord_139498, baseEnd_139498] using wordTrace_append hprefix tailTrace_139498
  have hstable : (prefixWord ++ tailWord_139498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139498).length < 2 ^ (prefixWord ++ tailWord_139498).sum := by decide
  have hdescent : baseEnd_139498 < baseStart_139498 := by decide
  rcases family_descends (prefixWord ++ tailWord_139498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139556 : List Nat := [2, 3, 1, 3, 1, 4, 1, 3, 2]
def baseStart_139556 : Nat := 118140960795 + 139556 * 2 ^ 59
def prefixEnd_139556 : Nat := 4983230072969 + 3 ^ 40 * 139556 * 2
def baseEnd_139556 : Nat := 63697161083521084629511

theorem tailTrace_139556 : CollatzResearch.WordTrace tailWord_139556 prefixEnd_139556 63697161083521084629511 := by
  unfold tailWord_139556
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545012741209960556183261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3393350321613280741577681 2545012741209960556183261)
  ·
    refine ⟨954379777953735208568723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2545012741209960556183261 954379777953735208568723)
    ·
      refine ⟨1431569666930602812853085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 954379777953735208568723 1431569666930602812853085)
      ·
        refine ⟨536838625098976054819907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1431569666930602812853085 536838625098976054819907)
        ·
          refine ⟨805257937648464082229861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536838625098976054819907 805257937648464082229861)
          ·
            refine ⟨150985863309087015418099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 805257937648464082229861 150985863309087015418099)
            ·
              refine ⟨226478794963630523127149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150985863309087015418099 226478794963630523127149)
              ·
                refine ⟨84929548111361446172681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226478794963630523127149 84929548111361446172681)
                ·
                  refine ⟨63697161083521084629511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84929548111361446172681 63697161083521084629511)
                  ·
                    rfl

theorem cell20_139556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_139556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139556 prefixEnd_139556 := by exact prefixLift 139556
  have htrace : WordTrace (prefixWord ++ tailWord_139556) baseStart_139556 baseEnd_139556 := by
    simpa [prefixWord, tailWord_139556, baseEnd_139556] using wordTrace_append hprefix tailTrace_139556
  have hstable : (prefixWord ++ tailWord_139556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139556).length < 2 ^ (prefixWord ++ tailWord_139556).sum := by decide
  have hdescent : baseEnd_139556 < baseStart_139556 := by decide
  rcases family_descends (prefixWord ++ tailWord_139556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139577 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 4]
def baseStart_139577 : Nat := 118140960795 + 139577 * 2 ^ 59
def prefixEnd_139577 : Nat := 4983230072969 + 3 ^ 40 * 139577 * 2
def baseEnd_139577 : Nat := 63706746055738344929425

theorem tailTrace_139577 : CollatzResearch.WordTrace tailWord_139577 prefixEnd_139577 63706746055738344929425 := by
  unfold tailWord_139577
  simp only [CollatzResearch.WordTrace]
  refine ⟨5090791415343841698880985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3393860943562561132587323 5090791415343841698880985)
  ·
    refine ⟨3818093561507881274160739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5090791415343841698880985 3818093561507881274160739)
    ·
      refine ⟨5727140342261821911241109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3818093561507881274160739 5727140342261821911241109)
      ·
        refine ⟨268459703543522902089427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5727140342261821911241109 268459703543522902089427)
        ·
          refine ⟨402689555315284353134141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268459703543522902089427 402689555315284353134141)
          ·
            refine ⟨151008583243231632425303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402689555315284353134141 151008583243231632425303)
            ·
              refine ⟨226512874864847448637955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151008583243231632425303 226512874864847448637955)
              ·
                refine ⟨339769312297271172956933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226512874864847448637955 339769312297271172956933)
                ·
                  refine ⟨63706746055738344929425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339769312297271172956933 63706746055738344929425)
                  ·
                    rfl

theorem cell20_139577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_139577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139577 prefixEnd_139577 := by exact prefixLift 139577
  have htrace : WordTrace (prefixWord ++ tailWord_139577) baseStart_139577 baseEnd_139577 := by
    simpa [prefixWord, tailWord_139577, baseEnd_139577] using wordTrace_append hprefix tailTrace_139577
  have hstable : (prefixWord ++ tailWord_139577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139577).length < 2 ^ (prefixWord ++ tailWord_139577).sum := by decide
  have hdescent : baseEnd_139577 < baseStart_139577 := by decide
  rcases family_descends (prefixWord ++ tailWord_139577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139595 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_139595 : Nat := 118140960795 + 139595 * 2 ^ 59
def prefixEnd_139595 : Nat := 4983230072969 + 3 ^ 40 * 139595 * 2
def baseEnd_139595 : Nat := 63714961746210282329351

theorem tailTrace_139595 : CollatzResearch.WordTrace tailWord_139595 prefixEnd_139595 63714961746210282329351 := by
  unfold tailWord_139595
  simp only [CollatzResearch.WordTrace]
  refine ⟨5091447929278630773036239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3394298619519087182024159 5091447929278630773036239)
  ·
    refine ⟨7637171893917946159554359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5091447929278630773036239 7637171893917946159554359)
    ·
      refine ⟨11455757840876919239331539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7637171893917946159554359 11455757840876919239331539)
      ·
        refine ⟨17183636761315378858997309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11455757840876919239331539 17183636761315378858997309)
        ·
          refine ⟨6443863785493267072123991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17183636761315378858997309 6443863785493267072123991)
          ·
            refine ⟨9665795678239900608185987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6443863785493267072123991 9665795678239900608185987)
            ·
              refine ⟨14498693517359850912278981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9665795678239900608185987 14498693517359850912278981)
              ·
                refine ⟨2718505034504972046052309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14498693517359850912278981 2718505034504972046052309)
                ·
                  refine ⟨63714961746210282329351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2718505034504972046052309 63714961746210282329351)
                  ·
                    rfl

theorem cell20_139595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_139595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139595 prefixEnd_139595 := by exact prefixLift 139595
  have htrace : WordTrace (prefixWord ++ tailWord_139595) baseStart_139595 baseEnd_139595 := by
    simpa [prefixWord, tailWord_139595, baseEnd_139595] using wordTrace_append hprefix tailTrace_139595
  have hstable : (prefixWord ++ tailWord_139595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139595).length < 2 ^ (prefixWord ++ tailWord_139595).sum := by decide
  have hdescent : baseEnd_139595 < baseStart_139595 := by decide
  rcases family_descends (prefixWord ++ tailWord_139595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139629 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 3]
def baseStart_139629 : Nat := 118140960795 + 139629 * 2 ^ 59
def prefixEnd_139629 : Nat := 4983230072969 + 3 ^ 40 * 139629 * 2
def baseEnd_139629 : Nat := 63730480272657275195879

theorem tailTrace_139629 : CollatzResearch.WordTrace tailWord_139629 prefixEnd_139629 63730480272657275195879 := by
  unfold tailWord_139629
  simp only [CollatzResearch.WordTrace]
  refine ⟨5092688011155454579773941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3395125340770303053182627 5092688011155454579773941)
  ·
    refine ⟨477439501045823866853807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5092688011155454579773941 477439501045823866853807)
    ·
      refine ⟨716159251568735800280711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477439501045823866853807 716159251568735800280711)
      ·
        refine ⟨1074238877353103700421067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 716159251568735800280711 1074238877353103700421067)
        ·
          refine ⟨1611358316029655550631601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1074238877353103700421067 1611358316029655550631601)
          ·
            refine ⟨1208518737022241662973701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1611358316029655550631601 1208518737022241662973701)
            ·
              refine ⟨226597263191670311807569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1208518737022241662973701 226597263191670311807569)
              ·
                refine ⟨169947947393752733855677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226597263191670311807569 169947947393752733855677)
                ·
                  refine ⟨63730480272657275195879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169947947393752733855677 63730480272657275195879)
                  ·
                    rfl

theorem cell20_139629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_139629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139629 prefixEnd_139629 := by exact prefixLift 139629
  have htrace : WordTrace (prefixWord ++ tailWord_139629) baseStart_139629 baseEnd_139629 := by
    simpa [prefixWord, tailWord_139629, baseEnd_139629] using wordTrace_append hprefix tailTrace_139629
  have hstable : (prefixWord ++ tailWord_139629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139629).length < 2 ^ (prefixWord ++ tailWord_139629).sum := by decide
  have hdescent : baseEnd_139629 < baseStart_139629 := by decide
  rcases family_descends (prefixWord ++ tailWord_139629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139632 : List Nat := [2, 1, 1, 1, 4, 5, 2, 2, 2]
def baseStart_139632 : Nat := 118140960795 + 139632 * 2 ^ 59
def prefixEnd_139632 : Nat := 4983230072969 + 3 ^ 40 * 139632 * 2
def baseEnd_139632 : Nat := 63731849554402598095867

theorem tailTrace_139632 : CollatzResearch.WordTrace tailWord_139632 prefixEnd_139632 63731849554402598095867 := by
  unfold tailWord_139632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546398715072293046066575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3395198286763057394755433 2546398715072293046066575)
  ·
    refine ⟨3819598072608439569099863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2546398715072293046066575 3819598072608439569099863)
    ·
      refine ⟨5729397108912659353649795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3819598072608439569099863 5729397108912659353649795)
      ·
        refine ⟨8594095663368989030474693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5729397108912659353649795 8594095663368989030474693)
        ·
          refine ⟨1611392936881685443214005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8594095663368989030474693 1611392936881685443214005)
          ·
            refine ⟨151068087832658010301313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1611392936881685443214005 151068087832658010301313)
            ·
              refine ⟨113301065874493507725985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151068087832658010301313 113301065874493507725985)
              ·
                refine ⟨84975799405870130794489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113301065874493507725985 84975799405870130794489)
                ·
                  refine ⟨63731849554402598095867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84975799405870130794489 63731849554402598095867)
                  ·
                    rfl

theorem cell20_139632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_139632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139632 prefixEnd_139632 := by exact prefixLift 139632
  have htrace : WordTrace (prefixWord ++ tailWord_139632) baseStart_139632 baseEnd_139632 := by
    simpa [prefixWord, tailWord_139632, baseEnd_139632] using wordTrace_append hprefix tailTrace_139632
  have hstable : (prefixWord ++ tailWord_139632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139632).length < 2 ^ (prefixWord ++ tailWord_139632).sum := by decide
  have hdescent : baseEnd_139632 < baseStart_139632 := by decide
  rcases family_descends (prefixWord ++ tailWord_139632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139643 : List Nat := [1, 1, 1, 1, 1, 9, 1, 5]
def baseStart_139643 : Nat := 118140960795 + 139643 * 2 ^ 59
def prefixEnd_139643 : Nat := 4983230072969 + 3 ^ 40 * 139643 * 2
def baseEnd_139643 : Nat := 21245623418045149576385

theorem tailTrace_139643 : CollatzResearch.WordTrace tailWord_139643 prefixEnd_139643 21245623418045149576385 := by
  unfold tailWord_139643
  simp only [CollatzResearch.WordTrace]
  refine ⟨5093198633104734970783583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3395465755403156647189055 5093198633104734970783583)
  ·
    refine ⟨7639797949657102456175375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5093198633104734970783583 7639797949657102456175375)
    ·
      refine ⟨11459696924485653684263063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7639797949657102456175375 11459696924485653684263063)
      ·
        refine ⟨17189545386728480526394595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11459696924485653684263063 17189545386728480526394595)
        ·
          refine ⟨25784318080092720789591893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17189545386728480526394595 25784318080092720789591893)
          ·
            refine ⟨151079988750543285876515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 25784318080092720789591893 151079988750543285876515)
            ·
              refine ⟨226619983125814928814773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151079988750543285876515 226619983125814928814773)
              ·
                refine ⟨21245623418045149576385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226619983125814928814773 21245623418045149576385)
                ·
                  rfl

theorem cell20_139643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 5].length) (baseStart_139643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139643 prefixEnd_139643 := by exact prefixLift 139643
  have htrace : WordTrace (prefixWord ++ tailWord_139643) baseStart_139643 baseEnd_139643 := by
    simpa [prefixWord, tailWord_139643, baseEnd_139643] using wordTrace_append hprefix tailTrace_139643
  have hstable : (prefixWord ++ tailWord_139643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139643).length < 2 ^ (prefixWord ++ tailWord_139643).sum := by decide
  have hdescent : baseEnd_139643 < baseStart_139643 := by decide
  rcases family_descends (prefixWord ++ tailWord_139643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139657 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 6]
def baseStart_139657 : Nat := 118140960795 + 139657 * 2 ^ 59
def prefixEnd_139657 : Nat := 4983230072969 + 3 ^ 40 * 139657 * 2
def baseEnd_139657 : Nat := 63743260235613622262431

theorem tailTrace_139657 : CollatzResearch.WordTrace tailWord_139657 prefixEnd_139657 63743260235613622262431 := by
  unfold tailWord_139657
  simp only [CollatzResearch.WordTrace]
  refine ⟨5093709255054015361793225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3395806170036010241195483 5093709255054015361793225)
  ·
    refine ⟨3820281941290511521344919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5093709255054015361793225 3820281941290511521344919)
    ·
      refine ⟨5730422911935767282017379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3820281941290511521344919 5730422911935767282017379)
      ·
        refine ⟨8595634367903650923026069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5730422911935767282017379 8595634367903650923026069)
        ·
          refine ⟨402920360995483637016847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8595634367903650923026069 402920360995483637016847)
          ·
            refine ⟨604380541493225455525271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402920360995483637016847 604380541493225455525271)
            ·
              refine ⟨906570812239838183287907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604380541493225455525271 906570812239838183287907)
              ·
                refine ⟨1359856218359757274931861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 906570812239838183287907 1359856218359757274931861)
                ·
                  refine ⟨63743260235613622262431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1359856218359757274931861 63743260235613622262431)
                  ·
                    rfl

theorem cell20_139657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_139657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139657 prefixEnd_139657 := by exact prefixLift 139657
  have htrace : WordTrace (prefixWord ++ tailWord_139657) baseStart_139657 baseEnd_139657 := by
    simpa [prefixWord, tailWord_139657, baseEnd_139657] using wordTrace_append hprefix tailTrace_139657
  have hstable : (prefixWord ++ tailWord_139657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139657).length < 2 ^ (prefixWord ++ tailWord_139657).sum := by decide
  have hdescent : baseEnd_139657 < baseStart_139657 := by decide
  rcases family_descends (prefixWord ++ tailWord_139657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139719 : List Nat := [1, 1, 4, 1, 1, 4, 4, 4]
def baseStart_139719 : Nat := 118140960795 + 139719 * 2 ^ 59
def prefixEnd_139719 : Nat := 4983230072969 + 3 ^ 40 * 139719 * 2
def baseEnd_139719 : Nat := 21257186241672320731837

theorem tailTrace_139719 : CollatzResearch.WordTrace tailWord_139719 prefixEnd_139719 21257186241672320731837 := by
  unfold tailWord_139719
  simp only [CollatzResearch.WordTrace]
  refine ⟨5095970580829399950550211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3397313720552933300366807 5095970580829399950550211)
  ·
    refine ⟨7643955871244099925825317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5095970580829399950550211 7643955871244099925825317)
    ·
      refine ⟨1433241725858268736092247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7643955871244099925825317 1433241725858268736092247)
      ·
        refine ⟨2149862588787403104138371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433241725858268736092247 2149862588787403104138371)
        ·
          refine ⟨3224793883181104656207557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149862588787403104138371 3224793883181104656207557)
          ·
            refine ⟨604648853096457123038917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3224793883181104656207557 604648853096457123038917)
            ·
              refine ⟨113371659955585710569797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 604648853096457123038917 113371659955585710569797)
              ·
                refine ⟨21257186241672320731837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113371659955585710569797 21257186241672320731837)
                ·
                  rfl

theorem cell20_139719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 4].length) (baseStart_139719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139719 prefixEnd_139719 := by exact prefixLift 139719
  have htrace : WordTrace (prefixWord ++ tailWord_139719) baseStart_139719 baseEnd_139719 := by
    simpa [prefixWord, tailWord_139719, baseEnd_139719] using wordTrace_append hprefix tailTrace_139719
  have hstable : (prefixWord ++ tailWord_139719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139719).length < 2 ^ (prefixWord ++ tailWord_139719).sum := by decide
  have hdescent : baseEnd_139719 < baseStart_139719 := by decide
  rcases family_descends (prefixWord ++ tailWord_139719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139757 : List Nat := [1, 5, 1, 3, 1, 1, 1, 7]
def baseStart_139757 : Nat := 118140960795 + 139757 * 2 ^ 59
def prefixEnd_139757 : Nat := 4983230072969 + 3 ^ 40 * 139757 * 2
def baseEnd_139757 : Nat := 21262967653485906309563

theorem tailTrace_139757 : CollatzResearch.WordTrace tailWord_139757 prefixEnd_139757 21262967653485906309563 := by
  unfold tailWord_139757
  simp only [CollatzResearch.WordTrace]
  refine ⟨5097356554691732440433525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3398237703127821626955683 5097356554691732440433525)
  ·
    refine ⟨477877177002349916290643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5097356554691732440433525 477877177002349916290643)
    ·
      refine ⟨716815765503524874435965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477877177002349916290643 716815765503524874435965)
      ·
        refine ⟨268805912063821827913487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 716815765503524874435965 268805912063821827913487)
        ·
          refine ⟨403208868095732741870231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268805912063821827913487 403208868095732741870231)
          ·
            refine ⟨604813302143599112805347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403208868095732741870231 604813302143599112805347)
            ·
              refine ⟨907219953215398669208021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604813302143599112805347 907219953215398669208021)
              ·
                refine ⟨21262967653485906309563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 907219953215398669208021 21262967653485906309563)
                ·
                  rfl

theorem cell20_139757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_139757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139757 prefixEnd_139757 := by exact prefixLift 139757
  have htrace : WordTrace (prefixWord ++ tailWord_139757) baseStart_139757 baseEnd_139757 := by
    simpa [prefixWord, tailWord_139757, baseEnd_139757] using wordTrace_append hprefix tailTrace_139757
  have hstable : (prefixWord ++ tailWord_139757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139757).length < 2 ^ (prefixWord ++ tailWord_139757).sum := by decide
  have hdescent : baseEnd_139757 < baseStart_139757 := by decide
  rcases family_descends (prefixWord ++ tailWord_139757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139785 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_139785 : Nat := 118140960795 + 139785 * 2 ^ 59
def prefixEnd_139785 : Nat := 4983230072969 + 3 ^ 40 * 139785 * 2
def baseEnd_139785 : Nat := 63801682923414065995241

theorem tailTrace_139785 : CollatzResearch.WordTrace tailWord_139785 prefixEnd_139785 63801682923414065995241 := by
  unfold tailWord_139785
  simp only [CollatzResearch.WordTrace]
  refine ⟨5098377798590293222452809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3398918532393528814968539 5098377798590293222452809)
  ·
    refine ⟨3823783348942719916839607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5098377798590293222452809 3823783348942719916839607)
    ·
      refine ⟨5735675023414079875259411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3823783348942719916839607 5735675023414079875259411)
      ·
        refine ⟨8603512535121119812889117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5735675023414079875259411 8603512535121119812889117)
        ·
          refine ⟨3226317200670419929833419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8603512535121119812889117 3226317200670419929833419)
          ·
            refine ⟨4839475801005629894750129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3226317200670419929833419 4839475801005629894750129)
            ·
              refine ⟨3629606850754222421062597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4839475801005629894750129 3629606850754222421062597)
              ·
                refine ⟨680551284516416703949237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3629606850754222421062597 680551284516416703949237)
                ·
                  refine ⟨63801682923414065995241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 680551284516416703949237 63801682923414065995241)
                  ·
                    rfl

theorem cell20_139785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_139785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139785 prefixEnd_139785 := by exact prefixLift 139785
  have htrace : WordTrace (prefixWord ++ tailWord_139785) baseStart_139785 baseEnd_139785 := by
    simpa [prefixWord, tailWord_139785, baseEnd_139785] using wordTrace_append hprefix tailTrace_139785
  have hstable : (prefixWord ++ tailWord_139785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139785).length < 2 ^ (prefixWord ++ tailWord_139785).sum := by decide
  have hdescent : baseEnd_139785 < baseStart_139785 := by decide
  rcases family_descends (prefixWord ++ tailWord_139785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139802 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_139802 : Nat := 118140960795 + 139802 * 2 ^ 59
def prefixEnd_139802 : Nat := 4983230072969 + 3 ^ 40 * 139802 * 2
def baseEnd_139802 : Nat := 63809442186637562428505

theorem tailTrace_139802 : CollatzResearch.WordTrace tailWord_139802 prefixEnd_139802 63809442186637562428505 := by
  unfold tailWord_139802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1274749459882176281455415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3399331893019136750547773 1274749459882176281455415)
  ·
    refine ⟨1912124189823264422183123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1274749459882176281455415 1912124189823264422183123)
    ·
      refine ⟨2868186284734896633274685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1912124189823264422183123 2868186284734896633274685)
      ·
        refine ⟨1075569856775586237478007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2868186284734896633274685 1075569856775586237478007)
        ·
          refine ⟨1613354785163379356217011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075569856775586237478007 1613354785163379356217011)
          ·
            refine ⟨2420032177745069034325517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613354785163379356217011 2420032177745069034325517)
            ·
              refine ⟨907512066654400887872069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2420032177745069034325517 907512066654400887872069)
              ·
                refine ⟨170158512497700166476013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 907512066654400887872069 170158512497700166476013)
                ·
                  refine ⟨63809442186637562428505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170158512497700166476013 63809442186637562428505)
                  ·
                    rfl

theorem cell20_139802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_139802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139802 prefixEnd_139802 := by exact prefixLift 139802
  have htrace : WordTrace (prefixWord ++ tailWord_139802) baseStart_139802 baseEnd_139802 := by
    simpa [prefixWord, tailWord_139802, baseEnd_139802] using wordTrace_append hprefix tailTrace_139802
  have hstable : (prefixWord ++ tailWord_139802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139802).length < 2 ^ (prefixWord ++ tailWord_139802).sum := by decide
  have hdescent : baseEnd_139802 < baseStart_139802 := by decide
  rcases family_descends (prefixWord ++ tailWord_139802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139805 : List Nat := [1, 4, 2, 2, 1, 3, 1, 4, 2]
def baseStart_139805 : Nat := 118140960795 + 139805 * 2 ^ 59
def prefixEnd_139805 : Nat := 4983230072969 + 3 ^ 40 * 139805 * 2
def baseEnd_139805 : Nat := 63810811468382885328493

theorem tailTrace_139805 : CollatzResearch.WordTrace tailWord_139805 prefixEnd_139805 63810811468382885328493 := by
  unfold tailWord_139805
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099107258517836638180869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3399404839011891092120579 5099107258517836638180869)
  ·
    refine ⟨956082610972094369658913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5099107258517836638180869 956082610972094369658913)
    ·
      refine ⟨717061958229070777244185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 956082610972094369658913 717061958229070777244185)
      ·
        refine ⟨537796468671803082933139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 717061958229070777244185 537796468671803082933139)
        ·
          refine ⟨806694703007704624399709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537796468671803082933139 806694703007704624399709)
          ·
            refine ⟨302510513627889234149891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 806694703007704624399709 302510513627889234149891)
            ·
              refine ⟨453765770441833851224837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302510513627889234149891 453765770441833851224837)
              ·
                refine ⟨85081081957843847104657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453765770441833851224837 85081081957843847104657)
                ·
                  refine ⟨63810811468382885328493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85081081957843847104657 63810811468382885328493)
                  ·
                    rfl

theorem cell20_139805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_139805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139805 prefixEnd_139805 := by exact prefixLift 139805
  have htrace : WordTrace (prefixWord ++ tailWord_139805) baseStart_139805 baseEnd_139805 := by
    simpa [prefixWord, tailWord_139805, baseEnd_139805] using wordTrace_append hprefix tailTrace_139805
  have hstable : (prefixWord ++ tailWord_139805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139805).length < 2 ^ (prefixWord ++ tailWord_139805).sum := by decide
  have hdescent : baseEnd_139805 < baseStart_139805 := by decide
  rcases family_descends (prefixWord ++ tailWord_139805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139809 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_139809 : Nat := 118140960795 + 139809 * 2 ^ 59
def prefixEnd_139809 : Nat := 4983230072969 + 3 ^ 40 * 139809 * 2
def baseEnd_139809 : Nat := 63812637177376649195143

theorem tailTrace_139809 : CollatzResearch.WordTrace tailWord_139809 prefixEnd_139809 63812637177376649195143 := by
  unfold tailWord_139809
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099253150503345321326481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3399502100335563547550987 5099253150503345321326481)
  ·
    refine ⟨3824439862877508990994861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5099253150503345321326481 3824439862877508990994861)
    ·
      refine ⟨1434164948579065871623073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3824439862877508990994861 1434164948579065871623073)
      ·
        refine ⟨1075623711434299403717305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1434164948579065871623073 1075623711434299403717305)
        ·
          refine ⟨806717783575724552787979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1075623711434299403717305 806717783575724552787979)
          ·
            refine ⟨1210076675363586829181969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806717783575724552787979 1210076675363586829181969)
            ·
              refine ⟨907557506522690121886477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1210076675363586829181969 907557506522690121886477)
              ·
                refine ⟨340334064946008795707429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 907557506522690121886477 340334064946008795707429)
                ·
                  refine ⟨63812637177376649195143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 340334064946008795707429 63812637177376649195143)
                  ·
                    rfl

theorem cell20_139809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_139809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139809 prefixEnd_139809 := by exact prefixLift 139809
  have htrace : WordTrace (prefixWord ++ tailWord_139809) baseStart_139809 baseEnd_139809 := by
    simpa [prefixWord, tailWord_139809, baseEnd_139809] using wordTrace_append hprefix tailTrace_139809
  have hstable : (prefixWord ++ tailWord_139809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139809).length < 2 ^ (prefixWord ++ tailWord_139809).sum := by decide
  have hdescent : baseEnd_139809 < baseStart_139809 := by decide
  rcases family_descends (prefixWord ++ tailWord_139809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139833 : List Nat := [1, 2, 1, 5, 1, 1, 5, 4]
def baseStart_139833 : Nat := 118140960795 + 139833 * 2 ^ 59
def prefixEnd_139833 : Nat := 4983230072969 + 3 ^ 40 * 139833 * 2
def baseEnd_139833 : Nat := 21274530477113077465015

theorem tailTrace_139833 : CollatzResearch.WordTrace tailWord_139833 prefixEnd_139833 21274530477113077465015 := by
  unfold tailWord_139833
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100128502416397420200153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3400085668277598280133435 5100128502416397420200153)
  ·
    refine ⟨3825096376812298065150115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5100128502416397420200153 3825096376812298065150115)
    ·
      refine ⟨5737644565218447097725173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3825096376812298065150115 5737644565218447097725173)
      ·
        refine ⟨537904177989229415411735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5737644565218447097725173 537904177989229415411735)
        ·
          refine ⟨806856266983844123117603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537904177989229415411735 806856266983844123117603)
          ·
            refine ⟨1210284400475766184676405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806856266983844123117603 1210284400475766184676405)
            ·
              refine ⟨113464162544603079813413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1210284400475766184676405 113464162544603079813413)
              ·
                refine ⟨21274530477113077465015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113464162544603079813413 21274530477113077465015)
                ·
                  rfl

theorem cell20_139833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 4].length) (baseStart_139833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139833 prefixEnd_139833 := by exact prefixLift 139833
  have htrace : WordTrace (prefixWord ++ tailWord_139833) baseStart_139833 baseEnd_139833 := by
    simpa [prefixWord, tailWord_139833, baseEnd_139833] using wordTrace_append hprefix tailTrace_139833
  have hstable : (prefixWord ++ tailWord_139833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139833).length < 2 ^ (prefixWord ++ tailWord_139833).sum := by decide
  have hdescent : baseEnd_139833 < baseStart_139833 := by decide
  rcases family_descends (prefixWord ++ tailWord_139833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139857 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 3]
def baseStart_139857 : Nat := 118140960795 + 139857 * 2 ^ 59
def prefixEnd_139857 : Nat := 4983230072969 + 3 ^ 40 * 139857 * 2
def baseEnd_139857 : Nat := 63834545685301815594947

theorem tailTrace_139857 : CollatzResearch.WordTrace tailWord_139857 prefixEnd_139857 63834545685301815594947 := by
  unfold tailWord_139857
  simp only [CollatzResearch.WordTrace]
  refine ⟨5101003854329449519073825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3400669236219633012715883 5101003854329449519073825)
  ·
    refine ⟨3825752890747087139305369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5101003854329449519073825 3825752890747087139305369)
    ·
      refine ⟨2869314668060315354479027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3825752890747087139305369 2869314668060315354479027)
      ·
        refine ⟨4303972002090473031718541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869314668060315354479027 4303972002090473031718541)
        ·
          refine ⟨1613989500783927386894453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4303972002090473031718541 1613989500783927386894453)
          ·
            refine ⟨151311515698493192521355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1613989500783927386894453 151311515698493192521355)
            ·
              refine ⟨226967273547739788782033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151311515698493192521355 226967273547739788782033)
              ·
                refine ⟨170225455160804841586525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226967273547739788782033 170225455160804841586525)
                ·
                  refine ⟨63834545685301815594947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170225455160804841586525 63834545685301815594947)
                  ·
                    rfl

theorem cell20_139857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_139857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139857 prefixEnd_139857 := by exact prefixLift 139857
  have htrace : WordTrace (prefixWord ++ tailWord_139857) baseStart_139857 baseEnd_139857 := by
    simpa [prefixWord, tailWord_139857, baseEnd_139857] using wordTrace_append hprefix tailTrace_139857
  have hstable : (prefixWord ++ tailWord_139857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139857).length < 2 ^ (prefixWord ++ tailWord_139857).sum := by decide
  have hdescent : baseEnd_139857 < baseStart_139857 := by decide
  rcases family_descends (prefixWord ++ tailWord_139857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139864 : List Nat := [2, 1, 2, 2, 1, 2, 4, 4, 2]
def baseStart_139864 : Nat := 118140960795 + 139864 * 2 ^ 59
def prefixEnd_139864 : Nat := 4983230072969 + 3 ^ 40 * 139864 * 2
def baseEnd_139864 : Nat := 63837740676040902361585

theorem tailTrace_139864 : CollatzResearch.WordTrace tailWord_139864 prefixEnd_139864 63837740676040902361585 := by
  unfold tailWord_139864
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550629582652044857289323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3400839443536059809719097 2550629582652044857289323)
  ·
    refine ⟨3825944373978067285933985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2550629582652044857289323 3825944373978067285933985)
    ·
      refine ⟨2869458280483550464450489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3825944373978067285933985 2869458280483550464450489)
      ·
        refine ⟨2152093710362662848337867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2869458280483550464450489 2152093710362662848337867)
        ·
          refine ⟨3228140565543994272506801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152093710362662848337867 3228140565543994272506801)
          ·
            refine ⟨2421105424157995704380101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3228140565543994272506801 2421105424157995704380101)
            ·
              refine ⟨453957267029624194571269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2421105424157995704380101 453957267029624194571269)
              ·
                refine ⟨85116987568054536482113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453957267029624194571269 85116987568054536482113)
                ·
                  refine ⟨63837740676040902361585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85116987568054536482113 63837740676040902361585)
                  ·
                    rfl

theorem cell20_139864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_139864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139864 prefixEnd_139864 := by exact prefixLift 139864
  have htrace : WordTrace (prefixWord ++ tailWord_139864) baseStart_139864 baseEnd_139864 := by
    simpa [prefixWord, tailWord_139864, baseEnd_139864] using wordTrace_append hprefix tailTrace_139864
  have hstable : (prefixWord ++ tailWord_139864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139864).length < 2 ^ (prefixWord ++ tailWord_139864).sum := by decide
  have hdescent : baseEnd_139864 < baseStart_139864 := by decide
  rcases family_descends (prefixWord ++ tailWord_139864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139888 : List Nat := [2, 1, 1, 1, 7, 2, 2, 4]
def baseStart_139888 : Nat := 118140960795 + 139888 * 2 ^ 59
def prefixEnd_139888 : Nat := 4983230072969 + 3 ^ 40 * 139888 * 2
def baseEnd_139888 : Nat := 21282898310001161853829

theorem tailTrace_139888 : CollatzResearch.WordTrace tailWord_139888 prefixEnd_139888 21282898310001161853829 := by
  unfold tailWord_139888
  simp only [CollatzResearch.WordTrace]
  refine ⟨2551067258608570906726159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3401423011478094542301545 2551067258608570906726159)
  ·
    refine ⟨3826600887912856360089239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2551067258608570906726159 3826600887912856360089239)
    ·
      refine ⟨5739901331869284540133859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3826600887912856360089239 5739901331869284540133859)
      ·
        refine ⟨8609851997803926810200789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5739901331869284540133859 8609851997803926810200789)
        ·
          refine ⟨201793406198529534614081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8609851997803926810200789 201793406198529534614081)
          ·
            refine ⟨151345054648897150960561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201793406198529534614081 151345054648897150960561)
            ·
              refine ⟨113508790986672863220421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151345054648897150960561 113508790986672863220421)
              ·
                refine ⟨21282898310001161853829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113508790986672863220421 21282898310001161853829)
                ·
                  rfl

theorem cell20_139888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_139888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139888 prefixEnd_139888 := by exact prefixLift 139888
  have htrace : WordTrace (prefixWord ++ tailWord_139888) baseStart_139888 baseEnd_139888 := by
    simpa [prefixWord, tailWord_139888, baseEnd_139888] using wordTrace_append hprefix tailTrace_139888
  have hstable : (prefixWord ++ tailWord_139888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139888).length < 2 ^ (prefixWord ++ tailWord_139888).sum := by decide
  have hdescent : baseEnd_139888 < baseStart_139888 := by decide
  rcases family_descends (prefixWord ++ tailWord_139888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139933 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 3]
def baseStart_139933 : Nat := 118140960795 + 139933 * 2 ^ 59
def prefixEnd_139933 : Nat := 4983230072969 + 3 ^ 40 * 139933 * 2
def baseEnd_139933 : Nat := 63869234156183329061303

theorem tailTrace_139933 : CollatzResearch.WordTrace tailWord_139933 prefixEnd_139933 63869234156183329061303 := by
  unfold tailWord_139933
  simp only [CollatzResearch.WordTrace]
  refine ⟨5103775802054114498840453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3402517201369409665893635 5103775802054114498840453)
  ·
    refine ⟨956957962885146468532585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5103775802054114498840453 956957962885146468532585)
    ·
      refine ⟨717718472163859851399439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 956957962885146468532585 717718472163859851399439)
      ·
        refine ⟨1076577708245789777099159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717718472163859851399439 1076577708245789777099159)
        ·
          refine ⟨1614866562368684665648739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1076577708245789777099159 1614866562368684665648739)
          ·
            refine ⟨2422299843553026998473109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614866562368684665648739 2422299843553026998473109)
            ·
              refine ⟨113545305166548140553427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2422299843553026998473109 113545305166548140553427)
              ·
                refine ⟨170317957749822210830141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113545305166548140553427 170317957749822210830141)
                ·
                  refine ⟨63869234156183329061303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170317957749822210830141 63869234156183329061303)
                  ·
                    rfl

theorem cell20_139933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_139933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_139933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_139933 prefixEnd_139933 := by exact prefixLift 139933
  have htrace : WordTrace (prefixWord ++ tailWord_139933) baseStart_139933 baseEnd_139933 := by
    simpa [prefixWord, tailWord_139933, baseEnd_139933] using wordTrace_append hprefix tailTrace_139933
  have hstable : (prefixWord ++ tailWord_139933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139933).length < 2 ^ (prefixWord ++ tailWord_139933).sum := by decide
  have hdescent : baseEnd_139933 < baseStart_139933 := by decide
  rcases family_descends (prefixWord ++ tailWord_139933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
